#!/usr/bin/env python3
"""Witness-budget baseline runner."""

import argparse
import json
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path

try:
    from tabulate import tabulate
except ImportError:  # pragma: no cover
    tabulate = None  # type: ignore

SCRIPT_ROOT = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_ROOT.parent


def derive_prefix(module: str) -> str:
    if module.startswith("Budgets."):
        parts = module.split(".")
        if len(parts) >= 2:
            return parts[1]
    if "." in module:
        return module.split(".")[-1]
    return module


def safe_module_name(module: str) -> str:
    return module.replace(".", "-").lower()


def run_baseline(module: str, prefix: str, output: Path, log_dir: Path) -> dict:
    tmp = REPO_ROOT / "tests" / f"BaselineTemp_{int(time.time() * 1000)}.lean"
    try:
        tmp.write_text(
            f"-- Auto-generated baseline analysis\n"
            f"-- Import: {module}\n"
            f"-- Analyze prefix: {prefix}\n"
            f"-- Filter by module: {module}\n"
            f"import {module}\nimport WBudget.Baseline\n\n"
            f"#baseline_module {prefix} {module}\n",
            encoding="utf-8",
        )
    except Exception as exc:
        raise RuntimeError(f"Failed to write temp Lean file: {exc}")

    log_dir.mkdir(parents=True, exist_ok=True)
    log_file = log_dir / f"baseline_{safe_module_name(module)}.log"
    log_file.parent.mkdir(exist_ok=True)
    with log_file.open("w", encoding="utf-8") as log:
        proc = subprocess.Popen(
            ["lake", "env", "lean", str(tmp)],
            cwd=REPO_ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        json_lines = []
        assert proc.stdout is not None
        for line in proc.stdout:
            log.write(line)
            # Filter JSON lines, excluding error messages that contaminate output
            if (line.startswith(("[", "{", "]", ",")) or line.startswith("  ")) and "Error analyzing" not in line:
                json_lines.append(line)
            elif line.strip() in ["}", ","]:
                # Standalone closing brace or comma is valid JSON
                json_lines.append(line)
        proc.wait()
    tmp.unlink(missing_ok=True)
    if proc.returncode != 0:
        raise RuntimeError(f"baseline command failed for {module}; see {log_file}")
    output.write_text("".join(json_lines), encoding="utf-8")
    data = json.loads(output.read_text(encoding="utf-8"))
    if not data:
        raise RuntimeError(
            f"No declarations matched prefix '{prefix}' in module '{module}'"
        )
    return data


def summarize(data: list[dict]) -> tuple[dict[str, int], dict[str, int]]:
    def tally(key: str) -> dict[str, int]:
        counts: dict[str, int] = {}
        for entry in data:
            val = entry.get(key, "C0")
            counts[val] = counts.get(val, 0) + 1
        return counts

    return tally("vbudget"), tally("xbudget")


def analyze_prop_erasure(data: list[dict]) -> dict:
    """Analyze prop-erasure benefit from enhanced baseline data."""
    if not data:
        return {}

    total = len(data)

    # Find declarations with vbudget ≠ xbudget (prop-erasure benefit)
    prop_erasure_benefit = [d for d in data if d['vbudget'] != d['xbudget']]

    # Count axiom positions
    type_flow_axioms = {}
    prop_only_axioms = {}

    for entry in data:
        # Type-flow triggers (affect extraction)
        for trigger in entry.get('type_flow_triggers', []):
            const = trigger.get('const', trigger) if isinstance(trigger, dict) else trigger
            type_flow_axioms[const] = type_flow_axioms.get(const, 0) + 1

        # Prop-only triggers (verification only)
        for trigger in entry.get('prop_only_triggers', []):
            const = trigger.get('const', trigger) if isinstance(trigger, dict) else trigger
            prop_only_axioms[const] = prop_only_axioms.get(const, 0) + 1

    return {
        'total': total,
        'prop_erasure_count': len(prop_erasure_benefit),
        'prop_erasure_pct': 100 * len(prop_erasure_benefit) / total if total > 0 else 0,
        'type_flow_axioms': type_flow_axioms,
        'prop_only_axioms': prop_only_axioms,
        'sample_benefits': prop_erasure_benefit[:3]  # Top 3 examples
    }


LEVELS = ["C0", "C1", "C2", "C3", "C4", "C5"]


def format_counts(counts: dict[str, int]) -> str:
    visible = [lvl for lvl in LEVELS if counts.get(lvl, 0) > 0]
    if not visible:
        visible = ["C0"]
    parts = [f"{level}:{counts.get(level, 0)}" for level in visible]
    return " ".join(parts)


def print_prop_erasure_summary(analysis: dict, module: str):
    """Print prop-erasure analysis summary."""
    if not analysis:
        return

    pct = analysis.get('prop_erasure_pct', 0)
    count = analysis.get('prop_erasure_count', 0)
    total = analysis.get('total', 0)

    if pct > 0:
        print(f"\n  🎯 Prop-Erasure: {count}/{total} decls ({pct:.1f}%) have vbudget>xbudget")
        print(f"     (classical proofs with constructive extraction)")

        # Show top axioms if available
        type_flow = analysis.get('type_flow_axioms', {})
        prop_only = analysis.get('prop_only_axioms', {})

        if type_flow:
            top_blockers = sorted(type_flow.items(), key=lambda x: x[1], reverse=True)[:3]
            print(f"\n  ⚠️  Top extraction blockers:")
            for axiom, count in top_blockers:
                print(f"     - {axiom}: {count} occurrences")

        if prop_only:
            top_erased = sorted(prop_only.items(), key=lambda x: x[1], reverse=True)[:3]
            print(f"\n  ✓  Top erased axioms (verification only):")
            for axiom, count in top_erased:
                print(f"     - {axiom}: {count} occurrences")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Run witness-budget baseline on one or more Lean modules",
    )
    parser.add_argument("module", nargs="?", help="Primary module to import")
    parser.add_argument(
        "legacy_prefix", nargs="?", help="[legacy] explicit prefix override"
    )
    parser.add_argument(
        "legacy_output", nargs="?", help="[legacy] explicit output path"
    )
    parser.add_argument(
        "-p", "--prefix", help="Declaration prefix override for the primary module"
    )
    parser.add_argument(
        "-o", "--output", help="Output JSON path for the primary module"
    )
    parser.add_argument(
        "--module",
        dest="extra_modules",
        action="append",
        help="Additional module to analyze (repeatable)",
    )
    parser.add_argument(
        "-j",
        "--jobs",
        type=int,
        default=1,
        help="Number of modules to analyze concurrently",
    )
    parser.add_argument(
        "--continue-on-error",
        action="store_true",
        help="Do not stop on first failure (exit code still non-zero if any fail)",
    )
    args = parser.parse_intermixed_args(argv)

    modules: list[tuple[str, str | None, str | None]] = []

    if args.module:
        modules.append(
            (
                args.module,
                args.prefix or args.legacy_prefix,
                args.output or args.legacy_output,
            )
        )

    if args.extra_modules:
        for extra in args.extra_modules:
            modules.append((extra, None, None))

    if not modules:
        parser.error(
            "Please provide at least one module via positional argument or --module"
        )

    log_dir = REPO_ROOT / "tmp"
    total = len(modules)

    jobs_data = []
    for idx, (module, prefix_override, output_override) in enumerate(modules, start=1):
        prefix = prefix_override or derive_prefix(module)
        output_path = output_override
        if output_path is None:
            stamp = datetime.now().strftime("%Y%m%d")
            output_path = f"budgets/baseline-{safe_module_name(module)}-{stamp}.json"
        output = REPO_ROOT / output_path
        output.parent.mkdir(parents=True, exist_ok=True)
        jobs_data.append(
            {
                "module": module,
                "prefix": prefix,
                "output": output,
                "idx": idx,
                "total": total,
            }
        )

    results: list[tuple[str, int, dict[str, int], dict[str, int], float, Path, dict]] = []
    failures: list[str] = []

    def run_job(
        job: dict,
    ) -> tuple[str, int, dict[str, int], dict[str, int], float, Path, dict]:
        module = job["module"]
        prefix = job["prefix"]
        output = job["output"]
        print(f"[{job['idx']}/{job['total']}] {module}")
        print(f"    prefix: {prefix}")
        print(f"    output: {output}")
        start = time.time()
        data = run_baseline(module, prefix, output, log_dir)
        elapsed = time.time() - start
        decls = len(data)
        vb, xb = summarize(data)
        prop_erasure = analyze_prop_erasure(data)
        print(f"    ✓ {decls} decls in {elapsed:.1f}s")
        print_prop_erasure_summary(prop_erasure, module)
        return module, decls, vb, xb, elapsed, output, prop_erasure

    if args.jobs <= 1:
        for job in jobs_data:
            try:
                results.append(run_job(job))
            except Exception as exc:
                failures.append(f"{job['module']}: {exc}")
                print(f"    ✗ {exc}", file=sys.stderr)
                if not args.continue_on_error:
                    return 1
    else:
        from concurrent.futures import ThreadPoolExecutor, as_completed

        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            future_map = {executor.submit(run_job, job): job for job in jobs_data}
            for future in as_completed(future_map):
                job = future_map[future]
                try:
                    results.append(future.result())
                except Exception as exc:
                    failures.append(f"{job['module']}: {exc}")
                    print(f"    ✗ {exc}", file=sys.stderr)
                    if not args.continue_on_error:
                        executor.shutdown(cancel_futures=True)
                        return 1

    # Simple summary table for now (single module still gets displayed)
    print()
    rows = []
    for module, decls, vb, xb, elapsed, output, prop_erasure in results:
        pe_count = prop_erasure.get('prop_erasure_count', 0)
        pe_pct = prop_erasure.get('prop_erasure_pct', 0)
        pe_str = f"{pe_count} ({pe_pct:.0f}%)" if pe_count > 0 else "-"
        rows.append(
            [
                module,
                decls,
                format_counts(vb),
                format_counts(xb),
                pe_str,
                f"{elapsed:.1f}s",
            ]
        )

    headers = ["Module", "Decls", "vbudget (C0-C5)", "xbudget (C0-C5)", "Prop-Erasure", "Time"]

    if tabulate is not None:
        print(tabulate(rows, headers=headers, tablefmt="github"))
    else:
        module_width = max(len(r[0]) for r in rows) if rows else len(headers[0])
        module_width = max(module_width, len(headers[0]))
        decls_width = max(len(str(r[1])) for r in rows) if rows else len(headers[1])
        decls_width = max(decls_width, len(headers[1]))
        vb_width = max(len(r[2]) for r in rows) if rows else len(headers[2])
        vb_width = max(vb_width, len(headers[2]))
        xb_width = max(len(r[3]) for r in rows) if rows else len(headers[3])
        xb_width = max(xb_width, len(headers[3]))
        pe_width = max(len(r[4]) for r in rows) if rows else len(headers[4])
        pe_width = max(pe_width, len(headers[4]))
        time_width = max(len(r[5]) for r in rows) if rows else len(headers[5])
        time_width = max(time_width, len(headers[5]))

        def line(char: str = "-") -> str:
            return f"+-{char * module_width}-+-{char * decls_width}-+-{char * vb_width}-+-{char * xb_width}-+-{char * pe_width}-+-{char * time_width}-+"

        print(line("-"))
        header_row = (
            f"| {'Module':<{module_width}} | {'Decls':>{decls_width}} | "
            f"{'vbudget (C0-C5)':<{vb_width}} | {'xbudget (C0-C5)':<{xb_width}} | "
            f"{'Prop-Erasure':<{pe_width}} | {'Time':<{time_width}} |"
        )
        print(header_row)
        print(line("="))
        for module, decls, vb_str, xb_str, pe_str, elapsed_str in rows:
            row = (
                f"| {module:<{module_width}} | {decls:>{decls_width}} | "
                f"{vb_str:<{vb_width}} | {xb_str:<{xb_width}} | {pe_str:<{pe_width}} | {elapsed_str:<{time_width}} |"
            )
            print(row)
        print(line("-"))

    if failures:
        print()
        print("Failures:")
        for err in failures:
            print(f"  - {err}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
