#!/usr/bin/env python3
"""
QRK-D Performance Baseline
==========================

This script mirrors the dimension-generic witness extraction performed by
`tests/QRKDDemo.lean`.  Unlike the earlier "parameter-only" helpers, it now:

* Builds the exact same finite-support test sequences used in Lean.
* Applies the constructive rounding algorithm `roundToGridD` on every
  non-zero Fourier mode (floor-based rounding on a δ-grid).
* Checks coefficient-box membership with the same conservative mesh.
* Tracks both the theoretical error budgets (inside + tail) and the actual
  ℓ² rounding error, all in exact rational arithmetic.

The goal is to provide an apples-to-apples Python reference when benchmarking
against the extracted Lean binary.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Dict, Iterable, Tuple
import time
import argparse

# ---------------------------------------------------------------------------
# Rational / complex helpers
# ---------------------------------------------------------------------------

ComplexFrac = Tuple[Fraction, Fraction]
ZERO_COMPLEX: ComplexFrac = (Fraction(0), Fraction(0))
PI_RAT_LB = Fraction(3, 1)  # Conservative π lower bound used in Lean proofs


def ceil_fraction_nonneg(q: Fraction) -> int:
    """Ceiling of a non-negative rational number."""
    if q <= 0:
        return 0
    n, d = q.numerator, q.denominator
    return (n + d - 1) // d


def floor_fraction(q: Fraction) -> int:
    """Exact floor for rationals (mirrors Lean's `⌊x⌋`)."""
    n, d = q.numerator, q.denominator
    # Python's // already implements floor for integers.
    return n // d


def complex_sub(a: ComplexFrac, b: ComplexFrac) -> ComplexFrac:
    return (a[0] - b[0], a[1] - b[1])


def complex_sq_abs(z: ComplexFrac) -> Fraction:
    return z[0] * z[0] + z[1] * z[1]


# ---------------------------------------------------------------------------
# Fourier sequence model (matches Lean test sequences)
# ---------------------------------------------------------------------------


class FourierSeqD:
    def __init__(self, d: int, coeffs: Dict[Tuple[int, ...], ComplexFrac]):
        self.d = d
        self.coeffs = coeffs

    def a(self, k: Tuple[int, ...]) -> ComplexFrac:
        return self.coeffs.get(k, ZERO_COMPLEX)

    def support(self) -> Iterable[Tuple[int, ...]]:
        return self.coeffs.keys()

    def is_mean_zero(self) -> bool:
        return self.a(tuple(0 for _ in range(self.d))) == ZERO_COMPLEX


def axis_vector(d: int, axis: int, value: int = 1) -> Tuple[int, ...]:
    return tuple(value if i == axis else 0 for i in range(d))


def build_test_sequence(d: int) -> FourierSeqD:
    """Copy of the Lean demo sequences (see tests/QRKDDemo.lean)."""
    coeffs: Dict[Tuple[int, ...], ComplexFrac] = {}
    if d == 1:
        coeffs[(1,)] = (Fraction(1), Fraction(0))
        coeffs[(-1,)] = (Fraction(1), Fraction(0))
    else:
        for axis in range(d):
            coeffs[axis_vector(d, axis, 1)] = (Fraction(1), Fraction(0))
    return FourierSeqD(d, coeffs)


# ---------------------------------------------------------------------------
# Witness parameter formulas (identical to Lean)
# ---------------------------------------------------------------------------


def m_of(eps: Fraction, R: Fraction) -> int:
    quotient = R / (PI_RAT_LB * eps)
    return ceil_fraction_nonneg(quotient) + 1


def mesh_d(d: int, eps: Fraction, M: int) -> Fraction:
    exp = (d + 1) // 2  # ceil(d/2)
    return eps / (4 * (2 * M + 1) ** exp)


def index_set_cardinality(d: int, M: int) -> int:
    return (2 * M + 1) ** d - 1


def coeff_box_radius(bound: Fraction, delta: Fraction) -> int:
    ratio = bound / delta if delta != 0 else Fraction(0)
    return ceil_fraction_nonneg(ratio) + 1


def coeff_bound(R: Fraction, k: Tuple[int, ...]) -> Fraction:
    return Fraction(0) if all(coord == 0 for coord in k) else R


# ---------------------------------------------------------------------------
# Witness extraction (rounding only the actual support)
# ---------------------------------------------------------------------------


def round_support(seq: FourierSeqD, delta: Fraction, R: Fraction) -> Dict[Tuple[int, ...], Tuple[int, int]]:
    rounded: Dict[Tuple[int, ...], Tuple[int, int]] = {}
    for k in seq.support():
        coeff = seq.a(k)
        re_scaled = coeff[0] / delta
        im_scaled = coeff[1] / delta
        re_int = floor_fraction(re_scaled)
        im_int = floor_fraction(im_scaled)
        radius = coeff_box_radius(coeff_bound(R, k), delta)
        assert abs(re_int) <= radius, f"Real part exceeded box for k={k}"
        assert abs(im_int) <= radius, f"Imag part exceeded box for k={k}"
        rounded[k] = (re_int, im_int)
    return rounded


def reconstruct_coeff(entry: Tuple[int, int], delta: Fraction) -> ComplexFrac:
    return (Fraction(entry[0]) * delta, Fraction(entry[1]) * delta)


def rounding_error(seq: FourierSeqD, rounded: Dict[Tuple[int, ...], Tuple[int, int]], delta: Fraction) -> Fraction:
    err = Fraction(0)
    for k, coeff in seq.coeffs.items():
        approx = reconstruct_coeff(rounded[k], delta)
        diff = complex_sub(coeff, approx)
        err += complex_sq_abs(diff)
    return err


def tail_energy(seq: FourierSeqD, M: int) -> Fraction:
    total = Fraction(0)
    for k, coeff in seq.coeffs.items():
        if any(abs(coord) > M for coord in k):
            total += complex_sq_abs(coeff)
    return total


def tail_error_budget(R: Fraction, M: int) -> Fraction:
    if M == 0:
        return Fraction(0)
    return (R * R) / (4 * (PI_RAT_LB ** 2) * (M ** 2))


def inside_error_budget(d: int, M: int, delta: Fraction) -> Fraction:
    count = index_set_cardinality(d, M)
    return Fraction(2 * count, 1) * (delta * delta)


# ---------------------------------------------------------------------------
# Reporting / formatting
# ---------------------------------------------------------------------------


def format_fraction(q: Fraction, precision: int = 6) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    return f"{float(q):.{precision}g} ({q.numerator}/{q.denominator})"


def format_sq_err(q: Fraction) -> str:
    return f"{float(q):.6e} (exact = {q.numerator}/{q.denominator})"


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def run_case(name: str, d: int, eps: Fraction, R: Fraction) -> None:
    seq = build_test_sequence(d)
    assert seq.is_mean_zero(), "Lean demo sequences are mean-zero by construction"

    M = m_of(eps, R)
    delta = mesh_d(d, eps, M)

    start = time.perf_counter()
    rounded = round_support(seq, delta, R)
    elapsed = time.perf_counter() - start

    round_err = rounding_error(seq, rounded, delta)
    tail_err = tail_energy(seq, M)
    inside_budget = inside_error_budget(d, M, delta)
    tail_budget = tail_error_budget(R, M)
    total_budget = inside_budget + tail_budget
    eps_sq = eps * eps

    theoretical_index = index_set_cardinality(d, M)

    print(f"╔{'═'*70}╗")
    print(f"║ {name:<66} ║")
    print(f"╚{'═'*70}╝")
    print(f"Dimension d            : {d}")
    print(f"ε (target L² error)    : {eps}  → ε² = {format_sq_err(eps_sq)}")
    print(f"H¹ radius R            : {R}")
    print(f"M (cutoff)             : {M}")
    print(f"δ (mesh)               : {format_fraction(delta)}")
    print(f"Index set size         : (2M+1)^{d} - 1 = {theoretical_index:,}")
    print(f"Active support size    : {len(list(seq.support())):,} (rounded explicitly)")
    print()
    print("Witness extraction (Python)")
    print("──────────────────────────")
    print(f"Rounded coefficients    : {len(rounded)}")
    print(f"Extraction time         : {elapsed * 1000:.3f} ms")
    print()
    print("Error accounting")
    print("────────────────")
    print(f"Actual rounding error   : {format_sq_err(round_err)}")
    print(f"Actual tail energy      : {format_sq_err(tail_err)}")
    print(f"Theoretical inside ≤    : {format_sq_err(inside_budget)}")
    print(f"Theoretical tail ≤      : {format_sq_err(tail_budget)}")
    print(f"Total error budget ≤    : {format_sq_err(total_budget)}")
    print()

    actual_total = round_err + tail_err
    print(f"Actual total error      : {format_sq_err(actual_total)}")
    print(f"Budget covers ε²?       : {'YES' if total_budget <= eps_sq else 'NO'}")
    print(f"Actual error ≤ ε²?      : {'YES' if actual_total <= eps_sq else 'NO'}")
    print()


def parse_cli() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="QRK-D Python baseline (constructive witness extraction).",
        formatter_class=argparse.RawTextHelpFormatter,
    )
    parser.add_argument("--dim", type=int, help="dimension d (natural number ≥ 1)")
    parser.add_argument("--eps", type=str, help="target accuracy ε (rational, e.g. 1/20)")
    parser.add_argument("--radius", type=str, help="H¹ radius R (rational)")
    return parser.parse_args()


def parse_fraction(text: str) -> Fraction:
    text = text.strip()
    if "/" in text:
        num_str, den_str = text.split("/", maxsplit=1)
        return Fraction(int(num_str), int(den_str))
    return Fraction(int(text))


def main() -> None:
    args = parse_cli()

    default_cases = [
        ("1D witness (ε = 1/10, R = 10)", 1, Fraction(1, 10), Fraction(10, 1)),
        ("2D witness (ε = 1/10, R = 10)", 2, Fraction(1, 10), Fraction(10, 1)),
        ("3D witness (ε = 1/10, R = 13)", 3, Fraction(1, 10), Fraction(13, 1)),
        ("4D witness (ε = 1/10, R = 14)", 4, Fraction(1, 10), Fraction(14, 1)),
        ("5D witness (ε = 1/10, R = 16)", 5, Fraction(1, 10), Fraction(16, 1)),
    ]

    print("╔══════════════════════════════════════════════════════════════════════╗")
    print("║  QRK-D Python Baseline — Constructive Witness Extraction            ║")
    print("║  Mirrors tests/QRKDDemo.lean (d ∈ {1,…,5})                          ║")
    print("╚══════════════════════════════════════════════════════════════════════╝")
    print()

    if args.dim is None and args.eps is None and args.radius is None:
        cases = default_cases
    elif args.dim is not None and args.eps is not None and args.radius is not None:
        d = args.dim
        if d < 1:
            raise SystemExit("qrkd_baseline: --dim must be ≥ 1")
        eps = parse_fraction(args.eps)
        radius = parse_fraction(args.radius)
        cases = [(f"Custom witness (d={d}, ε={eps}, R={radius})", d, eps, radius)]
    else:
        raise SystemExit("qrkd_baseline: please supply --dim, --eps, and --radius together (or none).")

    for name, d, eps, R in cases:
        run_case(name, d, eps, R)

    print("All cases completed successfully.")


if __name__ == "__main__":
    main()
