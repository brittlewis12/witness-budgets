#!/usr/bin/env python3
"""
QA-L Python Baseline
====================

This script mirrors the constructive Quantitative Aubin–Lions demo implemented in
`tests/QALDemo.lean`.  Similar to the QRK-D baselines, it:

* Constructs the exact Fourier test curves used in Lean (constant, linear, 2D constant).
* Builds the same uniform time grids and spatial rounding parameters (`M`, δ).
* Applies the factored rounding procedure at each time node to obtain grid witnesses.
* Integrates the coefficient-wise L² error of the resulting piecewise-constant
  witness across all slabs, yielding an empirical QA-L error that can be compared to ε².

All arithmetic is exact (Python `Fraction`) so that the reported numbers match the
formal budgets.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, Iterable, List, Tuple
import argparse
import time

ComplexFrac = Tuple[Fraction, Fraction]
Mode = Tuple[int, ...]
ZERO_COMPLEX: ComplexFrac = (Fraction(0), Fraction(0))
PI_RAT_LB = Fraction(3, 1)


def ceil_fraction_nonneg(q: Fraction) -> int:
    if q <= 0:
        return 0
    n, d = q.numerator, q.denominator
    return (n + d - 1) // d


def floor_fraction(q: Fraction) -> int:
    n, d = q.numerator, q.denominator
    return n // d


def complex_sub(a: ComplexFrac, b: ComplexFrac) -> ComplexFrac:
    return (a[0] - b[0], a[1] - b[1])


def complex_add(a: ComplexFrac, b: ComplexFrac) -> ComplexFrac:
    return (a[0] + b[0], a[1] + b[1])


def complex_scalar_mul(s: Fraction, z: ComplexFrac) -> ComplexFrac:
    return (s * z[0], s * z[1])


def complex_sq_abs(z: ComplexFrac) -> Fraction:
    return z[0] * z[0] + z[1] * z[1]


def is_zero_mode(k: Mode) -> bool:
    return all(coord == 0 for coord in k)


def coeff_bound(R: Fraction, k: Mode) -> Fraction:
    return Fraction(0) if is_zero_mode(k) else R


def coeff_box_radius(bound: Fraction, delta: Fraction) -> int:
    if delta == 0:
        raise ZeroDivisionError("delta must be positive")
    return ceil_fraction_nonneg(bound / delta) + 1


def m_of(eps: Fraction, R: Fraction) -> int:
    return ceil_fraction_nonneg(R / (PI_RAT_LB * eps)) + 1


def mesh_d(d: int, eps: Fraction, M: int) -> Fraction:
    exp = (d + 1) // 2  # ceil(d/2)
    return eps / (4 * Fraction((2 * M + 1) ** exp))


def integrate_sq_error(alpha: ComplexFrac, beta: ComplexFrac,
                        a: Fraction, b: Fraction) -> Fraction:
    ar, ai = alpha
    br, bi = beta
    A = ar * ar + ai * ai
    B = 2 * (ar * br + ai * bi)
    C = br * br + bi * bi
    interval_t2 = Fraction(b * b - a * a)
    interval_t3 = Fraction(b * b * b - a * a * a)
    return (A * interval_t3 / 3) + (B * interval_t2 / 2) + C * (b - a)


def format_fraction(q: Fraction, precision: int = 6) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    return f"{float(q):.{precision}g} ({q.numerator}/{q.denominator})"


def format_sq_err(q: Fraction) -> str:
    return f"{float(q):.6e} (exact = {q.numerator}/{q.denominator})"


@dataclass
class QALCase:
    name: str
    dimension: int
    epsilon: Fraction
    radius: Fraction
    deriv_bound: Fraction
    horizon: Fraction
    segments: int
    curve_kind: str
    start_raw: Dict[Mode, ComplexFrac]
    end_raw: Dict[Mode, ComplexFrac]

    def __post_init__(self) -> None:
        support_set = set(self.start_raw) | set(self.end_raw)
        self.support: List[Mode] = sorted(support_set)
        self.start: Dict[Mode, ComplexFrac] = {
            k: self.start_raw.get(k, ZERO_COMPLEX) for k in self.support
        }
        self.end: Dict[Mode, ComplexFrac] = {
            k: self.end_raw.get(k, ZERO_COMPLEX) for k in self.support
        }
        self.slopes: Dict[Mode, ComplexFrac] = {
            k: complex_sub(self.end[k], self.start[k]) for k in self.support
        }
        self.mesh: Fraction = self.horizon / self.segments

    def coeffs_at(self, t: Fraction) -> Dict[Mode, ComplexFrac]:
        return {
            k: complex_add(self.start[k], complex_scalar_mul(t, self.slopes[k]))
            for k in self.support
        }


def round_coeffs(coeffs: Dict[Mode, ComplexFrac], delta: Fraction,
                 R: Fraction) -> Dict[Mode, Tuple[int, int]]:
    rounded: Dict[Mode, Tuple[int, int]] = {}
    for k, coeff in coeffs.items():
        re_int = floor_fraction(coeff[0] / delta)
        im_int = floor_fraction(coeff[1] / delta)
        radius = coeff_box_radius(coeff_bound(R, k), delta)
        if abs(re_int) > radius or abs(im_int) > radius:
            raise ValueError(
                f"Coefficient for mode {k} exceeded box bounds (int=({re_int},{im_int}), radius={radius})"
            )
        rounded[k] = (re_int, im_int)
    return rounded


def reconstruct_coeff(entry: Tuple[int, int], delta: Fraction) -> ComplexFrac:
    return (Fraction(entry[0]) * delta, Fraction(entry[1]) * delta)


def rounding_error(coeffs: Dict[Mode, ComplexFrac], approx: Dict[Mode, ComplexFrac]) -> Fraction:
    err = Fraction(0)
    for k in coeffs:
        diff = complex_sub(coeffs[k], approx[k])
        err += complex_sq_abs(diff)
    return err


def build_cases() -> Dict[str, QALCase]:
    frac = Fraction
    case1 = QALCase(
        name="Constant Curve 1D",
        dimension=1,
        epsilon=frac(1, 10),
        radius=frac(12, 1),
        deriv_bound=frac(1, 10),
        horizon=frac(1, 1),
        segments=4,
        curve_kind="constant",
        start_raw={
            (1,): (frac(1), frac(0)),
            (-1,): (frac(1), frac(0)),
        },
        end_raw={
            (1,): (frac(1), frac(0)),
            (-1,): (frac(1), frac(0)),
        },
    )

    case2 = QALCase(
        name="Linear Interpolation 1D",
        dimension=1,
        epsilon=frac(1, 10),
        radius=frac(18, 1),
        deriv_bound=frac(5, 1),
        horizon=frac(1, 1),
        segments=12,
        curve_kind="linear",
        start_raw={
            (1,): (frac(1), frac(0)),
            (-1,): (frac(1), frac(0)),
            (2,): (frac(0), frac(0)),
            (-2,): (frac(0), frac(0)),
        },
        end_raw={
            (1,): (frac(0), frac(0)),
            (-1,): (frac(0), frac(0)),
            (2,): (frac(1), frac(0)),
            (-2,): (frac(1), frac(0)),
        },
    )

    case3 = QALCase(
        name="Constant Curve 2D",
        dimension=2,
        epsilon=frac(1, 10),
        radius=frac(12, 1),
        deriv_bound=frac(1, 10),
        horizon=frac(1, 1),
        segments=4,
        curve_kind="constant",
        start_raw={
            (1, 0): (frac(1), frac(0)),
            (0, 1): (frac(1), frac(0)),
        },
        end_raw={
            (1, 0): (frac(1), frac(0)),
            (0, 1): (frac(1), frac(0)),
        },
    )

    return {
        "constant1d": case1,
        "linear1d": case2,
        "constant2d": case3,
    }


def integrate_case(case: QALCase, approx_nodes: List[Dict[Mode, ComplexFrac]]) -> Fraction:
    total = Fraction(0)
    for i in range(case.segments):
        a = case.mesh * i
        b = a + case.mesh
        approx = approx_nodes[i]
        for k in case.support:
            alpha = case.slopes[k]
            beta = complex_sub(case.start[k], approx[k])
            total += integrate_sq_error(alpha, beta, a, b)
    return total


def run_case(case: QALCase) -> None:
    eps_sq = case.epsilon * case.epsilon
    M = m_of(case.epsilon, case.radius)
    delta = mesh_d(case.dimension, case.epsilon, M)

    approx_nodes: List[Dict[Mode, ComplexFrac]] = []
    rounding_errs: List[Fraction] = []
    rounding_start = time.perf_counter()
    for i in range(case.segments):
        t = case.mesh * i
        coeffs = case.coeffs_at(t)
        rounded = round_coeffs(coeffs, delta, case.radius)
        approx = {k: reconstruct_coeff(rounded[k], delta) for k in case.support}
        approx_nodes.append(approx)
        rounding_errs.append(rounding_error(coeffs, approx))
    rounding_elapsed = time.perf_counter() - rounding_start

    total_round_err = sum(rounding_errs, Fraction(0))
    max_round_err = max(rounding_errs) if rounding_errs else Fraction(0)

    integration_start = time.perf_counter()
    total_error = integrate_case(case, approx_nodes)
    integration_elapsed = time.perf_counter() - integration_start

    print(f"╔{'═'*70}╗")
    print(f"║ {case.name:<66} ║")
    print(f"╚{'═'*70}╝")
    print(f"Dimension d            : {case.dimension}")
    print(f"Curve type             : {case.curve_kind}")
    print(f"ε (target L² error)    : {case.epsilon}  → ε² = {format_sq_err(eps_sq)}")
    print(f"H¹ radius R            : {case.radius}")
    print(f"Time derivative bound S : {case.deriv_bound}")
    print(f"Horizon T              : {case.horizon}")
    print(f"Segments K             : {case.segments}  (mesh = {format_fraction(case.mesh)})")
    print(f"Frequency cutoff M     : {M}")
    print(f"δ (spatial mesh)       : {format_fraction(delta)}")
    print(f"Support size           : {len(case.support)} modes")
    print()
    print("Node rounding (per left endpoint)")
    print("──────────────────────────────")
    for idx, (t, err) in enumerate(zip((case.mesh * i for i in range(case.segments)), rounding_errs)):
        print(f"t_{idx} = {format_fraction(t)} → rounding error = {format_sq_err(err)}")
    print(f"Total rounding error on nodes  : {format_sq_err(total_round_err)}")
    print(f"Max rounding error per node    : {format_sq_err(max_round_err)}")
    print(f"Rounding time                  : {rounding_elapsed * 1000:.3f} ms")
    print()
    print("Temporal integration of |u - w|²")
    print("────────────────────────────────")
    print(f"Actual ∫‖u - w‖² dt       : {format_sq_err(total_error)}")
    print(f"Integration time             : {integration_elapsed * 1000:.3f} ms")
    print(f"Within ε² budget?           : {'YES' if total_error <= eps_sq else 'NO'}")
    print()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="QA-L Python baseline (constructive space-time witness)",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument(
        "--case",
        choices=["all", "constant1d", "linear1d", "constant2d"],
        default="all",
        help="Which test case(s) to run",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    cases = build_cases()

    print("╔══════════════════════════════════════════════════════════════════════╗")
    print("║  Quantitative Aubin–Lions Python Baseline — Witness Extraction      ║")
    print("║  Mirrors tests/QALDemo.lean (constant & linear demo curves)         ║")
    print("╚══════════════════════════════════════════════════════════════════════╝")
    print()

    selected: Iterable[str]
    if args.case == "all":
        selected = ["constant1d", "linear1d", "constant2d"]
    else:
        selected = [args.case]

    for key in selected:
        run_case(cases[key])

    print("All QA-L baseline cases completed.")


if __name__ == "__main__":
    main()
