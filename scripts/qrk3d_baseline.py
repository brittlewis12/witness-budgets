#!/usr/bin/env python3
"""
QRK-3D Performance Baseline — Constructive Witness Extraction

Faithfully mirrors the Lean demo in `tests/QRK3DDemo.lean`:
  * Uses the formal test sequences (product corner mode, diagonal mode, mixed mode)
  * Computes M and δ with the 3D mesh formula δ = ε/(8·(2M+1)²)
  * Rounds only the non-zero Fourier modes (factored witness) using exact rationals
  * Checks coefficient boxes and L² error budgets exactly before emitting results

Benchmark this script against the Lean binary `qrk3d_demo` for apples-to-apples
performance comparisons.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Dict, Iterable, Tuple
import time

ComplexFrac = Tuple[Fraction, Fraction]
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


def complex_sq_abs(z: ComplexFrac) -> Fraction:
    return z[0] * z[0] + z[1] * z[1]


class FourierSeq3D:
    def __init__(self, coeffs: Dict[Tuple[int, int, int], ComplexFrac]):
        self.coeffs = coeffs

    def a(self, k: Tuple[int, int, int]) -> ComplexFrac:
        return self.coeffs.get(k, ZERO_COMPLEX)

    def support(self) -> Iterable[Tuple[int, int, int]]:
        return self.coeffs.keys()

    def is_mean_zero(self) -> bool:
        return self.a((0, 0, 0)) == ZERO_COMPLEX


def m_of(eps: Fraction, R: Fraction) -> int:
    quotient = R / (PI_RAT_LB * eps)
    return ceil_fraction_nonneg(quotient) + 1


def mesh_3d(eps: Fraction, M: int) -> Fraction:
    return eps / (8 * (2 * M + 1) ** 2)


def index_set_cardinality(M: int) -> int:
    return (2 * M + 1) ** 3 - 1


def coeff_box_radius(bound: Fraction, delta: Fraction) -> int:
    if bound == 0:
        return 1
    ratio = bound / delta
    return ceil_fraction_nonneg(ratio) + 1


def coeff_bound(R: Fraction, k: Tuple[int, int, int]) -> Fraction:
    return Fraction(0) if (k[0] == 0 and k[1] == 0 and k[2] == 0) else R


def round_support(seq: FourierSeq3D, delta: Fraction, R: Fraction) -> Dict[Tuple[int, int, int], Tuple[int, int]]:
    rounded: Dict[Tuple[int, int, int], Tuple[int, int]] = {}
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


def reconstruct(entry: Tuple[int, int], delta: Fraction) -> ComplexFrac:
    return (Fraction(entry[0]) * delta, Fraction(entry[1]) * delta)


def rounding_error(seq: FourierSeq3D, rounded: Dict[Tuple[int, int, int], Tuple[int, int]], delta: Fraction) -> Fraction:
    err = Fraction(0)
    for k, coeff in seq.coeffs.items():
        approx = reconstruct(rounded[k], delta)
        diff = complex_sub(coeff, approx)
        err += complex_sq_abs(diff)
    return err


def tail_energy(seq: FourierSeq3D, M: int) -> Fraction:
    total = Fraction(0)
    for k, coeff in seq.coeffs.items():
        if any(abs(coord) > M for coord in k):
            total += complex_sq_abs(coeff)
    return total


def tail_error_budget(R: Fraction, M: int) -> Fraction:
    if M == 0:
        return Fraction(0)
    return (R * R) / (4 * (PI_RAT_LB ** 2) * (M ** 2))


def inside_error_budget(M: int, delta: Fraction) -> Fraction:
    count = index_set_cardinality(M)
    return Fraction(2 * count, 1) * (delta * delta)


def format_fraction(q: Fraction, precision: int = 6) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    return f"{float(q):.{precision}g} ({q.numerator}/{q.denominator})"


def format_sq_err(q: Fraction) -> str:
    return f"{float(q):.6e} (exact = {q.numerator}/{q.denominator})"


def seq_product_corners() -> FourierSeq3D:
    coeffs: Dict[Tuple[int, int, int], ComplexFrac] = {
        (1, 1, 1): (Fraction(-1, 8), Fraction(0)),
        (1, 1, -1): (Fraction(1, 8), Fraction(0)),
        (1, -1, 1): (Fraction(1, 8), Fraction(0)),
        (1, -1, -1): (Fraction(-1, 8), Fraction(0)),
        (-1, 1, 1): (Fraction(1, 8), Fraction(0)),
        (-1, 1, -1): (Fraction(-1, 8), Fraction(0)),
        (-1, -1, 1): (Fraction(-1, 8), Fraction(0)),
        (-1, -1, -1): (Fraction(1, 8), Fraction(0)),
    }
    return FourierSeq3D(coeffs)


def seq_diagonal() -> FourierSeq3D:
    return FourierSeq3D({
        (1, 1, 1): (Fraction(0), Fraction(1, 2)),
        (-1, -1, -1): (Fraction(0), Fraction(-1, 2)),
    })


def seq_mixed_mode() -> FourierSeq3D:
    return FourierSeq3D({
        (2, 1, 1): (Fraction(-1, 8), Fraction(0)),
        (2, -1, 1): (Fraction(1, 8), Fraction(0)),
        (-2, 1, 1): (Fraction(1, 8), Fraction(0)),
        (-2, -1, 1): (Fraction(-1, 8), Fraction(0)),
    })


def run_case(name: str, seq_fn, eps: Fraction, R: Fraction) -> None:
    seq = seq_fn()
    assert seq.is_mean_zero(), "Lean test sequences are mean-zero"

    M = m_of(eps, R)
    delta = mesh_3d(eps, M)

    start = time.perf_counter()
    rounded = round_support(seq, delta, R)
    elapsed = time.perf_counter() - start

    round_err = rounding_error(seq, rounded, delta)
    tail_err = tail_energy(seq, M)
    inside_budget = inside_error_budget(M, delta)
    tail_budget = tail_error_budget(R, M)
    total_budget = inside_budget + tail_budget
    eps_sq = eps * eps

    print(f"╔{'═'*70}╗")
    print(f"║ {name:<66} ║")
    print(f"╚{'═'*70}╝")
    print(f"ε = {eps}  (ε² = {format_sq_err(eps_sq)})")
    print(f"R = {R}")
    print(f"M = {M}")
    print(f"δ = {format_fraction(delta)}")
    print(f"Index set size = (2M+1)³ - 1 = {index_set_cardinality(M):,}")
    print(f"Active modes rounded = {len(seq.coeffs):,}")
    print()
    print("Witness extraction (Python)")
    print("──────────────────────────")
    print(f"Time: {elapsed * 1000:.3f} ms")
    print()
    print("Error accounting")
    print("────────────────")
    print(f"Actual rounding error : {format_sq_err(round_err)}")
    print(f"Actual tail energy    : {format_sq_err(tail_err)}")
    print(f"Inside budget ≤       : {format_sq_err(inside_budget)}")
    print(f"Tail budget ≤         : {format_sq_err(tail_budget)}")
    print(f"Total budget ≤        : {format_sq_err(total_budget)}")
    actual_total = round_err + tail_err
    print(f"Actual total error    : {format_sq_err(actual_total)}")
    print(f"Budget covers ε²?     : {'YES' if total_budget <= eps_sq else 'NO'}")
    print(f"Actual error ≤ ε²?    : {'YES' if actual_total <= eps_sq else 'NO'}")
    print()


def main() -> None:
    print("╔══════════════════════════════════════════════════════════════════════╗")
    print("║  QRK-3D Python Baseline — Constructive Witness Extraction           ║")
    print("║  Matches tests/QRK3DDemo.lean (seq3D_1, seq3D_2, seq3D_3)           ║")
    print("╚══════════════════════════════════════════════════════════════════════╝")
    print()

    cases = [
        ("Test 1: sin(2πx)sin(2πy)sin(2πz)", seq_product_corners, Fraction(1, 10), Fraction(5, 1)),
        ("Test 2: sin(2π(x+y+z))", seq_diagonal, Fraction(1, 20), Fraction(8, 1)),
        ("Test 3: mixed high-frequency mode", seq_mixed_mode, Fraction(1, 10), Fraction(13, 1)),
    ]

    for name, builder, eps, R in cases:
        run_case(name, builder, eps, R)

    print("All QRK-3D witness extractions completed successfully.")


if __name__ == "__main__":
    main()
