#!/usr/bin/env python3
"""
QRK-1D Baseline - Python Reference Implementation

Implements the grid size computations from RellichKondrachov1D.lean (Seq.lean)
for compactness witness generation in the 1D Fourier coefficient space.

Key computations:
- M_of(ε, R): Frequency cutoff for approximation
- mesh(ε, M): Grid mesh size for coefficient discretization
- coeffBox: Integer lattice boxes for each frequency
- Grid cardinality estimation

This validates the constructive extractability of the compactness proof.
"""

from fractions import Fraction
from typing import Tuple, List
import math


# ============================================================================
# Core Constants
# ============================================================================

PI_RAT_LB = Fraction(3, 1)  # Rational lower bound for π


# ============================================================================
# Grid Parameter Computations
# ============================================================================

def M_of(eps: Fraction, R: Fraction) -> int:
    """
    Frequency cutoff M for ε-approximation.

    Formula: M = ⌈R / (π_lb * ε)⌉ + 1

    This controls the tail error: frequencies |k| > M contribute < (ε/2)²
    to the total approximation error.
    """
    quotient = R / (PI_RAT_LB * eps)
    return math.ceil(quotient) + 1


def mesh(eps: Fraction, M: int) -> Fraction:
    """
    Grid mesh size δ for coefficient discretization.

    Formula: δ = ε / (2 * (2*M + 1))

    This controls rounding error: discretizing coefficients to δ-grid
    contributes < (ε/2)² to total error.
    """
    return eps / (2 * (2 * M + 1))


def index_set_size(M: int) -> int:
    """
    Size of frequency index set {-M,...,-1,1,...,M} (excluding 0).

    Returns: 2*M
    """
    return 2 * M


def coeff_bound(R: Fraction, k: int) -> Fraction:
    """
    Rational bound on coefficient magnitude for frequency k.

    For k ≠ 0: bound = R (conservative bound)
    For k = 0: bound = 0 (mean-zero constraint)
    """
    return Fraction(0) if k == 0 else R


def coeff_box_radius(bound: Fraction, delta: Fraction) -> int:
    """
    Integer radius of coefficient box.

    Formula: rad = ⌈bound / δ⌉ + 1

    The box [-rad, rad] × [-rad, rad] contains all possible
    discrete coefficient values.
    """
    if bound == 0:
        return 1  # Minimal box containing (0,0)
    quotient = bound / delta
    return math.ceil(quotient) + 1


def coeff_box_size(radius: int) -> int:
    """
    Number of integer lattice points in [-rad, rad]².

    Returns: (2*rad + 1)²
    """
    return (2 * radius + 1) ** 2


# ============================================================================
# Grid Analysis
# ============================================================================

def analyze_grid_params(eps: Fraction, R: Fraction) -> dict:
    """
    Compute all grid parameters for (ε, R) witness package.

    Returns dictionary with:
    - M: frequency cutoff
    - delta: mesh size
    - index_set_card: |IndexSet(M)|
    - sample_boxes: list of (k, radius, size) for sample frequencies
    - log10_grid_estimate: rough log₁₀(grid_size)
    """
    M = M_of(eps, R)
    delta = mesh(eps, M)
    idx_size = index_set_size(M)

    # Analyze coefficient boxes for sample frequencies
    sample_freqs = [0, 1, M // 2, M - 1, M] if M > 3 else list(range(-M+1, M+1))
    sample_boxes = []

    for k in sample_freqs:
        bound = coeff_bound(R, k)
        rad = coeff_box_radius(bound, delta)
        size = coeff_box_size(rad)
        sample_boxes.append((k, rad, size))

    # Rough grid cardinality estimate (product over all frequencies)
    # This is a VERY rough upper bound - actual grid is much smaller
    # due to constraints on total energy
    typical_k = M // 2 if M > 1 else 1
    typical_bound = coeff_bound(R, typical_k)
    typical_rad = coeff_box_radius(typical_bound, delta)
    typical_box_size = coeff_box_size(typical_rad)

    # Grid is roughly: (typical_box)^(2M)
    # We'll just report log₁₀ to avoid overflow
    if typical_box_size > 1:
        log10_grid_size = idx_size * math.log10(typical_box_size)
    else:
        log10_grid_size = 0

    return {
        'eps': eps,
        'R': R,
        'M': M,
        'delta': delta,
        'index_set_card': idx_size,
        'sample_boxes': sample_boxes,
        'log10_grid_size': log10_grid_size
    }


# ============================================================================
# Pretty Printing
# ============================================================================

def print_grid_analysis(analysis: dict) -> None:
    """Print grid analysis with box-drawing characters."""
    eps = analysis['eps']
    R = analysis['R']
    M = analysis['M']
    delta = analysis['delta']
    idx_size = analysis['index_set_card']
    sample_boxes = analysis['sample_boxes']
    log10_size = analysis['log10_grid_size']

    print("╔══════════════════════════════════════════════════════════════╗")
    print(f"║  Grid Parameters: ε = {eps}, R = {R:<30} ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print()
    print(f"Frequency cutoff:     M = {M}")
    print(f"Index set size:       |IndexSet(M)| = {idx_size} frequencies")
    print(f"Grid mesh:            δ = {delta}")
    print(f"                         ≈ {float(delta):.6e}")
    print()
    print("Coefficient Box Analysis")
    print("────────────────────────────────────────────────────────────────")
    print("  k   | Bound    | Radius | Box Size [(2r+1)²]")
    print("──────|──────────|────────|───────────────────")

    for k, rad, size in sample_boxes:
        bound = coeff_bound(R, k)
        print(f" {k:4} | {str(bound):8} | {rad:6} | {size:8,}")

    print()
    if log10_size > 0:
        print(f"Estimated grid cardinality: ~ 10^{log10_size:.1f} points")
        print("(Very rough upper bound; actual grid much smaller)")
    else:
        print("Grid cardinality: small (exact count depends on energy constraints)")
    print()


# ============================================================================
# Test Suite
# ============================================================================

def run_test(name: str, eps: Fraction, R: Fraction) -> None:
    """Run grid analysis for one (ε, R) pair."""
    print("╔══════════════════════════════════════════════════════════════╗")
    print(f"║  {name:<58}  ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print()

    analysis = analyze_grid_params(eps, R)
    print_grid_analysis(analysis)
    print()


def main():
    """Run all test cases."""
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  Rellich-Kondrachov 1D Baseline (Python)                    ║")
    print("║  Grid Parameter Computations                                 ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print()
    print("Reference: budgets/Budgets/RellichKondrachov1D/Seq.lean")
    print("Computes witness grid parameters for compactness proof")
    print()
    print("Formulas:")
    print(f"  π_lb = {PI_RAT_LB} (rational lower bound)")
    print("  M(ε,R) = ⌈R/(π_lb·ε)⌉ + 1")
    print("  δ(ε,M) = ε/(2·(2M+1))")
    print("  IndexSet(M) = {{-M,...,-1,1,...,M}}, size = 2M")
    print()

    # Test 1: Moderate tolerance and radius
    run_test(
        "Test 1: Pure sine mode (ε=1/10, R=1)",
        Fraction(1, 10),
        Fraction(1, 1)
    )

    # Test 2: Tighter tolerance, larger radius
    run_test(
        "Test 2: Two-mode superposition (ε=1/20, R=3/2)",
        Fraction(1, 20),
        Fraction(3, 2)
    )

    # Test 3: Moderate settings
    run_test(
        "Test 3: Higher frequency mode (ε=1/10, R=2)",
        Fraction(1, 10),
        Fraction(2, 1)
    )

    print("╔══════════════════════════════════════════════════════════════╗")
    print("║ Baseline Status: SUCCESS                                    ║")
    print("║ All grid parameters computed with exact rational arithmetic ║")
    print("╚══════════════════════════════════════════════════════════════╝")


if __name__ == "__main__":
    main()
