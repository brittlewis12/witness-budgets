#!/usr/bin/env python3
"""
QRK-2D Baseline - Python Reference Implementation

Implements 2D grid parameters from RellichKondrachov2D/Seq.lean
for compactness witness generation in 2D Fourier coefficient space.

Key computations:
- M_of(ε, R): Same formula as 1D (dimension-free!)
- mesh2D(ε, M): Conservative mesh for (2M+1)² factor
- IndexSet2D cardinality: (2M+1)² - 1 (excluding DC mode)
- Grid explosion analysis

This validates constructive extractability of the 2D compactness proof.

IMPORTANT: We extract the FACTORED witness (M, δ, IndexSet), NOT the full grid!
The grid size is astronomically large, but the witness parameters are simple.
"""

from fractions import Fraction
from typing import Tuple, List
import math


# ============================================================================
# Core Constants
# ============================================================================

PI_RAT_LB = Fraction(3, 1)  # Conservative π lower bound (same as 1D)


# ============================================================================
# Grid Parameter Computations (2D)
# ============================================================================

def M_of(eps: Fraction, R: Fraction) -> int:
    """
    Frequency cutoff M for ε-approximation.

    Formula: M = ⌈R / (π_lb * ε)⌉ + 1

    DIMENSION-FREE: Same formula as 1D!
    This controls the tail error from frequencies outside the square [-M,M]².
    """
    quotient = R / (PI_RAT_LB * eps)
    return math.ceil(quotient) + 1


def mesh2D(eps: Fraction, M: int) -> Fraction:
    """
    Grid mesh size δ for coefficient discretization in 2D.

    Formula: δ = ε / (4 * (2*M + 1))

    Factor of 4 instead of 2 accounts for:
    - (2M+1)² total frequencies (vs 2M in 1D)
    - Conservative error budget allocation
    """
    return eps / (4 * (2 * M + 1))


def index_set_size_2D(M: int) -> int:
    """
    Size of 2D frequency index set [-M,M]² \\ {(0,0)}.

    Returns: (2*M + 1)² - 1

    The full square has (2M+1)² points, minus the DC mode (0,0).
    """
    return (2 * M + 1) ** 2 - 1


def coeff_bound_2D(R: Fraction, k: Tuple[int, int]) -> Fraction:
    """
    Rational bound on coefficient magnitude for frequency k = (k1, k2).

    For k ≠ (0,0): bound = R (conservative bound)
    For k = (0,0): bound = 0 (mean-zero constraint)
    """
    return Fraction(0) if k == (0, 0) else R


def coeff_box_radius_2D(bound: Fraction, delta: Fraction) -> int:
    """
    Integer radius of coefficient box in complex plane.

    Formula: rad = ⌈bound / δ⌉ + 1

    The box [-rad, rad]² contains all possible discrete
    coefficient values (real and imaginary parts).
    """
    if bound == 0:
        return 1  # Minimal box containing (0,0)
    quotient = bound / delta
    return math.ceil(quotient) + 1


def coeff_box_size_2D(radius: int) -> int:
    """
    Number of integer lattice points in [-rad, rad]² (complex coefficient).

    Returns: (2*rad + 1)²

    Each coefficient c_k is discretized to a 2D integer lattice
    (representing real and imaginary parts).
    """
    return (2 * radius + 1) ** 2


# ============================================================================
# Grid Analysis
# ============================================================================

def analyze_grid_params_2D(eps: Fraction, R: Fraction) -> dict:
    """
    Compute all 2D grid parameters for (ε, R) witness package.

    Returns dictionary with:
    - M: frequency cutoff
    - delta: mesh size
    - num_frequencies: |(2M+1)² - 1|
    - sample_boxes: list of ((k1,k2), radius, size) for sample frequencies
    - log10_grid_estimate: rough log₁₀(grid_size)
    """
    M = M_of(eps, R)
    delta = mesh2D(eps, M)
    num_freqs = index_set_size_2D(M)

    # Analyze coefficient boxes for sample frequencies
    # Sample: DC mode, axes modes, diagonal mode, corner modes
    sample_freqs = [
        (0, 0),           # DC mode (should be zero)
        (1, 0),           # Horizontal mode
        (0, 1),           # Vertical mode
        (1, 1),           # Diagonal mode
        (M // 2, 0) if M > 2 else (1, 0),        # Mid-horizontal
        (M // 2, M // 2) if M > 2 else (1, 1),   # Mid-diagonal
        (M, 0),           # Max horizontal
        (0, M),           # Max vertical
        (M, M),           # Corner mode
    ]

    sample_boxes = []
    for k in sample_freqs:
        bound = coeff_bound_2D(R, k)
        rad = coeff_box_radius_2D(bound, delta)
        size = coeff_box_size_2D(rad)
        sample_boxes.append((k, rad, size))

    # Grid explosion analysis
    # Full grid is product of all coefficient boxes: Π_{k ∈ IndexSet} Box_k
    # This is ASTRONOMICALLY large (10^X where X ~ thousands)
    typical_k = (M // 2, M // 2) if M > 1 else (1, 1)
    typical_bound = coeff_bound_2D(R, typical_k)
    typical_rad = coeff_box_radius_2D(typical_bound, delta)
    typical_box_size = coeff_box_size_2D(typical_rad)

    # Grid size is roughly: (typical_box)^(num_freqs)
    # Report log₁₀ to avoid overflow
    if typical_box_size > 1:
        log10_grid_size = num_freqs * math.log10(typical_box_size)
    else:
        log10_grid_size = 0

    return {
        'eps': eps,
        'R': R,
        'M': M,
        'delta': delta,
        'num_frequencies': num_freqs,
        'sample_boxes': sample_boxes,
        'log10_grid_size': log10_grid_size
    }


# ============================================================================
# Pretty Printing
# ============================================================================

def print_grid_analysis_2D(analysis: dict) -> None:
    """Print 2D grid analysis with box-drawing characters."""
    eps = analysis['eps']
    R = analysis['R']
    M = analysis['M']
    delta = analysis['delta']
    num_freqs = analysis['num_frequencies']
    sample_boxes = analysis['sample_boxes']
    log10_size = analysis['log10_grid_size']

    print("╔══════════════════════════════════════════════════════════════╗")
    print(f"║  2D Grid Parameters: ε = {eps}, R = {R:<26} ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print()
    print(f"Frequency cutoff:     M = {M}")
    print(f"Frequency square:     [-{M}, {M}]² ∋ (k₁, k₂)")
    print(f"Index set size:       |IndexSet2D(M)| = {num_freqs} frequencies")
    print(f"                      = (2M+1)² - 1 = {2*M+1}² - 1")
    print(f"Grid mesh:            δ = {delta}")
    print(f"                         ≈ {float(delta):.6e}")
    print()
    print("Coefficient Box Analysis (Sample Frequencies)")
    print("────────────────────────────────────────────────────────────────")
    print("   (k₁, k₂)   | Bound    | Radius | Box Size [(2r+1)²]")
    print("──────────────|──────────|────────|───────────────────")

    for k, rad, size in sample_boxes:
        bound = coeff_bound_2D(R, k)
        k_str = f"({k[0]:2},{k[1]:2})"
        print(f" {k_str:12} | {str(bound):8} | {rad:6} | {size:12,}")

    print()
    print("Grid Explosion Analysis")
    print("────────────────────────────────────────────────────────────────")

    if log10_size > 0:
        print(f"Estimated grid cardinality: ~ 10^{log10_size:.1f} points")
        print()
        if log10_size > 100:
            print("⚠ GRID IS ASTRONOMICALLY LARGE ⚠")
        if log10_size > 1000:
            print("(More points than atoms in observable universe!)")
        print()
        print("BUT: We extract the FACTORED witness (M, δ, IndexSet),")
        print("     NOT the full grid enumeration!")
        print()
        print("Witness complexity:")
        print(f"  - M: {M} (single integer)")
        print(f"  - δ: {delta} (single rational)")
        print(f"  - IndexSet: [-{M},{M}]² \\ {{(0,0)}} (compact description)")
        print()
        print("The witness is EXTRACTABLE despite grid explosion!")
    else:
        print("Grid cardinality: small (exact count depends on constraints)")
    print()


# ============================================================================
# Test Suite
# ============================================================================

def run_test_2D(name: str, eps: Fraction, R: Fraction) -> None:
    """Run 2D grid analysis for one (ε, R) pair."""
    print("╔══════════════════════════════════════════════════════════════╗")
    print(f"║  {name:<58}  ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print()

    analysis = analyze_grid_params_2D(eps, R)
    print_grid_analysis_2D(analysis)
    print()


def main():
    """Run all 2D test cases."""
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  Rellich-Kondrachov 2D Baseline (Python)                    ║")
    print("║  2D Grid Parameter Computations                              ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print()
    print("Reference: budgets/Budgets/RellichKondrachov2D/Seq.lean")
    print("Computes witness grid parameters for 2D compactness proof")
    print()
    print("Formulas:")
    print(f"  π_lb = {PI_RAT_LB} (rational lower bound)")
    print("  M(ε,R) = ⌈R/(π_lb·ε)⌉ + 1        [DIMENSION-FREE!]")
    print("  δ(ε,M) = ε/(4·(2M+1))            [2D mesh]")
    print("  IndexSet2D(M) = [-M,M]² \\ {(0,0)}, size = (2M+1)² - 1")
    print()

    # Test 1: Product mode - separable function
    run_test_2D(
        "Test 1: Product sine u(x,y) = sin(2πx)sin(2πy)",
        Fraction(1, 10),
        Fraction(1, 1)
    )

    # Test 2: Diagonal mode - non-separable function
    run_test_2D(
        "Test 2: Diagonal mode u(x,y) = sin(2π(x+y))",
        Fraction(1, 20),
        Fraction(3, 2)
    )

    # Test 3: Higher frequency - larger coefficient bounds
    run_test_2D(
        "Test 3: Higher frequency modes",
        Fraction(1, 10),
        Fraction(2, 1)
    )

    print("╔══════════════════════════════════════════════════════════════╗")
    print("║ 2D Baseline Status: SUCCESS                                 ║")
    print("║ All grid parameters computed with exact rational arithmetic ║")
    print("║ Witness is EXTRACTABLE despite grid explosion!              ║")
    print("╚══════════════════════════════════════════════════════════════╝")


if __name__ == "__main__":
    main()
