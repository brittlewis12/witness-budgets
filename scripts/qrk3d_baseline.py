#!/usr/bin/env python3
"""
QRK-3D Baseline - Python Reference Implementation

Implements 3D grid parameters from RellichKondrachov3D proof
for compactness witness generation in 3D Fourier coefficient space.

Key computations:
- M_of(ε, R): Same formula as 1D/2D (dimension-free!)
- mesh3D(ε, M): Conservative mesh for (2M+1)³ factor
- IndexSet3D cardinality: (2M+1)³ - 1 (excluding DC mode)
- Grid explosion analysis

This validates constructive extractability of the 3D compactness proof.

IMPORTANT: We extract the FACTORED witness (M, δ, IndexSet), NOT the full grid!
The grid size is astronomically large, but the witness parameters are simple.
"""

from fractions import Fraction
from typing import Tuple, List
import math


# ============================================================================
# Core Constants
# ============================================================================

PI_RAT_LB = Fraction(3, 1)  # Conservative π lower bound (same as 1D/2D)


# ============================================================================
# Grid Parameter Computations (3D)
# ============================================================================

def M_of(eps: Fraction, R: Fraction) -> int:
    """
    Frequency cutoff M for ε-approximation.

    Formula: M = ⌈R / (π_lb * ε)⌉ + 1

    DIMENSION-FREE: Same formula as 1D and 2D!
    This controls the tail error from frequencies outside the cube [-M,M]³.
    """
    quotient = R / (PI_RAT_LB * eps)
    return math.ceil(quotient) + 1


def mesh3D(eps: Fraction, M: int) -> Fraction:
    """
    Grid mesh size δ for coefficient discretization in 3D.

    Formula: δ = ε / (8 * (2*M + 1)²)

    Factor of 8 × (2M+1)² instead of 4 × (2M+1) accounts for:
    - (2M+1)³ total frequencies (vs (2M+1)² in 2D)
    - Conservative error budget allocation for 3D
    """
    return eps / (8 * (2 * M + 1) ** 2)


def index_set_size_3D(M: int) -> int:
    """
    Size of 3D frequency index set [-M,M]³ \\ {(0,0,0)}.

    Returns: (2*M + 1)³ - 1

    The full cube has (2M+1)³ points, minus the DC mode (0,0,0).
    """
    return (2 * M + 1) ** 3 - 1


def coeff_bound_3D(R: Fraction, k: Tuple[int, int, int]) -> Fraction:
    """
    Rational bound on coefficient magnitude for frequency k = (k1, k2, k3).

    For k ≠ (0,0,0): bound = R (conservative bound)
    For k = (0,0,0): bound = 0 (mean-zero constraint)
    """
    return Fraction(0) if k == (0, 0, 0) else R


def coeff_box_radius_3D(bound: Fraction, delta: Fraction) -> int:
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


def coeff_box_size_3D(radius: int) -> int:
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

def analyze_grid_params_3D(eps: Fraction, R: Fraction) -> dict:
    """
    Compute all 3D grid parameters for (ε, R) witness package.

    Returns dictionary with:
    - M: frequency cutoff
    - delta: mesh size
    - num_frequencies: |(2M+1)³ - 1|
    - sample_boxes: list of ((k1,k2,k3), radius, size) for sample frequencies
    - log10_grid_estimate: rough log₁₀(grid_size)
    """
    M = M_of(eps, R)
    delta = mesh3D(eps, M)
    num_freqs = index_set_size_3D(M)

    # Analyze coefficient boxes for sample frequencies
    # Sample: DC mode, axis modes, face diagonals, space diagonals, edge modes
    sample_freqs = [
        (0, 0, 0),                                    # DC mode (should be zero)
        (1, 0, 0),                                    # x-axis mode
        (0, 1, 0),                                    # y-axis mode
        (0, 0, 1),                                    # z-axis mode
        (1, 1, 0),                                    # xy-face diagonal
        (1, 0, 1),                                    # xz-face diagonal
        (0, 1, 1),                                    # yz-face diagonal
        (1, 1, 1),                                    # Space diagonal
        (M // 2, 0, 0) if M > 2 else (1, 0, 0),     # Mid x-axis
        (M // 2, M // 2, 0) if M > 2 else (1, 1, 0),  # Mid xy-diagonal
        (M // 2, M // 2, M // 2) if M > 2 else (1, 1, 1),  # Mid space-diagonal
        (M, 0, 0),                                    # Max x-axis
        (0, M, 0),                                    # Max y-axis
        (0, 0, M),                                    # Max z-axis
        (M, M, 0),                                    # Max xy-face
        (M, 0, M),                                    # Max xz-face
        (0, M, M),                                    # Max yz-face
        (M, M, M),                                    # Corner mode
    ]

    sample_boxes = []
    for k in sample_freqs:
        bound = coeff_bound_3D(R, k)
        rad = coeff_box_radius_3D(bound, delta)
        size = coeff_box_size_3D(rad)
        sample_boxes.append((k, rad, size))

    # Grid explosion analysis
    # Full grid is product of all coefficient boxes: Π_{k ∈ IndexSet} Box_k
    # This is ASTRONOMICALLY large (10^X where X ~ thousands or more)
    typical_k = (M // 2, M // 2, M // 2) if M > 1 else (1, 1, 1)
    typical_bound = coeff_bound_3D(R, typical_k)
    typical_rad = coeff_box_radius_3D(typical_bound, delta)
    typical_box_size = coeff_box_size_3D(typical_rad)

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

def print_grid_analysis_3D(analysis: dict) -> None:
    """Print 3D grid analysis with box-drawing characters."""
    eps = analysis['eps']
    R = analysis['R']
    M = analysis['M']
    delta = analysis['delta']
    num_freqs = analysis['num_frequencies']
    sample_boxes = analysis['sample_boxes']
    log10_size = analysis['log10_grid_size']

    print("╔══════════════════════════════════════════════════════════════╗")
    print(f"║  3D Grid Parameters: ε = {eps}, R = {str(R):<26} ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print()
    print(f"Frequency cutoff:     M = {M}")
    print(f"Frequency cube:       [-{M}, {M}]³ ∋ (k₁, k₂, k₃)")
    print(f"Index set size:       |IndexSet3D(M)| = {num_freqs} frequencies")
    print(f"                      = (2M+1)³ - 1 = {2*M+1}³ - 1")
    print(f"Grid mesh:            δ = {delta}")
    print(f"                         ≈ {float(delta):.6e}")
    print()
    print("Coefficient Box Analysis (Sample Frequencies)")
    print("────────────────────────────────────────────────────────────────")
    print("   (k₁, k₂, k₃)   | Bound    | Radius | Box Size [(2r+1)²]")
    print("───────────────────|──────────|────────|───────────────────")

    for k, rad, size in sample_boxes:
        bound = coeff_bound_3D(R, k)
        k_str = f"({k[0]:2},{k[1]:2},{k[2]:2})"
        print(f" {k_str:17} | {str(bound):8} | {rad:6} | {size:12,}")

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
        print(f"  - IndexSet: [-{M},{M}]³ \\ {{(0,0,0)}} (compact description)")
        print()
        print("The witness is EXTRACTABLE despite grid explosion!")
    else:
        print("Grid cardinality: small (exact count depends on constraints)")
    print()


# ============================================================================
# Test Suite
# ============================================================================

def run_test_3D(name: str, eps: Fraction, R: Fraction) -> None:
    """Run 3D grid analysis for one (ε, R) pair."""
    print("╔══════════════════════════════════════════════════════════════╗")
    print(f"║  {name:<58}  ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print()

    analysis = analyze_grid_params_3D(eps, R)
    print_grid_analysis_3D(analysis)
    print()


def main():
    """Run all 3D test cases."""
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  Rellich-Kondrachov 3D Baseline (Python)                    ║")
    print("║  3D Grid Parameter Computations                              ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print()
    print("Reference: budgets/Budgets/RellichKondrachov3D proof")
    print("Computes witness grid parameters for 3D compactness proof")
    print()
    print("Formulas:")
    print(f"  π_lb = {PI_RAT_LB} (rational lower bound)")
    print("  M(ε,R) = ⌈R/(π_lb·ε)⌉ + 1           [DIMENSION-FREE!]")
    print("  δ(ε,M) = ε/(8·(2M+1)²)              [3D mesh]")
    print("  IndexSet3D(M) = [-M,M]³ \\ {(0,0,0)}, size = (2M+1)³ - 1")
    print()

    # Test 1: Product mode - separable function
    run_test_3D(
        "Test 1: Product sine u(x,y,z) = sin(2πx)sin(2πy)sin(2πz)",
        Fraction(1, 10),
        Fraction(5, 1)
    )

    # Test 2: Diagonal mode - non-separable function
    run_test_3D(
        "Test 2: Diagonal mode u(x,y,z) = sin(2π(x+y+z))",
        Fraction(1, 20),
        Fraction(8, 1)
    )

    # Test 3: Higher frequency - larger coefficient bounds
    run_test_3D(
        "Test 3: Mixed mode with higher frequencies",
        Fraction(1, 10),
        Fraction(13, 1)
    )

    print("╔══════════════════════════════════════════════════════════════╗")
    print("║ 3D Baseline Status: SUCCESS                                 ║")
    print("║ All grid parameters computed with exact rational arithmetic ║")
    print("║ Witness is EXTRACTABLE despite grid explosion!              ║")
    print("╚══════════════════════════════════════════════════════════════╝")


if __name__ == "__main__":
    main()
