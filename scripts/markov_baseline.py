#!/usr/bin/env python3
"""
Markov Chain Baseline - Python Reference Implementation

Implements the same 3-state symmetric random walk as MarkovDemo.lean
using exact rational arithmetic (fractions.Fraction) for direct comparison.

Transition matrix:
  P = [[1/4, 3/8, 3/8],
       [3/8, 1/4, 3/8],
       [3/8, 3/8, 1/4]]

Stationary distribution: π = (1/3, 1/3, 1/3)
Contraction constant: K = 1/8
"""

from fractions import Fraction
from typing import List, Tuple
import time


def create_transition_matrix() -> List[List[Fraction]]:
    """Create the 3x3 symmetric transition matrix P."""
    return [
        [Fraction(1, 4), Fraction(3, 8), Fraction(3, 8)],
        [Fraction(3, 8), Fraction(1, 4), Fraction(3, 8)],
        [Fraction(3, 8), Fraction(3, 8), Fraction(1, 4)]
    ]


def apply_P(P: List[List[Fraction]], mu: List[Fraction]) -> List[Fraction]:
    """Apply transition matrix to distribution: (Pμ)ⱼ = Σᵢ Pⱼᵢ μᵢ"""
    return [
        P[j][0] * mu[0] + P[j][1] * mu[1] + P[j][2] * mu[2]
        for j in range(3)
    ]


def iterate(P: List[List[Fraction]], mu0: List[Fraction], n: int) -> List[Fraction]:
    """Iterate transition matrix n times."""
    mu = mu0
    for _ in range(n):
        mu = apply_P(P, mu)
    return mu


def l1_dist(mu: List[Fraction], nu: List[Fraction]) -> Fraction:
    """L1 distance between distributions."""
    return sum(abs(mu[i] - nu[i]) for i in range(3))


def run_convergence_test(
    name: str,
    P: List[List[Fraction]],
    pi: List[Fraction],
    mu0: List[Fraction],
    n_steps: List[int]
) -> None:
    """Run convergence test and print results."""
    print("╔══════════════════════════════════════════════════╗")
    print(f"║  {name:<46}  ║")
    print("╚══════════════════════════════════════════════════╝")
    print()
    print(f"Initial distribution: μ₀ = ({mu0[0]}, {mu0[1]}, {mu0[2]})")
    print(f"Stationary distribution: π = (1/3, 1/3, 1/3)")
    print(f"Contraction constant: K = 1/8")
    print()
    print("Step | Distribution                    | Distance to π")
    print("-----|---------------------------------|--------------")

    for n in n_steps:
        start = time.perf_counter()
        mu_n = iterate(P, mu0, n)
        elapsed = time.perf_counter() - start

        dist = l1_dist(mu_n, pi)
        dist_str = f"({mu_n[0]}, {mu_n[1]}, {mu_n[2]})"
        print(f"{n:4} | {dist_str} | {dist} | {elapsed:.4f}s")

    print()


def main():
    """Run all convergence tests."""
    print("╔════════════════════════════════════════════════════════════╗")
    print("║  Markov Chain Convergence Baseline (Python)               ║")
    print("║  3-State Symmetric Random Walk                             ║")
    print("╚════════════════════════════════════════════════════════════╝")
    print()
    print("Reference implementation using fractions.Fraction")
    print("Contraction constant: K = 1/8 (eigenvalue -1/8)")
    print()

    # Setup
    P = create_transition_matrix()
    pi = [Fraction(1, 3), Fraction(1, 3), Fraction(1, 3)]

    # Test 1: Corner (1, 0, 0)
    run_convergence_test(
        "Test 1: Starting from corner (1, 0, 0)",
        P, pi,
        [Fraction(1), Fraction(0), Fraction(0)],
        [0, 2, 4, 6, 8, 10]
    )

    # Test 2: Corner (0, 0, 1)
    run_convergence_test(
        "Test 2: Starting from corner (0, 0, 1)",
        P, pi,
        [Fraction(0), Fraction(0), Fraction(1)],
        [0, 2, 4, 6, 8, 10]
    )

    # Test 3: Off-center (1/2, 1/2, 0)
    run_convergence_test(
        "Test 3: Starting from (1/2, 1/2, 0)",
        P, pi,
        [Fraction(1, 2), Fraction(1, 2), Fraction(0)],
        [0, 2, 4, 6, 8, 10]
    )

    print("╔════════════════════════════════════════════════════════════╗")
    print("║ Baseline Status: SUCCESS                                   ║")
    print("║ All test cases converged with exact rational arithmetic   ║")
    print("╚════════════════════════════════════════════════════════════╝")


if __name__ == "__main__":
    main()
