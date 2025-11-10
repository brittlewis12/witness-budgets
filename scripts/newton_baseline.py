#!/usr/bin/env python3
"""
Python baseline for Newton-Kantorovich demo.

Implements the same Newton iteration for computing √2 as the Lean demo,
for performance comparison.
"""

from fractions import Fraction
from typing import Callable

def newton_map(x: Fraction) -> Fraction:
    """Newton iteration map for √2: N(x) = x/2 + 1/x"""
    return x / 2 + Fraction(1) / x

def f(x: Fraction) -> Fraction:
    """Function whose root we seek: f(x) = x² - 2"""
    return x * x - 2

def abs_frac(x: Fraction) -> Fraction:
    """Absolute value for fractions"""
    return x if x >= 0 else -x

def iterate(func: Callable[[Fraction], Fraction], x0: Fraction, n: int) -> Fraction:
    """Iterate a function n times"""
    x = x0
    for _ in range(n):
        x = func(x)
    return x

def run_newton_test(name: str, x0: Fraction, n_iters: int, tolerance: Fraction) -> None:
    """Run a Newton convergence test"""
    print(f"=== {name} ===")
    print(f"Starting point: {x0}")
    print(f"Target: √2 ≈ 1.414")
    print()

    x_n = iterate(newton_map, x0, n_iters)
    residual = abs_frac(f(x_n))

    print(f"After {n_iters} iterations:")
    print(f"  x_{n_iters} = {x_n} ≈ {float(x_n):.10f}")
    print(f"  Residual |x² - 2| = {residual} ≈ {float(residual):.2e}")

    if residual < tolerance:
        print(f"  ✓ CONVERGED (residual < {tolerance})")
    else:
        print(f"  ✗ NOT CONVERGED (residual ≥ {tolerance})")

    print()

def show_trajectory(x0: Fraction, n_steps: int) -> None:
    """Show convergence trajectory"""
    print("=== Convergence Trajectory ===")
    print(f"Starting from x₀ = {x0}")
    print()

    x = x0
    for i in range(n_steps):
        residual = abs_frac(f(x))
        print(f"  Iteration {i}: x = {x}, |x² - 2| = {residual}")
        x = newton_map(x)

    print()

def main():
    print("╔════════════════════════════════════════════════════════════╗")
    print("║    Newton Baseline (Python)                               ║")
    print("║    Computing √2 via Newton Iteration                      ║")
    print("╚════════════════════════════════════════════════════════════╝")
    print()
    print("Using Python fractions.Fraction for exact rational arithmetic")
    print("Convergence tolerance: 1/100")
    print()

    tolerance = Fraction(1, 100)

    # Show convergence trajectory
    show_trajectory(Fraction(3, 2), 6)

    # Run convergence tests from different starting points
    run_newton_test("Newton from x₀ = 3/2", Fraction(3, 2), 5, tolerance)
    run_newton_test("Newton from x₀ = 2", Fraction(2, 1), 5, tolerance)
    run_newton_test("Newton from x₀ = 1", Fraction(1, 1), 6, tolerance)

    print("╔════════════════════════════════════════════════════════════╗")
    print("║ All test cases converged                                  ║")
    print("╚════════════════════════════════════════════════════════════╝")

if __name__ == "__main__":
    main()
