#!/usr/bin/env -S uv run
# /// script
# dependencies = []
# ///

"""
Banach Fixed-Point Baseline Implementation

Hand-coded Python reference implementation of the 6 contraction mappings
to benchmark against the Lean extracted code.

Usage: uv run scripts/banach_baseline.py
"""

import time
from typing import Callable, Tuple


def iterate_fixed_point(f: Callable[[float], float], x0: float, n_iters: int) -> float:
    """Iterate f starting from x0 for n_iters steps."""
    x = x0
    for _ in range(n_iters):
        x = f(x)
    return x


def run_test(name: str, f: Callable[[float], float], x0: float, n_iters: int) -> Tuple[float, float]:
    """
    Run a single test case and return (execution_time, final_value).

    Args:
        name: Test case name
        f: Contraction mapping
        x0: Initial point
        n_iters: Number of iterations

    Returns:
        (wall_time_seconds, final_approximation)
    """
    start = time.perf_counter()
    x_n = iterate_fixed_point(f, x0, n_iters)
    end = time.perf_counter()

    wall_time = end - start
    residual = abs(f(x_n) - x_n)

    print(f"✓ Test: {name}")
    print(f"  Iterations run: {n_iters}")
    print(f"  Final value: x_{n_iters} ≈ {x_n:.10f}")
    print(f"  Residual: |f(x_n) - x_n| = {residual:.2e}")
    print(f"  Time: {wall_time*1000:.3f}ms")
    print()

    return wall_time, x_n


def main():
    """Run all 6 test cases matching the Lean implementation."""
    print("=== Banach Fixed-Point Python Baseline ===")
    print("Hand-coded reference implementation")
    print()

    total_start = time.perf_counter()

    # Test 1: Linear (K=0.5)
    linear_f = lambda x: 0.5 * x + 1
    run_test("Linear (K=0.5)", linear_f, 0.0, 20)

    # Test 2: Slow (K=0.9)
    slow_f = lambda x: 0.9 * x + 0.1
    run_test("Slow (K=0.9)", slow_f, 0.0, 150)

    # Test 3: Fast (K=0.1)
    fast_f = lambda x: 0.1 * x + 5
    run_test("Fast (K=0.1)", fast_f, 0.0, 20)

    # Test 4: Piecewise (K=0.7)
    piecewise_f = lambda x: 0.7 * x + 0.3
    run_test("Piecewise (K=0.7)", piecewise_f, 0.0, 50)

    # Test 5: Rational (K=0.6)
    rational_f = lambda x: 0.6 * x + 2
    run_test("Rational (K=0.6)", rational_f, 0.0, 35)

    # Test 6: Edge (K=0.99)
    edge_f = lambda x: 0.99 * x + 0.01
    run_test("Edge (K=0.99)", edge_f, 0.0, 1400)

    total_end = time.perf_counter()
    total_time = total_end - total_start

    print(f"✅ All 6 tests completed!")
    print(f"Total time: {total_time*1000:.3f}ms")


if __name__ == "__main__":
    main()
