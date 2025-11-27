#!/usr/bin/env python3
"""
Python Baseline for SemilinearHeat (1D)

This script mirrors the interval arithmetic heat PDE demo in tests/HeatDemoInterval.lean.
It simulates the semilinear heat equation:
  ∂ₜu - Δu = u³  on (0,1) × (0,T)

* Match Lean parameters: M=5, dt=1/100000000, amplitude=1/100, steps=100
* Fourier space evolution with cubic nonlinearity

The cubic nonlinearity is computed via two-stage convolution: u³ = (u*u)*u
This reduces complexity from O(N³) to O(N²).
"""

import time
from dataclasses import dataclass

# ==========================================
# 1. Bitwise Ops (Matching BitwiseOps.lean)
# ==========================================


def shift_right_floor(n: int, shift: int) -> int:
    # Lean: if n >= 0 then n / 2^k else ... complex floor logic
    # Python: // is defined as floor division (rounds to -inf)
    # This matches the mathematical intent of IntervalDyadic.
    return n >> shift


def shift_right_ceil(n: int, shift: int) -> int:
    # Matches RoundedDyadic.ceil
    # -(-n // d) is ceiling division
    divisor = 1 << shift
    return -(-n // divisor)


# ==========================================
# 2. Interval Arithmetic (Matching IntervalDyadic.lean)
# ==========================================


@dataclass(slots=True)
class IntervalD:
    lower: int  # Stored as raw integer (num)
    upper: int  # Stored as raw integer (num)
    # We assume fixed precision p implicitly to save object overhead,
    # matching the optimized C structure Lean likely generates.

    @staticmethod
    def from_rat(num: int, den: int, p: int) -> "IntervalD":
        # Matches IntervalDyadic.fromRat
        target = num * (1 << p)
        floor_val = target // den
        ceil_val = -(-target // den)
        return IntervalD(floor_val, ceil_val)

    @staticmethod
    def zero() -> "IntervalD":
        return IntervalD(0, 0)


def add_iv(a: IntervalD, b: IntervalD, p: int) -> IntervalD:
    # Matches IntervalDyadic.add
    # lower = floor((a.l + b.l) / 2^0) -- assuming exp aligned
    # Logic: raw add, then shift if precision needs reduction.
    # In the demo, we usually keep precision fixed at p.
    # But if we accumulate, we might need to shift.
    # Lean's `add` takes `p` and normalizes the result to `p`.

    raw_l = a.lower + b.lower
    raw_u = a.upper + b.upper

    # Check if we need to reduce (in this simplified model, we assume inputs
    # are already at precision p, so sum is at precision p.
    # Note: Lean re-normalizes. If 1/2 + 1/2 = 1, it might reduce exp.
    # For this benchmark, we skip GCD/normalization to give Python a fighting chance,
    # making it effectively "Fixed Point Arithmetic".

    return IntervalD(raw_l, raw_u)
    # Note: Lean adds rounding error 2/2^p here if shifting happens.
    # We are being generous to Python by skipping the shift overhead.


def sub_iv(a: IntervalD, b: IntervalD, p: int) -> IntervalD:
    # [al - bu, au - bl]
    return IntervalD(a.lower - b.upper, a.upper - b.lower)


def mul_iv(x: IntervalD, y: IntervalD, p: int) -> IntervalD:
    # Matches IntervalDyadic.mul
    xl, yl = x.lower, y.lower
    xu, yu = x.upper, y.upper

    p1 = xl * yl
    p2 = xl * yu
    p3 = xu * yl
    p4 = xu * yu

    min_prod = min(p1, p2, p3, p4)
    max_prod = max(p1, p2, p3, p4)

    # Result is at precision 2*p. We must reduce to p.
    # This matches RoundedDyadic.floor/ceil behavior
    l = shift_right_floor(min_prod, p)
    u = shift_right_ceil(max_prod, p)

    return IntervalD(l, u)


# ==========================================
# 3. Physics Kernel (Matching Evolution.lean)
# ==========================================


def apply_cubic_array(u: list[IntervalD], M: int, p: int) -> list[IntervalD]:
    # Matches applyCubic_Array (Direct O(N^2) implementation)
    size = 2 * M + 1

    # 1. u_sq = u * u
    u_sq = [IntervalD.zero() for _ in range(size)]
    for i in range(size):
        k = i - M
        acc = IntervalD.zero()
        for i1 in range(size):
            k1 = i1 - M
            k2 = k - k1
            if -M <= k2 <= M:  # Geometric bounds check
                i2 = k2 + M
                prod = mul_iv(u[i1], u[i2], p)
                acc = add_iv(acc, prod, p)
        u_sq[i] = acc

    # 2. u_cubed = u_sq * u
    u_cubed = [IntervalD.zero() for _ in range(size)]
    for i in range(size):
        k = i - M
        acc = IntervalD.zero()
        for i1 in range(size):
            k1 = i1 - M
            k2 = k - k1
            if -M <= k2 <= M:
                i2 = k2 + M
                prod = mul_iv(u_sq[i1], u[i2], p)
                acc = add_iv(acc, prod, p)
        u_cubed[i] = acc

    return u_cubed


def euler_step_array(
    u: list[IntervalD], dt: IntervalD, M: int, p: int
) -> list[IntervalD]:
    # Matches eulerStep_Array
    size = 2 * M + 1
    cubic = apply_cubic_array(u, M, p)
    res = []

    # Precompute pi^2 approx for Laplacian: 3.1^2 = 9.61
    # Lean uses interval containment for pi, we use a fixed rational approx for speed
    pi_sq_num = 961
    pi_sq_den = 100

    for i in range(size):
        k = i - M

        # Laplacian weight: -π² k²
        # lam = pi_sq * k * k
        lam_num = pi_sq_num * k * k
        lam_den = pi_sq_den

        # We need -lam. Construct IntervalD from rational.
        neg_lam = IntervalD.from_rat(-lam_num, lam_den, p)

        # -λ * u
        term1 = mul_iv(neg_lam, u[i], p)

        # rhs = -λu + u³
        rhs = add_iv(term1, cubic[i], p)

        # step = dt * rhs
        step = mul_iv(dt, rhs, p)

        # new_u = u + step
        new_u = add_iv(u[i], step, p)
        res.append(new_u)

    return res


def main():
    # CONFIGURATION (Matching HeatDemoInterval "Test 4")
    steps = 100
    M = 5  # High Resolution
    p = 32
    dt_rat = (1, 100000000)  # 1e-8 (Stability requirement)
    amp_rat = (1, 100)  # 0.01

    print(f"╔{'═' * 64}╗")
    print(f"║ Python Baseline for SemilinearHeat (1D) (Interval Fixed-Point) ║")
    print(f"║ M={M}, steps={steps}, dt=1e-7, amp=0.01, p={p}                        ║")
    print(f"╚{'═' * 64}╝")

    # Init Data
    dt = IntervalD.from_rat(dt_rat[0], dt_rat[1], p)
    amp = IntervalD.from_rat(amp_rat[0], amp_rat[1], p)

    size = 2 * M + 1
    u = [IntervalD.zero() for _ in range(size)]
    u[0] = amp  # k=-1 (index 0 for M=1)
    u[2] = amp  # k=1  (index 2 for M=1)

    start = time.time()

    for s in range(steps):
        u = euler_step_array(u, dt, M, p)

    end = time.time()

    # Final Analysis (k=1 is index 2)
    k1 = u[2]
    width_raw = k1.upper - k1.lower
    # Lean reported: 101/2^31.
    # Our width_raw is scaled by 2^p (2^32).
    # So expected width_raw is approx 2 * 101 = 202.

    print(f"\nCompleted in {(end - start) * 1000:.2f} ms")
    print(f"Final state k=1 raw: [{k1.lower}, {k1.upper}]")
    print(f"Width (raw): {width_raw}")
    print(f"Width (scaled): {width_raw / (1 << p):.2e}")


if __name__ == "__main__":
    main()
