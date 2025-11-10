# Banach Fixed-Point Demo Results

**Date**: 2025-10-28
**Status**: ✅ COMPLETE

## Summary

Constructive Banach demo (six contraction examples) now runs with the gcd-normalized `ConstructiveQ` runtime. Highlights:

- ✅ **Formal verification**: constructive Banach theorem (budgets/Budgets/BanachExtraction.lean)
- ✅ **Executable artifact**: ConstructiveQ iteration (`tests/BanachDemo.lean`)
- ✅ **Performance**: Lean 94.9ms ± 1.7ms vs Python 11.9ms ± 0.8ms (Python 7.94× faster)

## Benchmark Details (2025-10-29 with GCD-optimized ConstructiveQ)

| Implementation | Mean Time | Std Dev | Range | Runs |
|----------------|-----------|---------|-------|------|
| Lean | 94.9 ms | ± 1.7 ms | 92.7 - 100.2 ms | 27 |
| Python | 11.9 ms | ± 0.8 ms | 10.9 - 16.0 ms | 108 |

**Performance Ratio**: Python is **7.94× faster** than Lean

- Command: `hyperfine --warmup 3 --min-runs 20 './.lake/build/bin/banach_demo' 'python3 scripts/banach_baseline.py'`
- System: Apple M-series (ARM64), Lean 4.15.0-rc1, Python 3.x
- Full results: `benchmarks/banach_bench.json`

| Test case | Iterations | Residual (≤ 1e-6) |
|-----------|------------|-------------------|
| Linear (K = 1/2)   | 20 | 1/1_048_576 |
| Slow (K = 9/10)    | 150 | 1/1_000_000 |
| Fast (K = 1/10)    | 20 | 1/1_000_000 |
| Piecewise (K = 7/10) | 50 | 1/1_000_000 |
| Rational (K = 3/5) | 35 | 1/1_000_000 |
| Edge (K = 99/100)  | 1400 | 1/1_000_000 |

Residuals and convergence decisions match the Python baseline exactly.

