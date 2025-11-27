import Budgets.SpectralOps
import Budgets.IntervalComplex
import Budgets.IntervalDyadic
import Budgets.FFTMultiDim

/-!
# Spectral Operations Demo

Demonstrates the key spectral operations for PDE solvers:
1. FFT-based convolution (O(N log N) speedup)
2. Cubic nonlinearity via FFT
3. Spectral derivative
4. Validation tests

Run with: `lake exe tests/SpectralOpsDemo.lean`
-/

open SpectralOps IntervalComplex IntervalDyadic FFTMultiDim

/-- Leray projection sanity check: for k = (1,0) with û = (1,1),
    projection should zero ux and leave uy. -/
def leray_unit_mode_test : IO Unit := do
  let shape : Fin 2 → ℕ := fun _ => 3   -- 3×3 grid → M = 1
  let total := totalSize shape
  let coords : Fin 2 → ℕ := fun i => if i.val = 0 then 1 else 0
  let idx := toFlatIndex shape coords

  let arr := Array.ofFn (n := total) fun j =>
    if j.val = idx then IntervalComplex.one else IntervalComplex.zero
  let vf : VectorField 2 := ⟨fun i => if i.val = 0 then arr else arr⟩

  let projected := lerayProjection vf shape 53
  let ux := projected.components ⟨0, by decide⟩
  let uy := projected.components ⟨1, by decide⟩
  let ux_re := IntervalDyadic.midpoint ux[idx]!.re
  let uy_re := IntervalDyadic.midpoint uy[idx]!.re

  let tol : ℚ := 1 / 1000
  if abs ux_re > tol || abs (uy_re - 1) > tol then
    throw <| IO.userError s!"❌ Leray projection failed: ux={ux_re}, uy={uy_re} (expected ux≈0, uy≈1)"
  else
    IO.println s!"✓ Leray projection (k=(1,0)) OK: ux≈0, uy≈1"

def main : IO Unit := do
  IO.println "=== Spectral Operations Demo ==="
  IO.println ""

  -- Test 1: FFT Convolution Round-Trip
  IO.println "Test 1: FFT Round-Trip Validation"
  IO.println "-----------------------------------"
  let N := 16  -- Small grid for testing
  let test_signal := Array.ofFn (n := N) fun idx =>
    let val := IntervalDyadic.fromRat ((idx.val : ℚ) / N) 53
    ⟨val, IntervalDyadic.zero⟩

  let (err, rel_err) := validateConvolution test_signal test_signal 7 53
  IO.println s!"  Grid size: N = {N}"
  IO.println s!"  Max error: {err}"
  IO.println s!"  Max relative error: {rel_err}"
  IO.println ""

  -- Test 2: Cubic Nonlinearity
  IO.println "Test 2: Cubic Nonlinearity via FFT"
  IO.println "-----------------------------------"
  let u_cubic := applyCubicFFT test_signal 53
  IO.println s!"  Input size: {test_signal.size}"
  IO.println s!"  Output size: {u_cubic.size}"
  IO.println s!"  Size preserved: {test_signal.size == u_cubic.size}"
  IO.println ""

  -- Test 3: Spectral Derivative
  IO.println "Test 3: Spectral Derivative Test"
  IO.println "-----------------------------------"
  let deriv_error ← testSpectralDerivative 7 53
  IO.println s!"  Result: Max error = {deriv_error}"
  IO.println ""

  -- Test 4: Convolution Identity
  IO.println "Test 4: Convolution Identity (δ * u = u)"
  IO.println "-----------------------------------"
  let conv_error ← testConvolutionIdentity 16 53
  IO.println s!"  Result: Max error = {conv_error}"
  IO.println ""

  -- Test 5: Performance Benchmark
  IO.println "Test 5: Performance Comparison"
  IO.println "-----------------------------------"
  benchmarkConvolution 32 53
  IO.println ""
  benchmarkConvolution 128 53
  IO.println ""

  -- Test 6: Aliasing Demonstration
  IO.println "Test 6: Dealiasing Effect"
  IO.println "-----------------------------------"
  let N_alias := 8
  let u_alias := Array.ofFn (n := N_alias) fun _idx =>
    let val := IntervalDyadic.fromRat (1 / 2) 53
    ⟨val, IntervalDyadic.zero⟩

  IO.println s!"  Computing u³ with N = {N_alias}"
  IO.println s!"  Using 2N = {2 * N_alias} padding to avoid aliasing"
  let u_cube_dealiased := applyCubicFFT u_alias 53
  IO.println s!"  Result size: {u_cube_dealiased.size}"
  IO.println s!"  Padding applied: 2N → truncated back to N"
  IO.println ""

  -- Test 7: Leray projection
  IO.println "Test 7: Leray Projection (divergence-free)"
  IO.println "-----------------------------------"
  leray_unit_mode_test
  IO.println ""

  IO.println "=== Demo Complete ==="
  IO.println ""
  IO.println "Key Takeaways:"
  IO.println "1. FFT convolution: O(N log N) vs O(N²) direct method"
  IO.println "2. Cubic via FFT: 2-stage convolution with 2N padding"
  IO.println "3. Spectral derivative: Exact for bandlimited functions"
  IO.println "4. Aliasing control: Critical for nonlinear PDEs"
  IO.println ""
  IO.println "For Navier-Stokes/Semilinear Heat:"
  IO.println "- Replace O(N³) direct cubic with O(N² log N) FFT method"
  IO.println "- 100x+ speedup for typical grid sizes (N > 64)"
  IO.println "- Enables real-time simulation on larger grids"
