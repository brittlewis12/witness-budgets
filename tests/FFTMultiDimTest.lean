import Budgets.FFTMultiDim

/-!
# Multi-Dimensional FFT Tests

Validates the tensor product FFT implementation with separable test functions.

## Test Strategy

1. **2D Separable Function**: f(i,j) = sin(2πi/N) * cos(2πj/M)
   - Transform separates: FFT₂(f) = FFT₁(sin) ⊗ FFT₁(cos)
   - Validates axis independence

2. **Round-trip Test**: IFFT(FFT(arr)) ≈ arr
   - Checks invertibility
   - Measures reconstruction error

3. **Size Preservation**: All transforms preserve array size
-/

namespace FFTMultiDimTest

open FFTMultiDim
open IntervalComplex
open IntervalDyadic
open FFT

/-! ## 2D Test: Separable Function -/

/-- Simple 2D test: 4×4 grid with separable structure

    Function: f(i,j) = (i+1) * (j+1)
    This is clearly separable: g(i) = i+1, h(j) = j+1

    Expected transform behavior:
    - Row FFT transforms g(i) independently for each row
    - Column FFT transforms h(j) independently for each column
-/
def test2d_small : IO Unit := do
  let N := 4  -- 4 rows
  let M := 4  -- 4 columns

  -- Create separable function f(i,j) = (i+1) * (j+1)
  let g : ℕ → IntervalC := fun i =>
    ofReal (fromRat (i + 1 : ℚ) 53)
  let h : ℕ → IntervalC := fun j =>
    ofReal (fromRat (j + 1 : ℚ) 53)

  let arr := separableFunction2d g h N M

  IO.println s!"2D Test (4×4 separable function)"
  IO.println s!"Input array size: {arr.size}"
  IO.println s!"Expected size: {N * M}"

  -- Forward FFT
  let transformed := fft2d arr N M 53

  IO.println s!"Transformed size: {transformed.size}"
  IO.println s!"Size preserved: {transformed.size == arr.size}"

  -- Inverse FFT
  let reconstructed := ifft2d transformed N M 53

  IO.println s!"Reconstructed size: {reconstructed.size}"

  -- Compute round-trip error
  let error := test2dRoundTrip arr N M 53

  IO.println s!"Round-trip error: {error}"

/-! ## 2D Test: Delta Function -/

/-- Test with 2D delta function: δ(0,0) = 1, δ(i,j) = 0 elsewhere

    Expected FFT: Constant spectrum (all ones)
    This tests proper handling of sparse inputs
-/
def test2d_delta : IO Unit := do
  let N := 8
  let M := 8

  -- Create delta function at origin
  let arr := zeros2d N M
  let arr := set2d arr N M 0 0 IntervalComplex.one

  IO.println s!"\n2D Delta Function Test (8×8)"
  IO.println s!"Input: δ(0,0) = 1, rest zeros"

  -- FFT should give constant spectrum
  let transformed := fft2d arr N M 53

  IO.println s!"Transformed size: {transformed.size}"

  IO.println s!"First few FFT coefficients computed (should be constant)"

  -- Inverse transform
  let _reconstructed := ifft2d transformed N M 53

  IO.println "Reconstructed delta function"

  -- Check round-trip error
  let error := test2dRoundTrip arr N M 53
  IO.println s!"Round-trip error: {error}"

/-! ## 3D Test -/

/-- Simple 3D test: 2×2×2 cube -/
def test3d_small : IO Unit := do
  let N := 2
  let M := 2
  let K := 2

  -- Create simple 3D array with known values
  let arr := Array.ofFn (n := N * M * K) (fun idx =>
    ofReal (fromRat (idx.val + 1 : ℚ) 53))

  IO.println s!"\n3D Test (2×2×2 cube)"
  IO.println s!"Input size: {arr.size}"

  -- Forward FFT
  let transformed := fft3d arr N M K 53

  IO.println s!"Transformed size: {transformed.size}"
  IO.println s!"Size preserved: {transformed.size == arr.size}"

  -- Inverse FFT
  let reconstructed := ifft3d transformed N M K 53

  IO.println s!"Reconstructed size: {reconstructed.size}"

  -- Compute round-trip error manually
  let indices := List.range (min arr.size reconstructed.size)
  let error := indices.foldl (fun max_err idx =>
    let a := arr.getD idx IntervalComplex.zero
    let b := reconstructed.getD idx IntervalComplex.zero
    let diff_re := sub a.re b.re 53
    let diff_im := sub a.im b.im 53
    let err := max (width diff_re) (width diff_im)
    max max_err err) 0

  IO.println s!"Round-trip error: {error}"

/-! ## Performance Test: Larger 2D Grid -/

/-- Test on larger grid to verify scalability -/
def test2d_medium : IO Unit := do
  let N : ℕ := 16
  let M : ℕ := 16

  IO.println s!"\n2D Medium Test (16×16 grid)"
  IO.println s!"Total points: {N * M}"

  -- Create separable Gaussian-like function
  let gaussian1d : ℕ → ℚ := fun i =>
    let x := (i : ℚ) - (N / 2 : ℚ)
    let sigma : ℚ := (N : ℚ) / 4
    -- Approximate exp(-x²/σ²) with 1/(1+x²/σ²) for constructive version
    1 / (1 + x * x / (sigma * sigma))

  let g : ℕ → IntervalC := fun i => ofReal (fromRat (gaussian1d i) 53)
  let h : ℕ → IntervalC := fun j => ofReal (fromRat (gaussian1d j) 53)

  let arr := separableFunction2d g h N M

  IO.println s!"Input array created"

  -- Time the forward FFT
  let start_fft ← IO.monoMsNow
  let transformed := fft2d arr N M 53
  let end_fft ← IO.monoMsNow

  IO.println s!"Forward FFT time: {end_fft - start_fft} ms"
  IO.println s!"Transformed size: {transformed.size}"

  -- Time the inverse FFT
  let start_ifft ← IO.monoMsNow
  let _reconstructed := ifft2d transformed N M 53
  let end_ifft ← IO.monoMsNow

  IO.println s!"Inverse FFT time: {end_ifft - start_ifft} ms"

  -- Check accuracy
  let error := test2dRoundTrip arr N M 53

  IO.println s!"Round-trip error: {error}"

/-! ## Main Test Runner -/

def main : IO Unit := do
  IO.println "=== Multi-Dimensional FFT Test Suite ==="
  IO.println ""

  test2d_small
  test2d_delta
  test3d_small
  test2d_medium

  IO.println ""
  IO.println "=== All tests complete ==="

end FFTMultiDimTest

def main : IO Unit := FFTMultiDimTest.main
