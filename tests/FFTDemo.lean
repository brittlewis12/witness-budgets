import Budgets.FFT
import Budgets.IntervalComplex

/-!
# FFT Demo: Validation and Benchmarking

Tests the constructive FFT implementation with:
1. Delta function (should have uniform spectrum)
2. Parseval's theorem (energy conservation)
3. Round-trip FFT→IFFT (should recover original)
4. Performance benchmarking

Run with: lake exe fft_demo
-/

namespace FFTDemo

open FFT
open IntervalComplex
open IntervalDyadic

/-! ## Test Signals -/

/-- Delta function: impulse at t=0 -/
def test_delta (N : ℕ) : Array IntervalC :=
  deltaFunction N

/-- Constant signal: all ones -/
def test_constant (N : ℕ) : Array IntervalC :=
  Array.replicate N one

/-- Deterministic chaos signal - PROPER stress test for FFT
    Formula: phase = (i² · 13 + i · 7) mod 100
    Creates pseudo-random values in [0.1, 1.09] without RNG
    This is the GOLD STANDARD for FFT validation! -/
def test_chaos (N : ℕ) (precision : ℕ := 53) : Array IntervalC :=
  Array.ofFn (n := N) fun i =>
    -- Deterministic chaos (quadratic mixing)
    let phase_re := ((i.val * i.val * 13 + i.val * 7) % 100 : ℕ)
    let phase_im := ((i.val * i.val * 17 + i.val * 11) % 100 : ℕ)
    -- Map to [0.1, 1.09] to avoid zeros (add 1/10 offset)
    let re_val := (phase_re : ℚ) / 100 + 1/10
    let im_val := (phase_im : ℚ) / 100 + 1/10
    ⟨IntervalDyadic.fromRat re_val precision,
     IntervalDyadic.fromRat im_val precision⟩

/-- Simple ramp signal (for basic validation) -/
def test_ramp (N : ℕ) (precision : ℕ := 53) : Array IntervalC :=
  Array.ofFn (n := N) fun i =>
    let re_val := (1 + i.val : ℚ)
    let im_val := (2 + i.val : ℚ)
    ⟨IntervalDyadic.fromRat re_val precision,
     IntervalDyadic.fromRat im_val precision⟩

/-! ## Validation Tests -/

/-- Test 1: Delta function should have uniform spectrum -/
def test1_delta_spectrum (logN : ℕ := 4) (precision : ℕ := 53) : IO Unit := do
  let N := 2^logN
  IO.println s!"Test 1: Delta Function (N={N})"
  IO.println "Expected: Uniform spectrum (all coefficients ≈ 1)"

  let delta := test_delta N
  let spectrum := fft delta precision

  IO.println s!"Spectrum (first 8 coefficients):"
  for i in [0:min 8 N] do
    if h : i < spectrum.size then
      let coeff := spectrum[i]
      IO.println s!"  û[{i}] = ({IntervalDyadic.midpoint coeff.re}, {IntervalDyadic.midpoint coeff.im})"

/-- Test 2: Parseval's theorem - energy conservation
    Uses DETERMINISTIC CHAOS signal for proper stress testing -/
def test2_parseval (logN : ℕ := 5) (precision : ℕ := 53) : IO Unit := do
  let N := 2^logN
  IO.println s!"\nTest 2: Parseval's Theorem (N={N})"
  IO.println "Expected: ‖û‖² / (N·‖u‖²) ≈ 1"
  IO.println "Signal: Deterministic chaos (quadratic mixing)"

  let signal := test_chaos N precision
  let spectrum := fft signal precision

  -- Debug: show first value to confirm non-zero
  if h : 0 < signal.size then
    let s0 := signal[0]
    IO.println s!"  First signal value: ({IntervalDyadic.midpoint s0.re}, {IntervalDyadic.midpoint s0.im})"

  let ratio := parsevalRatio signal spectrum precision
  let ratio_mid := IntervalDyadic.midpoint ratio
  let ratio_w := IntervalDyadic.width ratio
  IO.println s!"Energy ratio: {ratio_mid}"
  IO.println s!"  (width = {ratio_w}, should be small)"

  let deviation := ratio_mid - 1
  let deviation_abs := if deviation ≥ 0 then deviation else -deviation
  if deviation_abs < 1/100 then  -- Tighter: 1% tolerance (expect ~10⁻¹⁵ with proper signal!)
    IO.println s!"✓ PASS: Parseval's theorem holds (deviation = {deviation_abs})"
  else
    IO.println s!"✗ FAIL: Energy not conserved! (deviation = {deviation_abs})"

/-- Test 3: Round-trip FFT→IFFT -/
def test3_roundtrip (logN : ℕ := 4) (precision : ℕ := 53) : IO Unit := do
  let N := 2^logN
  IO.println s!"\nTest 3: Round-trip FFT→IFFT (N={N})"
  IO.println "Expected: IFFT(FFT(u)) ≈ u"

  let original := test_chaos N precision
  let spectrum := fft original precision
  let reconstructed := ifft spectrum precision

  IO.println "Comparing original vs. reconstructed (first 4 elements):"
  let mut max_rel_error : ℚ := 0

  for i in [0:min 4 N] do
    if h : i < original.size then
      let orig := original[i]
      let recon := reconstructed[i]'(by
        -- Size preservation: reconstructed = ifft spectrum, spectrum = fft original
        -- Both fft and ifft preserve size
        have h_spectrum : spectrum.size = original.size := FFT.fft_size_eq original precision
        have h_recon : reconstructed.size = spectrum.size := FFT.ifft_size_eq spectrum precision
        have h_size : reconstructed.size = original.size := by
          rw [h_recon, h_spectrum]
        omega)

      let orig_re_mid := IntervalDyadic.midpoint orig.re
      let orig_im_mid := IntervalDyadic.midpoint orig.im
      let recon_re_mid := IntervalDyadic.midpoint recon.re
      let recon_im_mid := IntervalDyadic.midpoint recon.im

      -- Compute relative error
      let re_error := if orig_re_mid ≠ 0 then
        let diff := orig_re_mid - recon_re_mid
        let abs_diff := if diff ≥ 0 then diff else -diff
        abs_diff / (if orig_re_mid ≥ 0 then orig_re_mid else -orig_re_mid)
      else 0

      let im_error := if orig_im_mid ≠ 0 then
        let diff := orig_im_mid - recon_im_mid
        let abs_diff := if diff ≥ 0 then diff else -diff
        abs_diff / (if orig_im_mid ≥ 0 then orig_im_mid else -orig_im_mid)
      else 0

      if i < 2 then  -- Only print first 2 for brevity
        IO.println s!"  u[{i}]: orig=({orig_re_mid}, {orig_im_mid})"
        IO.println s!"        recon=({recon_re_mid}, {recon_im_mid})"

      max_rel_error := max max_rel_error (max re_error im_error)

  IO.println s!"Max relative error: {max_rel_error}"
  if max_rel_error < 1/100 then  -- Less than 1% error
    IO.println "✓ PASS: Round-trip successful (within 1% tolerance)"
  else
    IO.println s!"✗ FAIL: Large relative error ({max_rel_error})"

/-- Test 4: Constant signal (should have DC-only spectrum) -/
def test4_constant (logN : ℕ := 4) (precision : ℕ := 53) : IO Unit := do
  let N := 2^logN
  IO.println s!"\nTest 4: Constant Signal (N={N})"
  IO.println "Expected: DC component = N, all others ≈ 0"

  let signal := test_constant N
  let spectrum := fft signal precision

  IO.println "Spectrum (first 4 coefficients):"
  for i in [0:min 4 N] do
    if h : i < spectrum.size then
      let coeff := spectrum[i]
      let re := IntervalDyadic.midpoint coeff.re
      let im := IntervalDyadic.midpoint coeff.im
      IO.println s!"  û[{i}] = ({re}, {im})"

  -- Check DC component
  if h : 0 < spectrum.size then
    let dc := spectrum[0]
    let dc_re := IntervalDyadic.midpoint dc.re
    let expected := (N : ℚ)
    let error := if dc_re ≥ expected then dc_re - expected else expected - dc_re
    if error < 1/10 then
      IO.println "✓ PASS: DC component correct"
    else
      IO.println s!"✗ FAIL: DC component = {dc_re}, expected ≈ {expected}"

/-! ## Performance Benchmark -/

/-- Benchmark FFT performance - STRESS TEST with larger sizes
    Uses deterministic chaos signal and multiple iterations for accurate timing -/
def benchmark : IO Unit := do
  IO.println ("\n" ++ String.replicate 60 '=')
  IO.println "FFT Performance Benchmark (Deterministic Chaos Signal)"
  IO.println (String.replicate 60 '=')
  IO.println "Note: Includes algebraic half-angle twiddle generation overhead"

  -- Small sizes: loop 100x for measurable timing
  for logN in [4, 5, 6] do
    let N := 2^logN
    let signal := test_chaos N 53
    let iterations := 100

    let start ← IO.monoMsNow
    for _ in [0:iterations] do
      let spectrum := fft signal 53
      let _ := spectrum.back?  -- Force evaluation
    let elapsed ← IO.monoMsNow

    let time_per_fft := (elapsed - start : ℚ) / iterations
    let ops_estimate := N * logN  -- Rough O(N log N) operations
    IO.println s!"N={N}  ({iterations}x):  {time_per_fft} ms/FFT  (~{ops_estimate} ops)"

  -- Larger sizes: loop for measurable timing
  for logN in [7, 8, 9, 10, 11, 12] do
    let N := 2^logN
    let signal := test_chaos N 53
    let iterations := if N <= 512 then 10 else if N <= 2048 then 3 else 1

    let start ← IO.monoMsNow
    for _ in [0:iterations] do
      let spectrum := fft signal 53
      let _ := spectrum.back?  -- Force evaluation
    let elapsed ← IO.monoMsNow

    let time_per_fft := if iterations > 1 then (elapsed - start : ℚ) / iterations else (elapsed - start : ℚ)
    let ops_estimate := N * logN
    let throughput := if time_per_fft > 0 then (ops_estimate : ℚ) / time_per_fft else ops_estimate
    if iterations > 1 then
      IO.println s!"N={N}  ({iterations}x):  {time_per_fft} ms/FFT  ({throughput} Kops/ms)"
    else
      IO.println s!"N={N}:  {time_per_fft} ms  ({throughput} Kops/ms)"

/-! ## Main Entry Point -/

def main : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════════╗"
  IO.println "║         Constructive FFT Validation Suite               ║"
  IO.println "║  Algebraic twiddle factors + Interval arithmetic        ║"
  IO.println "╚══════════════════════════════════════════════════════════╝"

  -- Run validation tests
  test1_delta_spectrum 4 53
  test2_parseval 5 53
  test3_roundtrip 4 53
  test4_constant 4 53

  -- Run benchmark
  benchmark

  IO.println ("\n" ++ String.replicate 60 '=')
  IO.println "Summary:"
  IO.println "  • FFT uses algebraic half-angle recursion (no sin/cos!)"
  IO.println "  • Interval arithmetic provides rigorous error bounds"
  IO.println "  • Fully constructive (xBudget = C0)"
  IO.println "  • Ready for multi-D extension and PDE integration"
  IO.println (String.replicate 60 '=')

end FFTDemo

def main : IO Unit := FFTDemo.main
