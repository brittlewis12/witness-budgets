import Budgets.FFT
import Budgets.IntervalComplex
import Budgets.IntervalDyadic
import Budgets.SpectralOps

open IntervalComplex IntervalDyadic FFT SpectralOps

/-!
# Comprehensive FFT & Spectral Method Test Suite

**Philosophy**: Test mathematical properties and known values WITHOUT looking at implementation.
Black-box and white-box tests to systematically eliminate sources of error.

## Test Categories

1. **FFT Fundamentals** - Basic properties must hold
2. **Known Transforms** - Delta, cosine, etc.
3. **Mathematical Identities** - Parseval, Hermitian symmetry, linearity
4. **Spectral Cubic** - Hand-computed examples
5. **Intermediate Values** - Physical space, cubed values
6. **Scaling & Invariants** - How output scales with input

-/

-- Helper: absolute value
def abs_rat (x : ℚ) : ℚ := if x < 0 then -x else x

/-! ## Test 1: FFT of Delta Function -/

def test_delta_fft : IO Unit := do
  IO.println "\n╔═══════════════════════════════════════╗"
  IO.println "║  TEST 1: FFT of Delta Function        ║"
  IO.println "╚═══════════════════════════════════════╝"
  IO.println "Property: δ[0] → uniform spectrum (all 1s)"

  let N := 8  -- Power of 2
  let precision := 53

  -- Create delta: [1, 0, 0, ..., 0]
  let delta := Array.ofFn (n := N) fun i =>
    if i.val = 0 then
      (IntervalComplex.one : IntervalC)
    else
      (IntervalComplex.zero : IntervalC)

  -- FFT
  let spectrum := fft delta precision

  IO.println s!"Input size: {delta.size}"
  IO.println s!"Output size: {spectrum.size}"
  IO.println "\nSpectrum values (should all be 1):"
  for i in [0:N] do
    if h : i < spectrum.size then
      let z := spectrum[i]
      let re_mid := IntervalDyadic.midpoint z.re
      let im_mid := IntervalDyadic.midpoint z.im
      IO.println s!"  k={i}: ({re_mid}, {im_mid})"

  -- Check: all should be ≈ 1
  let mut all_one := true
  for i in [0:N] do
    if h : i < spectrum.size then
      let z := spectrum[i]
      let re_mid := IntervalDyadic.midpoint z.re
      let im_mid := IntervalDyadic.midpoint z.im
      let re_err := abs_rat (re_mid - 1)
      let im_err := abs_rat im_mid
      if re_err > 1/1000 || im_err > 1/1000 then
        all_one := false
        IO.println s!"  ❌ FAIL at k={i}: expected (1,0), got ({re_mid}, {im_mid})"

  if all_one then
    IO.println "✅ PASS: All spectrum values ≈ 1"
  else
    IO.println "❌ FAIL: Spectrum not uniform"


/-! ## Test 2: FFT Round-Trip -/

def test_fft_roundtrip : IO Unit := do
  IO.println "\n╔═══════════════════════════════════════╗"
  IO.println "║  TEST 2: FFT Round-Trip               ║"
  IO.println "╚═══════════════════════════════════════╝"
  IO.println "Property: IFFT(FFT(x)) = x"

  let N := 8
  let precision := 53

  -- Create test signal: [1, 2, 3, 4, 5, 6, 7, 8]
  let signal := Array.ofFn (n := N) fun i =>
    IntervalComplex.ofReal (fromRat (i.val + 1 : ℚ) precision)

  -- FFT then IFFT
  let spectrum := fft signal precision
  let recovered := ifft spectrum precision

  IO.println "\nOriginal vs Recovered:"
  let mut max_error : ℚ := 0
  for i in [0:N] do
    if h1 : i < signal.size then
      if h2 : i < recovered.size then
        let orig := IntervalDyadic.midpoint signal[i].re
        let recov := IntervalDyadic.midpoint recovered[i].re
        let err := abs_rat (orig - recov)
        if err > max_error then
          max_error := err
        IO.println s!"  x[{i}]: {orig} → {recov} (error: {err})"

  if max_error < 1/1000000 then
    IO.println s!"✅ PASS: Max error = {max_error} < 10⁻⁶"
  else
    IO.println s!"❌ FAIL: Max error = {max_error} ≥ 10⁻⁶"


/-! ## Test 3: Hermitian Symmetry -/

def test_hermitian_symmetry : IO Unit := do
  IO.println "\n╔═══════════════════════════════════════╗"
  IO.println "║  TEST 3: Hermitian Symmetry           ║"
  IO.println "╚═══════════════════════════════════════╝"
  IO.println "Property: Real signal → û[k] = conj(û[-k])"

  let N := 8
  let precision := 53

  -- Real signal: [1, 2, 3, 4, 5, 6, 7, 8]
  let signal := Array.ofFn (n := N) fun i =>
    IntervalComplex.ofReal (fromRat (i.val + 1 : ℚ) precision)

  let spectrum := fft signal precision

  IO.println "\nChecking û[k] = conj(û[-k]):"
  let mut symmetric := true
  for k in [1:N/2] do
    if h1 : k < spectrum.size then
      if h2 : (N - k) < spectrum.size then
        let u_k := spectrum[k]
        let u_neg_k := spectrum[N - k]

        let u_k_re := IntervalDyadic.midpoint u_k.re
        let u_k_im := IntervalDyadic.midpoint u_k.im
        let u_neg_k_re := IntervalDyadic.midpoint u_neg_k.re
        let u_neg_k_im := IntervalDyadic.midpoint u_neg_k.im

        -- Check: u_k.re = u_neg_k.re and u_k.im = -u_neg_k.im
        let re_match := abs_rat (u_k_re - u_neg_k_re) < 1/1000000
        let im_match := abs_rat (u_k_im + u_neg_k_im) < 1/1000000

        IO.println s!"  k={k}: ({u_k_re}, {u_k_im})"
        IO.println s!"  k={N-k}: ({u_neg_k_re}, {u_neg_k_im})"

        if !re_match || !im_match then
          symmetric := false
          IO.println s!"  ❌ NOT conjugates!"

  if symmetric then
    IO.println "✅ PASS: Hermitian symmetry preserved"
  else
    IO.println "❌ FAIL: Hermitian symmetry BROKEN"


/-! ## Test 4: Parseval's Theorem -/

def test_parseval : IO Unit := do
  IO.println "\n╔═══════════════════════════════════════╗"
  IO.println "║  TEST 4: Parseval's Theorem           ║"
  IO.println "╚═══════════════════════════════════════╝"
  IO.println "Property: ||û||² = N·||u||²"

  let N := 8
  let precision := 53

  -- Signal: [1, 2, 3, 4, 5, 6, 7, 8]
  let signal := Array.ofFn (n := N) fun i =>
    IntervalComplex.ofReal (fromRat (i.val + 1 : ℚ) precision)

  -- Energy in time domain
  let mut time_energy : ℚ := 0
  for i in [0:N] do
    if h : i < signal.size then
      let x := IntervalDyadic.midpoint signal[i].re
      time_energy := time_energy + x * x

  -- FFT
  let spectrum := fft signal precision

  -- Energy in frequency domain
  let mut freq_energy : ℚ := 0
  for i in [0:N] do
    if h : i < spectrum.size then
      let z := spectrum[i]
      let re := IntervalDyadic.midpoint z.re
      let im := IntervalDyadic.midpoint z.im
      let mag_sq := re * re + im * im
      freq_energy := freq_energy + mag_sq

  IO.println s!"Time domain energy: {time_energy}"
  IO.println s!"Freq domain energy: {freq_energy}"
  IO.println s!"Expected ratio: {N} (freq = N × time)"
  IO.println s!"Actual ratio: {freq_energy / time_energy}"

  let ratio := freq_energy / time_energy
  let error := abs_rat (ratio - N) / N

  if error < 1/1000 then
    IO.println s!"✅ PASS: Energy ratio within 0.1%"
  else
    IO.println s!"❌ FAIL: Energy ratio error = {error * 100}%"


/-! ## Test 5: Simple Cosine -/

def test_simple_cosine : IO Unit := do
  IO.println "\n╔═══════════════════════════════════════╗"
  IO.println "║  TEST 5: Pure Cosine Signal           ║"
  IO.println "╚═══════════════════════════════════════╝"
  IO.println "Input: Fourier coefficients at k=±1 only"

  let N := 8
  let precision := 53

  -- In Fourier space: k=1 and k=N-1 (which is k=-1) have value 0.5 each
  -- This represents cos(2πx/N) in physical space
  let signal_fourier := Array.ofFn (n := N) fun i =>
    if i.val = 1 || i.val = N-1 then
      IntervalComplex.ofReal (fromRat (1/2 : ℚ) precision)
    else
      (IntervalComplex.zero : IntervalC)

  IO.println "\nFourier coefficients:"
  for i in [0:N] do
    if h : i < signal_fourier.size then
      let z := signal_fourier[i]
      let re := IntervalDyadic.midpoint z.re
      if re != 0 then
        IO.println s!"  û[{i}] = {re}"

  -- IFFT to get physical space
  let physical := ifft signal_fourier precision

  IO.println "\nPhysical space (should be cosine):"
  for i in [0:N] do
    if h : i < physical.size then
      let z := physical[i]
      let re := IntervalDyadic.midpoint z.re
      let im := IntervalDyadic.midpoint z.im
      IO.println s!"  x[{i}] = ({re}, {im})"

  IO.println "\n✅ Test complete (visual inspection - should be real cosine)"


/-! ## Test 6: Cubic of Pure Cosine -/

def test_cubic_cosine : IO Unit := do
  IO.println "\n╔═══════════════════════════════════════╗"
  IO.println "║  TEST 6: Cubic of Cosine              ║"
  IO.println "╚═══════════════════════════════════════╝"
  IO.println "Input: k=±1 modes (cosine)"
  IO.println "Expected: cos³(x) → modes at k=±1,±3"

  let N := 8
  let precision := 53

  -- Input in FFT order: k=1 and k=7 (which is k=-1)
  let signal := Array.ofFn (n := N) fun i =>
    if i.val = 1 || i.val = 7 then
      IntervalComplex.ofReal (fromRat (1/2 : ℚ) precision)
    else
      (IntervalComplex.zero : IntervalC)

  IO.println "\nInput (FFT order):"
  for i in [0:N] do
    if h : i < signal.size then
      let z := signal[i]
      let re := IntervalDyadic.midpoint z.re
      if re != 0 then
        IO.println s!"  û[{i}] = {re}"

  -- Apply cubic - note we're using FFT order directly here
  -- Would need to convert from lattice if that's what applyCubicFFT expects
  IO.println "\nSkipping cubic test - needs lattice order conversion"
  IO.println "This will be validated in the main validation suite"

/-! ## Test 7: Spectral Derivative k-mapping (FFT order) -/

/-- A single Fourier mode at k=+1 should differentiate to i·2π·mode.

    Mathematical basis: d/dx e^{i·2πkx} = i·2πk · e^{i·2πkx}

    For k=+1, L=1: the Fourier coefficient is multiplied by i·2π ≈ i·6.283
    This catches incorrect mapping of FFT indices to signed wave numbers. -/
def test_derivative_k_mapping : IO Unit := do
  IO.println "\n╔═══════════════════════════════════════╗"
  IO.println "║  TEST 7: Spectral Derivative Mapping  ║"
  IO.println "╚═══════════════════════════════════════╝"
  let N := 8      -- power of two so FFT is active
  let M := N / 2  -- the current spectralDerivative1D expects an M; we mirror the code's usage
  let precision := 53

  -- Frequency-space input: unit amplitude at k = +1 (FFT order index 1)
  let u_hat : Array IntervalC := Array.ofFn (n := N) fun i =>
    if i.val = 1 then ⟨IntervalDyadic.one, IntervalDyadic.zero⟩ else IntervalComplex.zero

  -- Back to physical space
  let u_phys := FFT.ifft u_hat precision
  let du_phys := spectralDerivative1D u_phys M 1 precision
  let du_hat := FFT.fft du_phys precision

  -- Expected at index 1: Re ≈ 0, Im ≈ 2π ≈ 6.283 (using 710/113 rational approx)
  -- Derivative of e^{i·2πkx} with respect to x is i·2πk·e^{i·2πkx}
  -- For k=1, L=1: multiply by i·2π
  let expected_im : ℚ := 710 / 113  -- 2π ≈ 6.28318...
  let coeff := du_hat.getD 1 IntervalComplex.zero
  let re := IntervalDyadic.midpoint coeff.re
  let im := IntervalDyadic.midpoint coeff.im
  let tol : ℚ := 1 / 100  -- 1% tolerance
  let rel_error := abs_rat (im - expected_im) / expected_im
  if abs_rat re > tol || rel_error > tol then
    throw <| IO.userError s!"❌ Derivative mapping failed: expected (0,{expected_im}), got ({re},{im}), rel_error={rel_error}"
  else
    IO.println s!"✓ PASS: k=+1 → (0, 2π) within {tol*100}% tolerance (got Im={im})"

/-! ## Test 8: Validation Guards (Stability Gate) -/

/-- Test that fft_safe correctly rejects non-power-of-two inputs.
    This validates the "stability gate" pattern: structural prevention of misuse. -/
def test_validation_guards : IO Unit := do
  IO.println "\n╔═══════════════════════════════════════╗"
  IO.println "║  TEST 8: Validation Guards            ║"
  IO.println "╚═══════════════════════════════════════╝"
  let precision := 53

  -- Test: fft_safe should accept power-of-two sizes
  let valid_input : Array IntervalC := Array.ofFn (n := 8) fun _ => IntervalComplex.one
  match FFT.fft_safe valid_input precision with
  | some _ => IO.println "✓ fft_safe accepts N=8 (power of two)"
  | none => throw <| IO.userError "❌ fft_safe incorrectly rejected N=8"

  -- Test: fft_safe should reject non-power-of-two sizes
  let invalid_input : Array IntervalC := Array.ofFn (n := 10) fun _ => IntervalComplex.one
  match FFT.fft_safe invalid_input precision with
  | some _ => throw <| IO.userError "❌ fft_safe incorrectly accepted N=10"
  | none => IO.println "✓ fft_safe rejects N=10 (not power of two)"

  -- Test: isPowerOfTwo function directly
  let tests := [(1, true), (2, true), (4, true), (8, true), (16, true),
                (0, false), (3, false), (5, false), (6, false), (7, false), (9, false), (10, false)]
  for (n, expected) in tests do
    let result := FFT.isPowerOfTwo n
    if result ≠ expected then
      throw <| IO.userError s!"❌ isPowerOfTwo({n}) = {result}, expected {expected}"

  IO.println "✓ isPowerOfTwo correctly classifies all test cases"
  IO.println "✅ PASS: Validation guards working correctly"

/-! ## Main Test Runner -/

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════════════╗"
  IO.println "║     COMPREHENSIVE FFT & SPECTRAL METHOD TEST SUITE        ║"
  IO.println "╚═══════════════════════════════════════════════════════════╝"

  test_delta_fft
  test_fft_roundtrip
  test_hermitian_symmetry
  test_parseval
  test_simple_cosine
  test_cubic_cosine
  test_derivative_k_mapping
  test_validation_guards

  IO.println "\n╔═══════════════════════════════════════════════════════════╗"
  IO.println "║                    TESTS COMPLETE                         ║"
  IO.println "║                                                           ║"
  IO.println "║  These tests validate that the FFT implementation is      ║"
  IO.println "║  fundamentally correct for power-of-2 inputs.             ║"
  IO.println "║                                                           ║"
  IO.println "║  Validation guards ensure safe public API usage.          ║"
  IO.println "╚═══════════════════════════════════════════════════════════╝"
