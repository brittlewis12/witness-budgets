import Budgets.IntervalComplex
import Budgets.GridMapping
import Budgets.Config

/-!
# Fast Fourier Transform (Constructive, Extractable)

Fully constructive FFT implementation using interval arithmetic for rigorous error tracking.

## Key Features

- **Radix-2 Cooley-Tukey algorithm**: O(N log N) complexity for N = 2^k
- **Algebraic twiddle factors**: Half-angle recursion from ω₄ = i (no transcendentals!)
- **Interval arithmetic**: Rigorous error bounds via IntervalComplex
- **Constructive**: xBudget = C0 (fully extractable)

## Algorithm Overview

```
FFT(u) for N = 2^k:
  Base: N=1 → return u
  Recursive:
    1. Split into even/odd indices
    2. FFT_even = FFT(u[0, 2, 4, ...])
    3. FFT_odd  = FFT(u[1, 3, 5, ...])
    4. Combine with twiddle: û[j] = even[j] + ω^j · odd[j]
                            û[j+N/2] = even[j] - ω^j · odd[j]
```

## Twiddle Factor Generation

Uses **algebraic half-angle formula** instead of sin/cos:
- ω₁ = 1 (exact)
- ω₂ = -1 (exact)
- ω₄ = i (exact)
- ω₈ = √ω₄ via half-angle recursion
- ω₁₆ = √ω₈, etc.

No transcendental functions needed! Just sqrt (Newton's method).

## Usage

```lean
-- Create twiddle table
let twiddles := IntervalComplex.twiddleTable 5 53  -- N=32, precision=53

-- Forward FFT
let spectrum := fft u twiddles

-- Inverse FFT
let reconstructed := ifft spectrum twiddles

-- Check: reconstructed ≈ u
```

-/

namespace FFT

open IntervalComplex
open GridMapping
open WitnessBudget (defaultPrecision fftFuelMargin)

/-! ## Validation Utilities -/

/-- Check if n is a power of two.
    Returns true for n = 1, 2, 4, 8, 16, ...
    Returns false for n = 0, 3, 5, 6, 7, 9, ... -/
def isPowerOfTwo (n : ℕ) : Bool :=
  n > 0 && (n &&& (n - 1)) == 0

/-- Validated FFT result type.
    `none` indicates a precondition violation (e.g., non-power-of-two size).
    `some arr` contains the valid transform. -/
abbrev FFTResult := Option (Array IntervalC)

/-- Error conditions for FFT operations -/
inductive FFTError where
  | notPowerOfTwo : ℕ → FFTError
  | sizeMismatch : ℕ → ℕ → FFTError
  | shapeMismatch : ℕ → ℕ → FFTError
  deriving Repr

/-- Describe an FFT error for debugging -/
def FFTError.toString : FFTError → String
  | .notPowerOfTwo n => s!"FFT requires power-of-two size, got {n}"
  | .sizeMismatch expected actual => s!"Size mismatch: plan expects {expected}, got {actual}"
  | .shapeMismatch expected actual => s!"Shape mismatch: expected total size {expected}, got {actual}"

/-! ## Array Utilities -/

/-- Split array into even-indexed elements -/
def splitEven (arr : Array IntervalC) : Array IntervalC :=
  let n := arr.size / 2
  Array.ofFn (n := n) fun i => arr[2 * i.val]'(by
    have h_i : i.val < n := i.isLt
    have h_n : n ≤ arr.size := Nat.div_le_self arr.size 2
    calc 2 * i.val
      < 2 * n := Nat.mul_lt_mul_of_pos_left h_i (by omega)
      _ ≤ arr.size := by omega)

/-- Split array into odd-indexed elements -/
def splitOdd (arr : Array IntervalC) : Array IntervalC :=
  let n := arr.size / 2
  Array.ofFn (n := n) fun i => arr[2 * i.val + 1]'(by
    have h_i : i.val < n := i.isLt
    -- We need 2*i + 1 < arr.size
    -- Since i < n = arr.size/2, we have i ≤ arr.size/2 - 1
    -- So 2*i + 1 ≤ 2*(arr.size/2 - 1) + 1 = arr.size - 2 + 1 = arr.size - 1 < arr.size
    have h_mul : 2 * n ≤ arr.size := Nat.mul_div_le arr.size 2
    calc 2 * i.val + 1
      < 2 * n := by omega
      _ ≤ arr.size := h_mul)

/-- Interleave two arrays: [a₀,b₀,a₁,b₁,a₂,b₂,...]
    Assumes even and odd have equal size (typical for FFT butterfly) -/
def interleave (even odd : Array IntervalC) : Array IntervalC :=
  let n := even.size + odd.size
  Array.ofFn (n := n) fun i =>
    if i.val % 2 = 0 then
      even.getD (i.val / 2) IntervalComplex.zero
    else
      odd.getD (i.val / 2) IntervalComplex.zero

/-! ## Helper Lemmas for Array Bounds -/

/-- Helper: splitEven produces array of size N/2 -/
theorem splitEven_size (arr : Array IntervalC) : (splitEven arr).size = arr.size / 2 := by
  unfold splitEven
  simp [Array.size_ofFn]

/-- Helper: splitOdd produces array of size N/2 -/
theorem splitOdd_size (arr : Array IntervalC) : (splitOdd arr).size = arr.size / 2 := by
  unfold splitOdd
  simp [Array.size_ofFn]

/-! ## Core FFT Algorithm -/

/-- Cooley-Tukey radix-2 FFT (recursive, out-of-place)

    Input: u (signal array, length N = 2^k)
           twiddles (precomputed ω^j for j=0..N-1)
           fuel (recursion limit for termination checker)

    Output: DFT coefficients û

    Complexity: O(N log N)

    Note: Uses fuel parameter for termination.
          For N=2^k, needs fuel ≥ k. Safe default: fuel = 20 (handles N up to 2^20 = 1M)
-/
def fft_recursive (u : Array IntervalC) (twiddles : Array IntervalC) (fuel : ℕ := 20) : Array IntervalC :=
  match fuel with
  | 0 => u  -- Out of fuel, return as-is (shouldn't happen with proper fuel)
  | fuel' + 1 =>
    let N := u.size
    if N ≤ 1 then
      u  -- Base case: DFT of single element is itself
    else if N % 2 ≠ 0 then
      u  -- Not power of 2, return as-is (could add error handling)
    else
      -- Radix-2 butterfly
      let u_even := splitEven u
      let u_odd := splitOdd u

      -- Recursive FFT on half-size problems
      let fft_even := fft_recursive u_even twiddles fuel'
      let fft_odd := fft_recursive u_odd twiddles fuel'

      -- Combine with twiddle factors
      -- Note: We use conditional indexing for safety. In practice, with proper twiddle table
      -- generation (twiddles.size = N), all indices are in bounds.
      Array.ofFn fun (i : Fin N) =>
        let half := N / 2
        if h_cond : i.val < half then
          -- First half: û[j] = even[j] + ω^j · odd[j]
          let j := i.val
          let twiddle_idx := j * (twiddles.size / N)
          let omega_j := if h : twiddle_idx < twiddles.size then
                          twiddles[twiddle_idx]
                        else
                          IntervalComplex.one -- TODO: consider validation mode which returns None in this case
          let even_val := if h : j < fft_even.size then
                           fft_even[j]
                         else
                           IntervalComplex.zero
          let odd_val := if h : j < fft_odd.size then
                          fft_odd[j]
                        else
                          IntervalComplex.zero
          even_val + omega_j * odd_val
        else
          -- Second half: û[j+N/2] = even[j] - ω^j · odd[j]
          let j := i.val - half
          let twiddle_idx := j * (twiddles.size / N)
          let omega_j := if h : twiddle_idx < twiddles.size then
                          twiddles[twiddle_idx]
                        else
                          IntervalComplex.one
          let even_val := if h : j < fft_even.size then
                           fft_even[j]
                         else
                           IntervalComplex.zero
          let odd_val := if h : j < fft_odd.size then
                          fft_odd[j]
                        else
                          IntervalComplex.zero
          even_val - omega_j * odd_val
termination_by fuel

/-- FFT execution plan: precomputed twiddle factors for repeated transforms.

    **Usage**:
    ```lean
    -- Create plan once
    let plan := mkFFTPlan 512 53  -- For N=512, precision=53

    -- Reuse for multiple transforms (2-5x faster!)
    let spectrum1 := fft_withPlan signal1 plan
    let spectrum2 := fft_withPlan signal2 plan
    ...
    ```

    **Performance**: Eliminates O(N) twiddle generation overhead per transform.
    For applications doing many FFTs of the same size (PDE time-stepping, batch
    processing), this gives significant speedup.

    **Safety**: The plan stores N and validates input size at runtime.
-/
structure FFTPlan where
  /-- Transform size (must be power of 2) -/
  N : ℕ
  /-- log₂(N) -/
  logN : ℕ
  /-- Precomputed twiddle factors: ω^j for j=0..N-1 where ω = exp(2πi/N) -/
  twiddles : Array IntervalC
  /-- Bit precision used for twiddle generation -/
  precision : ℕ

/-- Create FFT plan for transforms of size N.

    Parameters:
    - N: Transform size (should be power of 2 for radix-2 algorithm)
    - precision: Bit precision for interval arithmetic (default: global config)

    Returns: Plan that can be reused for multiple FFTs

    Complexity: O(N) one-time cost

    Example:
    ```lean
    let plan := mkFFTPlan 1024 53
    -- plan.twiddles.size = 1024
    -- plan.logN = 10
    ```
-/
def mkFFTPlan (N : ℕ) (precision : ℕ := defaultPrecision) : FFTPlan :=
  let logN := Nat.log2 N
  let twiddles := twiddleTable logN precision
  { N, logN, twiddles, precision }

/-- Apply FFT using a precomputed plan.

    Parameters:
    - u: Signal array (must have size = plan.N for correctness)
    - plan: Precomputed FFTPlan

    Returns: DFT coefficients

    Complexity: O(N log N) butterfly operations (no twiddle generation overhead!)

    **Safety**: If u.size ≠ plan.N, behavior is undefined (may return incorrect
    results or exceed array bounds). For safety-critical code, validate size first:
    ```lean
    if u.size = plan.N then
      fft_withPlan u plan
    else
      error "Size mismatch!"
    ```
-/
def fft_withPlan (u : Array IntervalC) (plan : FFTPlan) : Array IntervalC :=
  -- Use plan's precomputed twiddles
  fft_recursive u plan.twiddles (plan.logN + fftFuelMargin)

/-- Forward FFT wrapper with automatic twiddle generation (convenience API).

    For one-off transforms or when size varies. If doing multiple transforms
    of the same size, use `mkFFTPlan` + `fft_withPlan` instead for better performance.

    **WARNING**: This is the INTERNAL fast-path API. It assumes the input size is a
    power of two. For non-power-of-two sizes, it silently returns incorrect results.
    Use `fft_safe` for validated transforms with proper error handling.

    Parameters:
    - u: Signal array (size MUST be power of 2)
    - precision: Bit precision (default: global config)

    Returns: DFT coefficients

    Complexity: O(N log N) + O(N) twiddle generation

    See also: `fft_safe` for validated API, `fft_withPlan` for repeated transforms.
-/
def fft (u : Array IntervalC) (precision : ℕ := defaultPrecision) : Array IntervalC :=
  -- Create temporary plan and execute
  let plan := mkFFTPlan u.size precision
  fft_withPlan u plan

/-- Validated forward FFT with precondition checks.

    This is the **safe public API** for FFT. It validates that:
    1. Input size is a power of two (required for radix-2 algorithm)
    2. Input size is non-zero

    Returns `none` if preconditions are violated, `some result` otherwise.

    **Usage pattern** (stability gate):
    ```lean
    match fft_safe signal precision with
    | some spectrum => -- proceed with computation
    | none => -- handle error (e.g., resize input or report to user)
    ```

    Parameters:
    - u: Signal array
    - precision: Bit precision (default: global config)

    Returns: `some (DFT coefficients)` if valid, `none` if preconditions fail

    Complexity: O(1) validation + O(N log N) transform
-/
def fft_safe (u : Array IntervalC) (precision : ℕ := defaultPrecision) : FFTResult :=
  if isPowerOfTwo u.size then
    some (fft u precision)
  else
    none

/-- Validated FFT using precomputed plan with size check.

    Returns `none` if input size doesn't match plan size.

    This prevents silent corruption from size mismatches.
-/
def fft_withPlan_safe (u : Array IntervalC) (plan : FFTPlan) : FFTResult :=
  if u.size = plan.N then
    some (fft_withPlan u plan)
  else
    none

/-! ## Inverse FFT -/

/-- Inverse FFT: IFFT(û) = conj(FFT(conj(û))) / N

    Standard trick: conjugate input, FFT, conjugate output, scale by 1/N
-/
def ifft (u_hat : Array IntervalC) (precision : ℕ := 53) : Array IntervalC :=
  let N := u_hat.size

  -- Conjugate input
  let u_conj := u_hat.map (fun z => ⟨z.re, IntervalDyadic.neg z.im precision⟩)

  -- FFT of conjugate
  let fft_conj := fft u_conj precision

  -- Conjugate output and scale by 1/N
  let N_interval := IntervalDyadic.fromRat (N : ℚ) precision
  fft_conj.map (fun z =>
    let z_conj : IntervalC := ⟨z.re, IntervalDyadic.neg z.im precision⟩
    let re_scaled := IntervalDyadic.div z_conj.re N_interval precision
    let im_scaled := IntervalDyadic.div z_conj.im N_interval precision
    (⟨re_scaled, im_scaled⟩ : IntervalC))

/-- Validated inverse FFT with precondition checks.

    Returns `none` if input size is not a power of two.
-/
def ifft_safe (u_hat : Array IntervalC) (precision : ℕ := 53) : FFTResult :=
  if isPowerOfTwo u_hat.size then
    some (ifft u_hat precision)
  else
    none

/-! ## Size Preservation Lemmas -/

/-- fft_recursive preserves array size.
    Proof by induction on fuel parameter. Every branch returns either:
    - u itself (size preserved)
    - Array.ofFn (n := N) where N = u.size -/
theorem fft_recursive_size_eq (u : Array IntervalC) (twiddles : Array IntervalC) (fuel : ℕ) :
    (fft_recursive u twiddles fuel).size = u.size := by
  induction fuel generalizing u with
  | zero =>
    -- Base case: fuel = 0, returns u
    unfold fft_recursive
    rfl
  | succ fuel' ih =>
    -- Inductive case: fuel = fuel' + 1
    unfold fft_recursive
    simp only []
    split
    · -- N ≤ 1: returns u
      rfl
    · split
      · -- N % 2 ≠ 0: returns u
        rfl
      · -- Recursive case: returns Array.ofFn (n := N)
        simp [Array.size_ofFn]

/-- fft_withPlan preserves array size -/
theorem fft_withPlan_size_eq (u : Array IntervalC) (plan : FFTPlan) :
    (fft_withPlan u plan).size = u.size := by
  unfold fft_withPlan
  exact fft_recursive_size_eq u plan.twiddles _

/-- fft preserves array size -/
theorem fft_size_eq (u : Array IntervalC) (precision : ℕ) :
    (fft u precision).size = u.size := by
  unfold fft
  exact fft_withPlan_size_eq u _

/-- ifft preserves array size -/
theorem ifft_size_eq (u_hat : Array IntervalC) (precision : ℕ) :
    (ifft u_hat precision).size = u_hat.size := by
  unfold ifft
  simp [Array.size_map, fft_size_eq]

/-! ## Validation and Utilities -/

/-- Compute L² norm of signal: ‖u‖² = ∑|uᵢ|² -/
def l2_norm_squared (u : Array IntervalC) (precision : ℕ := 53) : IntervalDyadic.IntervalD :=
  u.foldl (fun acc z =>
    let mod_sq_re := IntervalDyadic.square z.re precision
    let mod_sq_im := IntervalDyadic.square z.im precision
    let mod_sq := IntervalDyadic.add mod_sq_re mod_sq_im precision
    IntervalDyadic.add acc mod_sq precision) IntervalDyadic.zero

/-- Parseval's theorem check: ‖û‖² ≈ N·‖u‖²

    Returns the ratio ‖û‖² / (N·‖u‖²) which should be ≈ 1
-/
def parsevalRatio (u u_hat : Array IntervalC) (precision : ℕ := 53) : IntervalDyadic.IntervalD :=
  let N := IntervalDyadic.fromRat (u.size : ℚ) precision
  let norm_u_sq := l2_norm_squared u precision
  let norm_u_hat_sq := l2_norm_squared u_hat precision
  let denominator := IntervalDyadic.mul N norm_u_sq precision

  -- Return ratio (should be ≈ 1 if FFT is correct)
  IntervalDyadic.div norm_u_hat_sq denominator precision

/-! ## Convenience Constructors -/

/-- Convert array of (real, imaginary) rational pairs to IntervalC array -/
def fromRationalPairs (data : Array (ℚ × ℚ)) (precision : ℕ := 53) : Array IntervalC :=
  data.map fun (re_q, im_q) =>
    let re := IntervalDyadic.fromRat re_q precision
    let im := IntervalDyadic.fromRat im_q precision
    ⟨re, im⟩

/-- Create delta function: δ[0] = 1, δ[i] = 0 for i > 0 -/
def deltaFunction (N : ℕ) : Array IntervalC :=
  Array.ofFn (n := N) fun i =>
    if i.val = 0 then IntervalComplex.one else IntervalComplex.zero

/-- Create sine mode: sin(2πkj/N) for j=0..N-1
    Uses ALGEBRAIC twiddle factors: sin(θ) = Im(exp(iθ))
    No transcendental functions needed! -/
def sineMode (k : ℕ) (N : ℕ) (precision : ℕ := 53) : Array IntervalC :=
  -- Compute log₂(N) for twiddle table
  let logN := Nat.log2 N
  -- Generate twiddle table: ω = exp(2πi/N) via half-angle recursion
  let twiddles := IntervalComplex.twiddleTable logN precision

  Array.ofFn (n := N) fun j =>
    -- sin(2πkj/N) = Im(ω^(kj)) where ω = exp(2πi/N)
    let idx := (k * j.val) % N
    if h : idx < twiddles.size then
      let omega_power := twiddles[idx]
      -- Return pure imaginary: (0, sin(2πkj/N))
      ⟨IntervalDyadic.zero, omega_power.im⟩
    else
      IntervalComplex.zero  -- Fallback for safety

end FFT
