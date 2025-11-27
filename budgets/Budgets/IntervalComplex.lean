import Budgets.IntervalDyadic
import Budgets.Config
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# Complex Interval Arithmetic

Interval arithmetic for complex numbers represented as pairs of real intervals.
Fully constructive (C0) and extractable.

Key operations:
- Arithmetic: add, mul, neg, sub
- Special: square, sqrt (for twiddle factor generation)
- Error tracking: width bounds for FFT analysis

## Design

We represent complex intervals as `(re: IntervalD, im: IntervalD)` where each
component is a real interval. This gives rigorous containment guarantees for
complex arithmetic operations.

## Precision

All operations use `WitnessBudget.defaultPrecision` (53 bits) unless explicitly
overridden. This ensures consistency across the entire FFT pipeline.
-/

namespace IntervalComplex

open IntervalDyadic
open WitnessBudget (defaultPrecision)

/-- Complex interval: rectangle in complex plane -/
structure IntervalC where
  re : IntervalD
  im : IntervalD

/-- Zero complex interval -/
def zero : IntervalC := ⟨IntervalDyadic.zero, IntervalDyadic.zero⟩

/-- Exact real value as complex interval -/
def ofReal (r : IntervalD) : IntervalC := ⟨r, IntervalDyadic.zero⟩

/-- Exact imaginary value as complex interval -/
def ofImag (i : IntervalD) : IntervalC := ⟨IntervalDyadic.zero, i⟩

/-- Complex interval from real and imaginary parts -/
def mk (re im : IntervalD) : IntervalC := ⟨re, im⟩

/-- The complex number 1 -/
def one : IntervalC := ofReal IntervalDyadic.one

/-- The complex number i -/
def i : IntervalC := ofImag IntervalDyadic.one

/-- Complex negation: -(a+bi) = -a - bi -/
def neg (z : IntervalC) (p : ℕ := defaultPrecision) : IntervalC :=
  ⟨IntervalDyadic.neg z.re p, IntervalDyadic.neg z.im p⟩

/-- Complex addition: (a+bi) + (c+di) = (a+c) + (b+d)i -/
def add (z w : IntervalC) (p : ℕ := defaultPrecision) : IntervalC :=
  ⟨IntervalDyadic.add z.re w.re p, IntervalDyadic.add z.im w.im p⟩

/-- Complex subtraction -/
def sub (z w : IntervalC) (p : ℕ := defaultPrecision) : IntervalC :=
  add z (neg w p) p

/-- Complex multiplication: (a+bi)(c+di) = (ac-bd) + (ad+bc)i -/
def mul (z w : IntervalC) (p : ℕ := defaultPrecision) : IntervalC :=
  let ac := IntervalDyadic.mul z.re w.re p
  let bd := IntervalDyadic.mul z.im w.im p
  let ad := IntervalDyadic.mul z.re w.im p
  let bc := IntervalDyadic.mul z.im w.re p
  ⟨IntervalDyadic.sub ac bd p, IntervalDyadic.add ad bc p⟩

/-- Complex square: z² (optimized, fewer ops than z*z) -/
def square (z : IntervalC) (p : ℕ := defaultPrecision) : IntervalC :=
  let re_sq := IntervalDyadic.square z.re p
  let im_sq := IntervalDyadic.square z.im p
  let re_im := IntervalDyadic.mul z.re z.im p
  ⟨IntervalDyadic.sub re_sq im_sq p, IntervalDyadic.add re_im re_im p⟩  -- 2*re*im

/-- Maximum width (uncertainty) of complex interval
    Uses decidable comparison to avoid classical Lattice ℚ contamination -/
def width (z : IntervalC) : ℚ :=
  if IntervalDyadic.width z.re ≤ IntervalDyadic.width z.im then
    IntervalDyadic.width z.im
  else
    IntervalDyadic.width z.re

/-- Modulus bound: |z| ≤ √(re² + im²) -/
def modulusBound (z : IntervalC) (p : ℕ := defaultPrecision) : IntervalD :=
  let re_sq := IntervalDyadic.square z.re p
  let im_sq := IntervalDyadic.square z.im p
  -- Upper bound: use upper bounds of re², im²
  let sum := IntervalDyadic.add re_sq im_sq p
  IntervalDyadic.sqrt sum p

/-- Real part -/
def realPart (z : IntervalC) : IntervalD := z.re

/-- Imaginary part -/
def imagPart (z : IntervalC) : IntervalD := z.im

-- Notation support (using default precision)
instance : Add IntervalC := ⟨fun a b => add a b defaultPrecision⟩
instance : Mul IntervalC := ⟨fun a b => mul a b defaultPrecision⟩
instance : Neg IntervalC := ⟨fun a => neg a defaultPrecision⟩
instance : Sub IntervalC := ⟨fun a b => sub a b defaultPrecision⟩
instance : Zero IntervalC := ⟨zero⟩
instance : One IntervalC := ⟨one⟩

/-! ## Twiddle Factor Generation via Half-Angle Formula

For radix-2 FFT, we only need roots of unity ω_N where N = 2^k.

Key insight: Use algebraic half-angle formula instead of transcendental functions!

Starting values (exact):
- ω₁ = 1
- ω₂ = -1
- ω₄ = i

Recursive formula:
- cos(θ/2) = √((1 + cos(θ))/2)
- sin(θ/2) = ±√((1 - cos(θ))/2)

For principal branch (0 ≤ θ < 2π), sin(θ/2) ≥ 0.
-/

/-- Generate ω_N = exp(2πi/N) using half-angle recursion

    For N = 2^k, we recursively compute:
    ω_{2N} from ω_N via half-angle formula

    Example: ω₈ = √((1+i)/2) computed from ω₄ = i
-/
def omega_halfAngle (logN : ℕ) (precision : ℕ := 53) : IntervalC :=
  let rec go (k : ℕ) (w : IntervalC) : IntervalC :=
    match k with
    | 0 => w  -- Base case reached
    | k'+1 =>
      -- Half-angle: ω_{N/2} → ω_N
      -- cos(θ/2) = √((1 + cos(θ))/2)
      -- sin(θ/2) = √((1 - cos(θ))/2)
      let one_plus_cos := IntervalDyadic.add IntervalDyadic.one w.re precision
      let one_minus_cos := IntervalDyadic.sub IntervalDyadic.one w.re precision
      let cos_half := IntervalDyadic.sqrt (IntervalDyadic.half one_plus_cos) precision
      let sin_half := IntervalDyadic.sqrt (IntervalDyadic.half one_minus_cos) precision
      go k' ⟨cos_half, sin_half⟩

  -- Start from known exact values
  match logN with
  | 0 => one                                                   -- ω₁ = 1
  | 1 => ofReal (IntervalDyadic.neg IntervalDyadic.one precision)  -- ω₂ = -1
  | 2 => i                                                     -- ω₄ = i
  | k+3 => go (k+1) i                                          -- Recurse from ω₄

/-- Generate full twiddle table for FFT of size N = 2^k

    Returns array of ω^j for j = 0..N-1 where ω = exp(2πi/N)

    Uses efficient strategy:
    - ω⁰ = 1
    - ω¹ = omega_halfAngle(k)
    - ω^j = (ω^{j-1}) * ω for j > 1 (iterative multiplication)
-/
def twiddleTable (logN : ℕ) (precision : ℕ := 53) : Array IntervalC :=
  let N := 2^logN
  let omega := omega_halfAngle logN precision

  -- Iteratively compute ω^j from ω^{j-1}
  let rec buildTable (j : ℕ) (current : IntervalC) (acc : Array IntervalC) : Array IntervalC :=
    if j ≥ N then acc
    else buildTable (j+1) (mul current omega precision) (acc.push current)

  buildTable 0 one #[]

/-! ## Correctness: omega_exact matches exp(2πi/2^k)

This section proves that the algebraic half-angle formula correctly computes
primitive roots of unity by matching the transcendental exponential formula.
-/

open Real Complex

/-! ### Exact version (no interval rounding) -/

/-- Exact computation of ω_{2^k} without interval arithmetic.
    This is easier to reason about than the interval version. -/
noncomputable def omega_exact : ℕ → ℂ
  | 0 => 1                  -- ω₁ = 1
  | 1 => -1                 -- ω₂ = -1
  | 2 => Complex.I          -- ω₄ = i
  | k+3 =>
      -- Recurse using half-angle formula
      let w := omega_exact (k+2)
      let cos_half := Real.sqrt ((1 + w.re) / 2)
      let sin_half := Real.sqrt ((1 - w.re) / 2)
      ⟨cos_half, sin_half⟩

/-! ### Base cases -/

theorem omega_exact_zero : omega_exact 0 = 1 := rfl

theorem omega_exact_one : omega_exact 1 = -1 := rfl

theorem omega_exact_two : omega_exact 2 = Complex.I := rfl

-- Verify base cases match exp formula
theorem omega_exact_zero_correct :
    omega_exact 0 = Complex.exp (2 * π * Complex.I / 1) := by
  rw [omega_exact_zero]
  simp only [div_one]
  exact Complex.exp_two_pi_mul_I.symm

theorem omega_exact_one_correct :
    omega_exact 1 = Complex.exp (2 * π * Complex.I / 2) := by
  rw [omega_exact_one]
  have : (2 : ℂ) * π * I / 2 = π * I := by ring
  rw [this]
  exact Complex.exp_pi_mul_I.symm

theorem omega_exact_two_correct :
    omega_exact 2 = Complex.exp (2 * π * Complex.I / 4) := by
  rw [omega_exact_two]
  have : (2 : ℂ) * π * I / 4 = π / 2 * I := by ring
  rw [this]
  exact Complex.exp_pi_div_two_mul_I.symm

/-! ### Half-angle formulas -/

/-- Helper: half-angle formula for cosine.
    Note: Requires θ ≤ π (not 2π) because cos(θ/2) ≥ 0 only when θ/2 ∈ [0, π/2].
    This is sufficient for FFT twiddle factors where θ = 2π/2^k ≤ π for k ≥ 1. -/
theorem cos_half_angle (θ : ℝ) (h : 0 ≤ θ) (h' : θ ≤ π) :
    Real.cos (θ / 2) = Real.sqrt ((1 + Real.cos θ) / 2) := by
  -- Use the identity: cos²(θ/2) = (1 + cos(θ)) / 2
  -- From Real.cos_sq: cos x ^ 2 = 1 / 2 + cos (2 * x) / 2
  have h1 : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by
    rw [Real.cos_sq (θ / 2)]
    ring_nf
  -- cos(θ/2) ≥ 0 for θ ∈ [0, π] when θ/2 ∈ [0, π/2]
  have h_pos : 0 ≤ Real.cos (θ / 2) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · linarith
    · linarith
  -- Take square root of both sides
  symm
  rw [← Real.sqrt_sq h_pos, h1]

/-- Helper: half-angle formula for sine in the principal range -/
theorem sin_half_angle (θ : ℝ) (h : 0 ≤ θ) (h' : θ ≤ 2 * π) :
    Real.sin (θ / 2) = Real.sqrt ((1 - Real.cos θ) / 2) := by
  -- Use sin²(θ/2) + cos²(θ/2) = 1 and cos²(θ/2) = (1 + cos θ) / 2
  have h1 : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
    rw [Real.sin_sq]
    have h2 : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by
      rw [Real.cos_sq (θ / 2)]
      ring_nf
    rw [h2]
    ring_nf
  -- sin(θ/2) ≥ 0 for θ ∈ [0, 2π], since θ/2 ∈ [0, π]
  have h_pos : 0 ≤ Real.sin (θ / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith
    · linarith
  -- Take square root of both sides
  symm
  rw [← Real.sqrt_sq h_pos, h1]

/-- Helper: exp(θ/2) in terms of half-angle formulas -/
theorem exp_half_from_half_angle (θ : ℝ) (h : 0 ≤ θ) (h' : θ ≤ π) :
    Complex.exp (θ * Complex.I / 2) =
    ⟨Real.sqrt ((1 + Real.cos θ) / 2), Real.sqrt ((1 - Real.cos θ) / 2)⟩ := by
  -- Step 1: Normalize θ * I / 2 to (θ / 2) * I
  have h1 : θ * Complex.I / 2 = ↑(θ / 2) * Complex.I := by
    push_cast
    ring
  rw [h1]

  -- Step 2: Apply Euler's formula exp(z) = exp(re(z)) * (cos(im(z)) + i*sin(im(z)))
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos]

  -- Step 3: Simplify re and im of (θ/2) * I
  -- re((θ/2) * I) = re(θ/2) * re(I) - im(θ/2) * im(I) = (θ/2) * 0 - 0 * 1 = 0
  -- im((θ/2) * I) = re(θ/2) * im(I) + im(θ/2) * re(I) = (θ/2) * 1 + 0 * 0 = θ/2
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
             Complex.I_re, Complex.I_im]
  simp only [mul_zero, sub_zero, add_zero, mul_one]

  -- Step 4: Simplify exp(0) = 1
  simp only [Complex.ofReal_zero, Complex.exp_zero, one_mul]

  -- Step 5: Now we have cos(θ/2) + I * sin(θ/2) = ⟨√((1+cos θ)/2), √((1-cos θ)/2)⟩
  -- Prove this component-wise using Complex.ext
  apply Complex.ext
  · -- Real part: cos(θ/2) = √((1 + cos θ)/2)
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero]
    simp only [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
    -- Goal: Real.cos (θ / 2) + (0 - 0 * 1) = √((1 + Real.cos θ) / 2)
    -- First simplify the LHS arithmetic
    have : (0 : ℝ) - 0 * 1 = 0 := by norm_num
    rw [this, add_zero]
    exact cos_half_angle θ h h'
  · -- Imaginary part: sin(θ/2) = √((1 - cos θ)/2)
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one]
    simp only [Complex.cos_ofReal_im, Complex.sin_ofReal_re]
    simp only [add_zero, zero_add]
    -- sin_half_angle requires θ ≤ 2π, but we have θ ≤ π which is stronger
    have h'' : θ ≤ 2 * π := by linarith
    exact sin_half_angle θ h h''

/-! ### Main correctness theorem -/

/-- The exact omega function computes the primitive 2^k-th root of unity -/
theorem omega_exact_eq_exp (k : ℕ) :
    omega_exact k = Complex.exp (2 * π * Complex.I / (2^k : ℂ)) := by
  match k with
  | 0 =>
      simp only [pow_zero]
      exact omega_exact_zero_correct
  | 1 =>
      simp only [pow_one]
      exact omega_exact_one_correct
  | 2 =>
      norm_num
      exact omega_exact_two_correct
  | k+3 =>
      -- The recursive case: use half-angle formula and induction
      -- Step 1: Get induction hypothesis for omega_exact (k+2)
      have ih : omega_exact (k+2) = Complex.exp (2 * π * Complex.I / (2^(k+2) : ℂ)) :=
        omega_exact_eq_exp (k+2)

      -- Step 2: Set θ = 2π/2^(k+2) and prove bounds
      let θ := 2 * π / 2^(k+2)

      have h_lower : 0 ≤ θ := by
        apply div_nonneg
        · apply mul_nonneg
          · norm_num
          · exact Real.pi_pos.le
        · exact (pow_pos (by norm_num : (0 : ℝ) < 2) (k+2)).le

      have h_upper : θ ≤ π := by
        -- Since k ≥ 0, we have k+2 ≥ 2, so 2^(k+2) ≥ 4 ≥ 2
        -- Therefore 2π/2^(k+2) ≤ 2π/2 = π
        have h2 : (2 : ℝ) ≤ 2^(k+2) := by
          have h : 2 ≤ k + 2 := by omega
          have step : (2 ^ 2 : ℕ) ≤ 2 ^ (k+2) := Nat.pow_le_pow_right (by norm_num) h
          have : (4 : ℝ) ≤ 2 ^ (k+2) := by
            norm_cast
          linarith
        calc θ = 2 * π / 2^(k+2) := rfl
             _ ≤ 2 * π / 2 := by
               apply div_le_div_of_nonneg_left
               · apply mul_nonneg; norm_num; exact Real.pi_pos.le
               · norm_num
               · exact h2
             _ = π := by ring

      -- Step 3: Show that (omega_exact (k+2)).re = cos(θ)
      have w_re_eq : (omega_exact (k+2)).re = Real.cos θ := by
        rw [ih]
        -- (exp(2πi/2^(k+2))).re = cos(2π/2^(k+2)) = cos(θ)
        have eq : (2 * ↑π * I / ↑(2 ^ (k + 2)) : ℂ) = ↑θ * I := by
          simp only [θ]
          push_cast
          ring
        rw [eq, Complex.exp_mul_I]
        simp only [Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re, Complex.sin_ofReal_im,
                   Complex.I_re, Complex.I_im, mul_zero]
        ring

      -- Step 4: Simplify goal - omega_exact (k+3) is defined as the let binding
      show omega_exact (k+3) = Complex.exp (2 * π * Complex.I / (2^(k+3) : ℂ))
      rw [omega_exact]

      -- Now goal is: ⟨√((1 + (omega_exact (k+2)).re)/2), √((1 - (omega_exact (k+2)).re)/2)⟩ = exp(2πi/2^(k+3))
      -- Apply half-angle formula: exp(θ*I/2) = ⟨√((1 + cos θ)/2), √((1 - cos θ)/2)⟩
      have half_angle := exp_half_from_half_angle θ h_lower h_upper

      rw [w_re_eq, ← half_angle]

      -- Step 5: Show θ*I/2 = 2πi/2^(k+3)
      congr 1
      -- θ * I / 2 = (2π/2^(k+2)) * I / 2 = 2π * I / 2^(k+3)
      simp only [θ]
      have : (2 : ℂ) ^ (k+3) = 2 * (2 : ℂ) ^ (k+2) := by
        rw [pow_succ]; ring
      rw [this]
      push_cast
      ring

/-- If ω_N = exp(2πi/N), then ω_{2N} = exp(2πi/2N) using half-angle formula -/
theorem omega_exact_succ (k : ℕ) :
    omega_exact (k+1) = Complex.exp (2 * π * Complex.I / (2^(k+1) : ℂ)) := by
  exact omega_exact_eq_exp (k+1)

end IntervalComplex
