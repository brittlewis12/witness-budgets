import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Bitwise Operations for Dyadic Arithmetic

This module provides extraction-safe bitwise operations that work correctly
in both Lean and C. The key insight is that C's integer division truncates
toward zero, while we need floor (toward -∞) and ceiling (toward +∞).

These operations are the "trusted kernel" - ugly but small and verified once.
-/
namespace BitwiseOps

/-- Safe arithmetic shift right that rounds towards -∞ for all numbers.
    This is extraction-safe: produces correct results in both Lean and C.

    Background: Lean's Int.div rounds toward -∞ (Euclidean division), but
    C/C++'s `/` rounds toward 0 (truncation). For negative numbers:
    - Lean: -5 / 2 = -3 (correct floor)
    - C:    -5 / 2 = -2 (wrong, rounds up)

    This function uses only operations that behave identically in Lean and C. -/
def shiftRightFloor (n : ℤ) (shift : ℕ) : ℤ :=
  if shift = 0 then n
  else
    let divisor := (2 ^ shift : ℤ)
    if n ≥ 0 then
      n / divisor  -- Positive: truncation = floor
    else
      -- Negative: C truncates toward 0, but we need floor (toward -∞)
      -- If there's a remainder, we need to subtract 1
      if n % divisor = 0 then
        n / divisor
      else
        (n / divisor) - 1

/-- Safe shift that rounds towards +∞ (ceiling).
    Extraction-safe: produces correct results in both Lean and C.

    For ceiling, we need:
    - Positive n: round UP if remainder (add 1)
    - Negative n: Lean's ediv rounds toward -∞ (floor), so we need to add 1 if remainder -/
def shiftRightCeil (n : ℤ) (shift : ℕ) : ℤ :=
  if shift = 0 then n
  else
    let divisor := (2 ^ shift : ℤ)
    if n % divisor = 0 then
      n / divisor  -- Exact division: floor = ceiling
    else
      (n / divisor) + 1  -- Has remainder: ceiling = floor + 1

/-! ## Shift function properties -/

/-- shiftRightFloor produces a value ≤ n / 2^shift
    The property is: floor(n/2^k) ≤ n/2^k, which is definitionally true for floor. -/
theorem shiftRightFloor_le (n : ℤ) (shift : ℕ) :
    (shiftRightFloor n shift : ℚ) ≤ (n : ℚ) / (2^shift : ℚ) := by
  simp only [shiftRightFloor]
  by_cases h0 : shift = 0
  · simp [h0]
  · simp only [if_neg h0]
    have h2k_pos : (2^shift : ℤ) > 0 := by positivity
    have h2k_ne : (2^shift : ℤ) ≠ 0 := ne_of_gt h2k_pos
    have h2k_pos_q : (0 : ℚ) < (2^shift : ℤ) := by positivity
    by_cases hn : n ≥ 0
    · -- n ≥ 0: integer division rounds down, so n/d * d ≤ n
      simp only [if_pos hn]
      have key : (n / (2^shift : ℤ)) * (2^shift : ℤ) ≤ n := Int.ediv_mul_le n h2k_ne
      have h2k_q_ne : ((2^shift : ℤ) : ℚ) ≠ 0 := by positivity
      have step1 : ((n / (2^shift : ℤ) : ℤ) : ℚ) * ((2^shift : ℤ) : ℚ) ≤ (n : ℚ) := by
        rw [← Int.cast_mul]; exact Int.cast_le.mpr key
      have heq : ((n / (2^shift : ℤ) : ℤ) : ℚ) = ((n / (2^shift : ℤ) : ℤ) : ℚ) * ((2^shift : ℤ) : ℚ) / ((2^shift : ℤ) : ℚ) := by
        field_simp
      calc ((n / (2^shift : ℤ) : ℤ) : ℚ)
          = ((n / (2^shift : ℤ) : ℤ) : ℚ) * ((2^shift : ℤ) : ℚ) / ((2^shift : ℤ) : ℚ) := heq
        _ ≤ (n : ℚ) / ((2^shift : ℤ) : ℚ) := by
            apply div_le_div_of_nonneg_right step1 (by positivity)
        _ = (n : ℚ) / (2^shift : ℚ) := by simp only [Int.cast_pow, Int.cast_ofNat]
    · -- n < 0
      simp only [if_neg hn]
      by_cases hrem : n % (2^shift : ℤ) = 0
      · -- no remainder: exact division, n = (n/d) * d
        simp only [if_pos hrem]
        have hdvd : (2^shift : ℤ) ∣ n := Int.dvd_of_emod_eq_zero hrem
        have h2k_q_ne : ((2^shift : ℤ) : ℚ) ≠ 0 := by positivity
        rw [Int.cast_div hdvd h2k_q_ne]
        simp only [Int.cast_pow, Int.cast_ofNat, le_refl]
      · -- has remainder: we subtract 1
        simp only [if_neg hrem]
        have emod_nonneg : 0 ≤ n % (2^shift : ℤ) := Int.emod_nonneg n h2k_ne
        have emod_lt : n % (2^shift : ℤ) < (2^shift : ℤ) := Int.emod_lt_of_pos n h2k_pos
        have div_formula := Int.emod_add_mul_ediv n (2^shift : ℤ)
        have emod_pos : 0 < n % (2^shift : ℤ) := (emod_nonneg.lt_or_eq).resolve_right (Ne.symm hrem)
        have key : ((n / (2^shift : ℤ)) - 1) * (2^shift : ℤ) ≤ n := by
          have h1 : n = n % (2^shift : ℤ) + (2^shift : ℤ) * (n / (2^shift : ℤ)) := div_formula.symm
          have h2 : (n / (2^shift : ℤ) - 1) * (2^shift : ℤ) = (2^shift : ℤ) * (n / (2^shift : ℤ)) - (2^shift : ℤ) := by
            rw [Int.sub_mul]; ring
          linarith
        have step1 : (((n / (2^shift : ℤ)) - 1 : ℤ) : ℚ) * ((2^shift : ℤ) : ℚ) ≤ (n : ℚ) := by
          rw [← Int.cast_mul]; exact Int.cast_le.mpr key
        simp only [Int.cast_sub, Int.cast_one]
        have h2k_q_ne : ((2^shift : ℤ) : ℚ) ≠ 0 := by positivity
        have heq : ((n / (2^shift : ℤ) : ℤ) : ℚ) - 1 = (((n / (2^shift : ℤ)) - 1 : ℤ) : ℚ) * ((2^shift : ℤ) : ℚ) / ((2^shift : ℤ) : ℚ) := by
          simp only [Int.cast_sub, Int.cast_one]; field_simp
        calc ((n / (2^shift : ℤ) : ℤ) : ℚ) - 1
            = (((n / (2^shift : ℤ)) - 1 : ℤ) : ℚ) * ((2^shift : ℤ) : ℚ) / ((2^shift : ℤ) : ℚ) := heq
          _ ≤ (n : ℚ) / ((2^shift : ℤ) : ℚ) := by
              apply div_le_div_of_nonneg_right step1 (by positivity)
          _ = (n : ℚ) / (2^shift : ℚ) := by simp only [Int.cast_pow, Int.cast_ofNat]

/-- n / 2^shift ≤ shiftRightCeil
    The property is: n/2^k ≤ ceil(n/2^k), which is definitionally true for ceil. -/
theorem le_shiftRightCeil (n : ℤ) (shift : ℕ) :
    (n : ℚ) / (2^shift : ℚ) ≤ (shiftRightCeil n shift : ℚ) := by
  simp only [shiftRightCeil]
  by_cases h0 : shift = 0
  · simp [h0]
  · simp only [if_neg h0]
    have h2k_pos : (2^shift : ℤ) > 0 := by positivity
    have h2k_ne : (2^shift : ℤ) ≠ 0 := ne_of_gt h2k_pos
    by_cases hrem : n % (2^shift : ℤ) = 0
    · -- Exact division: floor = ceiling
      simp only [if_pos hrem]
      have hdvd : (2^shift : ℤ) ∣ n := Int.dvd_of_emod_eq_zero hrem
      have h2k_q_ne : ((2^shift : ℤ) : ℚ) ≠ 0 := by positivity
      rw [Int.cast_div hdvd h2k_q_ne]
      simp only [Int.cast_pow, Int.cast_ofNat, le_refl]
    · -- Has remainder: ceiling = floor + 1
      simp only [if_neg hrem]
      have emod_nonneg : 0 ≤ n % (2^shift : ℤ) := Int.emod_nonneg n h2k_ne
      have emod_lt : n % (2^shift : ℤ) < (2^shift : ℤ) := Int.emod_lt_of_pos n h2k_pos
      have div_formula := Int.emod_add_mul_ediv n (2^shift : ℤ)
      have emod_pos : 0 < n % (2^shift : ℤ) := (emod_nonneg.lt_or_eq).resolve_right (Ne.symm hrem)
      have key : n < ((n / (2^shift : ℤ)) + 1) * (2^shift : ℤ) := by
        have h1 : n = n % (2^shift : ℤ) + (2^shift : ℤ) * (n / (2^shift : ℤ)) := div_formula.symm
        have h2 : (n / (2^shift : ℤ) + 1) * (2^shift : ℤ) = (2^shift : ℤ) * (n / (2^shift : ℤ)) + (2^shift : ℤ) := by
          rw [Int.add_mul]; ring
        linarith
      have step1 : (n : ℚ) < (((n / (2^shift : ℤ)) + 1 : ℤ) : ℚ) * ((2^shift : ℤ) : ℚ) := by
        rw [← Int.cast_mul]; exact Int.cast_lt.mpr key
      simp only [Int.cast_add, Int.cast_one]
      have h2k_q_ne : ((2^shift : ℤ) : ℚ) ≠ 0 := by positivity
      have heq : ((n / (2^shift : ℤ) : ℤ) : ℚ) + 1 = (((n / (2^shift : ℤ)) + 1 : ℤ) : ℚ) * ((2^shift : ℤ) : ℚ) / ((2^shift : ℤ) : ℚ) := by
        simp only [Int.cast_add, Int.cast_one]; field_simp
      have hlt : (n : ℚ) / (2^shift : ℚ) < ((n / (2^shift : ℤ) : ℤ) : ℚ) + 1 := by
        calc (n : ℚ) / (2^shift : ℚ)
            = (n : ℚ) / ((2^shift : ℤ) : ℚ) := by simp only [Int.cast_pow, Int.cast_ofNat]
          _ < (((n / (2^shift : ℤ)) + 1 : ℤ) : ℚ) * ((2^shift : ℤ) : ℚ) / ((2^shift : ℤ) : ℚ) := by
              apply div_lt_div_of_pos_right step1 (by positivity)
          _ = ((n / (2^shift : ℤ) : ℤ) : ℚ) + 1 := heq.symm
      exact le_of_lt hlt

/-- Floor is always at most ceiling -/
theorem shiftRightFloor_le_shiftRightCeil (n : ℤ) (shift : ℕ) :
    shiftRightFloor n shift ≤ shiftRightCeil n shift := by
  have h := le_shiftRightCeil n shift
  have h' := shiftRightFloor_le n shift
  exact Int.cast_le.mp (le_trans h' h)

/-- Shift difference bound: ceil - floor ≤ 2 -/
theorem shiftRightCeil_sub_floor_le (n : ℤ) (shift : ℕ) :
    shiftRightCeil n shift - shiftRightFloor n shift ≤ 2 := by
  unfold shiftRightCeil shiftRightFloor
  by_cases h0 : shift = 0
  · simp [h0]
  · simp only [if_neg h0]
    by_cases hrem : n % (2 ^ shift : ℤ) = 0
    · simp [hrem]
    · simp only [if_neg hrem]
      by_cases hn : n ≥ 0
      · simp only [if_pos hn]; omega
      · simp only [if_neg hn]; omega

end BitwiseOps
