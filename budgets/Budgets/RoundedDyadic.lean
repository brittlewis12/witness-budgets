import Budgets.DyadicCanonical
import Budgets.BitwiseOps
import Mathlib.Data.Real.Basic

/-!
# Rounded Dyadic Operations

This module provides precision-controlled rounding for dyadic rationals.
It hides the bitwise details and exposes clean floor/ceiling operations.

Contract: floor(x) ≤ x ≤ ceil(x)
-/

namespace RoundedDyadic

open DyadicCanonical BitwiseOps

/-- Round dyadic DOWN (towards -∞) to specified precision -/
def floor (d : D) (precision : ℕ) : D :=
  if d.exp ≤ precision then
    d  -- Already within precision
  else
    -- Shift right, rounding down (toward -∞)
    let excessBits := d.exp - precision
    let shifted := shiftRightFloor d.num excessBits
    normalize shifted precision

/-- Round dyadic UP (towards +∞) to specified precision -/
def ceil (d : D) (precision : ℕ) : D :=
  if d.exp ≤ precision then
    d  -- Already within precision
  else
    -- Shift right, rounding up (toward +∞)
    let excessBits := d.exp - precision
    let shifted := shiftRightCeil d.num excessBits
    normalize shifted precision

/-! ## Core guarantees -/

/-- Floor rounding preserves or decreases value -/
theorem floor_le (d : D) (p : ℕ) : toRat (floor d p) ≤ toRat d := by
  unfold floor
  split_ifs with h
  · rfl
  · -- Need to round down using shiftRightFloor
    rw [DyadicCanonical.normalize_eq]
    simp only [toRat]
    have h2p_pos : (0 : ℚ) < 2^p := by positivity
    have hlt : p < d.exp := Nat.lt_of_not_le h
    have hexp : d.exp - p + p = d.exp := Nat.sub_add_cancel (le_of_lt hlt)
    -- Use shiftRightFloor_le lemma
    have hshift := shiftRightFloor_le d.num (d.exp - p)
    calc (shiftRightFloor d.num (d.exp - p) : ℚ) / 2^p
        ≤ ((d.num : ℚ) / 2^(d.exp - p)) / 2^p := by
            exact div_le_div_of_nonneg_right hshift (le_of_lt h2p_pos)
      _ = (d.num : ℚ) / (2^(d.exp - p) * 2^p) := by rw [div_div]
      _ = (d.num : ℚ) / 2^d.exp := by rw [← pow_add, hexp]

/-- Ceiling rounding preserves or increases value -/
theorem le_ceil (d : D) (p : ℕ) : toRat d ≤ toRat (ceil d p) := by
  unfold ceil
  split_ifs with h
  · rfl
  · -- Need to round up using shiftRightCeil
    rw [DyadicCanonical.normalize_eq]
    simp only [toRat]
    have h2p_pos : (0 : ℚ) < 2^p := by positivity
    have hlt : p < d.exp := Nat.lt_of_not_le h
    have hexp : d.exp - p + p = d.exp := Nat.sub_add_cancel (le_of_lt hlt)
    -- Use le_shiftRightCeil lemma
    have hshift := le_shiftRightCeil d.num (d.exp - p)
    calc (d.num : ℚ) / 2^d.exp
        = (d.num : ℚ) / (2^(d.exp - p) * 2^p) := by rw [← pow_add, hexp]
      _ = ((d.num : ℚ) / 2^(d.exp - p)) / 2^p := by rw [div_div]
      _ ≤ (shiftRightCeil d.num (d.exp - p) : ℚ) / 2^p := by
            exact div_le_div_of_nonneg_right hshift (le_of_lt h2p_pos)

/-- Floor is at most ceiling -/
theorem floor_le_ceil (d : D) (p : ℕ) : toRat (floor d p) ≤ toRat (ceil d p) := by
  calc toRat (floor d p)
      ≤ toRat d := floor_le d p
    _ ≤ toRat (ceil d p) := le_ceil d p

/-- Rounding error is bounded by precision -/
theorem roundingError_bounded (d : D) (p : ℕ) :
    abs ((toRat (ceil d p) : ℝ) - (toRat (floor d p) : ℝ)) ≤ 2 / (2^p : ℝ) := by
  -- The gap between floor and ceil is at most 2 ULPs
  unfold floor ceil
  split_ifs with h
  · -- d.exp ≤ p: no rounding needed, floor = ceil = d
    simp only [sub_self, abs_zero]
    apply div_nonneg
    · norm_num
    · apply pow_nonneg; norm_num
  · -- d.exp > p: rounding happens
    rw [DyadicCanonical.normalize_eq, DyadicCanonical.normalize_eq]
    have h2p_pos_r : (0 : ℝ) < 2^p := by positivity
    -- shift_bound: ceil - floor ≤ 2
    have shift_bound : shiftRightCeil d.num (d.exp - p) - shiftRightFloor d.num (d.exp - p) ≤ 2 :=
      shiftRightCeil_sub_floor_le d.num (d.exp - p)
    -- floor ≤ ceil
    have hcf : shiftRightFloor d.num (d.exp - p) ≤ shiftRightCeil d.num (d.exp - p) :=
      shiftRightFloor_le_shiftRightCeil d.num (d.exp - p)
    -- Work in rationals first
    have key_q : ((shiftRightCeil d.num (d.exp - p) : ℤ) : ℚ) / (2^p : ℚ) -
                 ((shiftRightFloor d.num (d.exp - p) : ℤ) : ℚ) / (2^p : ℚ) ≤ 2 / (2^p : ℚ) := by
      rw [← sub_div]
      apply div_le_div_of_nonneg_right _ (le_of_lt (by positivity : (0 : ℚ) < 2^p))
      simp only [← Int.cast_sub]
      exact_mod_cast shift_bound
    -- Nonnegative since ceil ≥ floor
    have diff_nonneg_q : (0 : ℚ) ≤ ((shiftRightCeil d.num (d.exp - p) : ℤ) : ℚ) / (2^p : ℚ) -
                                   ((shiftRightFloor d.num (d.exp - p) : ℤ) : ℚ) / (2^p : ℚ) := by
      rw [← sub_div]
      apply div_nonneg _ (by positivity)
      simp only [← Int.cast_sub]
      exact Int.cast_nonneg.mpr (Int.sub_nonneg_of_le hcf)
    -- Convert to reals
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat]
    have diff_nonneg_r : (0 : ℝ) ≤ (shiftRightCeil d.num (d.exp - p) : ℝ) / (2^p : ℝ) -
                                   (shiftRightFloor d.num (d.exp - p) : ℝ) / (2^p : ℝ) := by
      have := diff_nonneg_q
      simp only at this ⊢
      exact_mod_cast this
    rw [abs_of_nonneg diff_nonneg_r, ← sub_div]
    apply div_le_div_of_nonneg_right _ (le_of_lt h2p_pos_r)
    simp only [← Int.cast_sub]
    exact_mod_cast shift_bound

/-- Helper: after rounding, floor ≤ ceil preserves order -/
theorem floor_ceil_preserves_order {a b : D} {p : ℕ} (h : toRat a ≤ toRat b) :
    toRat (floor a p) ≤ toRat (ceil b p) := by
  calc toRat (floor a p)
      ≤ toRat a := floor_le a p
    _ ≤ toRat b := h
    _ ≤ toRat (ceil b p) := le_ceil b p

end RoundedDyadic
