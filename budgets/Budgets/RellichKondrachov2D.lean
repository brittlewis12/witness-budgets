/-
Main Soundness Theorem for 2D Rellich-Kondrachov Compactness

This file proves the constructive witness existence theorem for the
Quantitative Rellich-Kondrachov (QRK) embedding on the 2D torus.

Key results:
- gridFinset_sound_2D: Main soundness theorem
- Dimension-free tail bound
- Conservative mesh formulas for 2D
-/

import Budgets.RellichKondrachov2D.Seq
import Mathlib.Analysis.Real.Pi.Bounds

open scoped BigOperators ComplexConjugate Real

namespace RellichKondrachov2D.Seq
open ℓ2Z2

/-! ## Helper Lemmas for Soundness Theorem -/

/-- M_of is positive (key for positivity of M in tail bound) -/
lemma M_of_pos (ε R : ℚ) (_hε : 0 < ε) (_hR : 0 < R) : 0 < M_of ε R := by
  unfold M_of
  omega

/-- Tail bound holds with M_of choice.
    Key insight: This bound is dimension-free (identical to the 1D case). -/
lemma tail_bound_M_of_2D {ε R : ℚ} (hε : 0 < (ε : ℝ)) (hR : 0 < (R : ℝ)) :
    (R : ℝ)^2 / (4 * Real.pi^2 * (M_of ε R : ℝ)^2) ≤ ((ε : ℝ) / 2)^2 := by
  set M := M_of ε R with hM_def

  -- Rational positivity (for ℚ arithmetic)
  have ε_pos_rat : 0 < ε := Rat.cast_pos.mp hε
  have R_pos_rat : 0 < R := Rat.cast_pos.mp hR
  have pi_lb_pos : 0 < pi_rat_lb := by norm_num [pi_rat_lb]

  -- Key: M > R/(pi_rat_lb * ε) in ℚ
  have hM_ge_rat : (M : ℚ) > R / (pi_rat_lb * ε) := by
    have h1 : (⌈R / (pi_rat_lb * ε)⌉₊ : ℚ) ≥ R / (pi_rat_lb * ε) := Nat.le_ceil (R / (pi_rat_lb * ε))
    calc (M : ℚ)
        = (⌈R / (pi_rat_lb * ε)⌉₊ + 1 : ℕ) := by simp [M, M_of]
      _ = (⌈R / (pi_rat_lb * ε)⌉₊ : ℚ) + 1 := by norm_cast
      _ > R / (pi_rat_lb * ε) := by linarith

  -- Convert to ℝ inequality
  have hM_ge : (M : ℝ) > (R : ℝ) / ((pi_rat_lb : ℝ) * (ε : ℝ)) := by
    calc (M : ℝ)
        = ((M : ℚ) : ℝ) := by norm_cast
      _ > ((R / (pi_rat_lb * ε)) : ℝ) := by exact_mod_cast hM_ge_rat
      _ = (R : ℝ) / ((pi_rat_lb : ℝ) * (ε : ℝ)) := by norm_cast

  -- Use pi > pi_rat_lb = 3
  have pi_lb : (pi_rat_lb : ℝ) ≤ Real.pi := by
    -- π ≈ 3.14159... ≥ 3
    show (3 : ℝ) ≤ Real.pi
    -- Use the fact that π > 3
    exact le_of_lt Real.pi_gt_three

  -- Strengthen bound using pi > pi_rat_lb
  have hM_pi : (M : ℝ) > (R : ℝ) / (Real.pi * (ε : ℝ)) := by
    calc (M : ℝ)
        > (R : ℝ) / ((pi_rat_lb : ℝ) * (ε : ℝ)) := hM_ge
      _ ≥ (R : ℝ) / (Real.pi * (ε : ℝ)) := by
          apply div_le_div_of_nonneg_left (by linarith)
          · positivity
          · exact mul_le_mul_of_nonneg_right pi_lb (by linarith)

  -- M > R/(π·ε) ⟹ 2π·M > 2R/ε ⟹ (2π·M)² > 4R²/ε²
  have hM_scaled : 2 * Real.pi * (M : ℝ) > 2 * (R : ℝ) / (ε : ℝ) := by
    have h1 : (M : ℝ) > (R : ℝ) / (Real.pi * (ε : ℝ)) := hM_pi
    have h2 : Real.pi * (ε : ℝ) * (M : ℝ) > (R : ℝ) := by
      calc Real.pi * (ε : ℝ) * (M : ℝ)
          = (Real.pi * (ε : ℝ)) * (M : ℝ) := by ring
        _ > (Real.pi * (ε : ℝ)) * ((R : ℝ) / (Real.pi * (ε : ℝ))) := by
            apply mul_lt_mul_of_pos_left h1 (by positivity)
        _ = (R : ℝ) := by field_simp
    calc 2 * Real.pi * (M : ℝ)
        = 2 * (Real.pi * (M : ℝ)) := by ring
      _ > 2 * ((R : ℝ) / (ε : ℝ)) := by
          apply mul_lt_mul_of_pos_left _ (by norm_num)
          calc Real.pi * (M : ℝ)
              = (Real.pi * (ε : ℝ) * (M : ℝ)) / (ε : ℝ) := by field_simp
            _ > (R : ℝ) / (ε : ℝ) := by exact div_lt_div_of_pos_right h2 hε
      _ = 2 * (R : ℝ) / (ε : ℝ) := by ring

  -- Therefore R²/(4π²M²) < (ε/2)²
  have tail_bd : (R : ℝ)^2 / (4 * Real.pi^2 * (M : ℝ)^2) < ((ε : ℝ) / 2)^2 := by
    -- Rewrite denominator: 4·π²·M² = (2·π·M)²
    have denom_eq : 4 * Real.pi^2 * (M : ℝ)^2 = (2 * Real.pi * (M : ℝ))^2 := by ring
    rw [denom_eq]
    -- Now continue with original proof
    calc (R : ℝ)^2 / ((2 * Real.pi * (M : ℝ))^2)
        < (R : ℝ)^2 / ((2 * (R : ℝ) / (ε : ℝ))^2) := by
          apply div_lt_div_of_pos_left
          · exact sq_pos_of_pos hR
          · exact sq_pos_of_pos (by positivity)
          · have h_neg : -(2 * Real.pi * (M : ℝ)) < 2 * (R : ℝ) / (ε : ℝ) := by
              have hM_pos : 0 < (M : ℝ) := by
                exact_mod_cast M_of_pos ε R (Rat.cast_pos.mp hε) (Rat.cast_pos.mp hR)
              have h1 : 0 < 2 * Real.pi * (M : ℝ) := by
                apply mul_pos; apply mul_pos; norm_num; exact Real.pi_pos; exact hM_pos
              have h2 : 0 < 2 * (R : ℝ) / (ε : ℝ) := by positivity
              linarith
            exact sq_lt_sq' h_neg hM_scaled
      _ = (R : ℝ)^2 / (4 * (R : ℝ)^2 / (ε : ℝ)^2) := by congr 1; ring
      _ = ((ε : ℝ) / 2)^2 := by field_simp; ring
  exact le_of_lt tail_bd

/-- Rounding error bound for inside region
    KEY DIFFERENCE from 1D: (2M+1)² instead of 2M -/
lemma rounding_bound_mesh_2D (ε : ℚ) (M : ℕ) :
    ((2 * M + 1)^2 : ℝ) * (2 * ((mesh2D ε M : ℝ))^2) ≤ ((ε : ℝ) / 2)^2 := by
  unfold mesh2D
  -- Expand and simplify: (2M+1)² * 2 * (ε/(4(2M+1)))² = (ε/2)²
  calc ((2 * M + 1)^2 : ℝ) * (2 * ((ε / (4 * (2 * M + 1)) : ℚ) : ℝ)^2)
      = ((2 * M + 1 : ℕ) : ℝ)^2 * (2 * ((ε : ℝ) / (4 * ((2 * M + 1 : ℕ) : ℝ)))^2) := by
        push_cast; ring
    _ = ((2 * M + 1 : ℕ) : ℝ)^2 * (2 * (ε : ℝ)^2 / (16 * ((2 * M + 1 : ℕ) : ℝ)^2)) := by
        congr 1
        field_simp
        ring
    _ = ((2 * M + 1 : ℕ) : ℝ)^2 * ((ε : ℝ)^2 / (8 * ((2 * M + 1 : ℕ) : ℝ)^2)) := by
        ring
    _ = (ε : ℝ)^2 / 8 := by
        field_simp
    _ ≤ (ε : ℝ)^2 / 4 := by
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by norm_num)
    _ = ((ε : ℝ) / 2)^2 := by ring

/-- Coefficient bound from H¹ norm for 2D (adapts 1D lemma) -/
lemma coeff_bound_from_H1_2D {x : ℓ2Z2} {R : ℝ} (_hR : 0 < R) (hx : x.InH1Ball R)
    (k : ℤ × ℤ) (_hk : k ≠ (0, 0)) :
    ‖x.a k‖^2 ≤ R^2 := by
  have h_weight : 1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2) > 0 := by
    linarith [sq_nonneg (2 * Real.pi * (k.1 : ℝ)), sq_nonneg (2 * Real.pi * (k.2 : ℝ))]
  have bound := hx.h1_bound {k}
  simp only [Finset.sum_singleton] at bound
  have h1 : (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖x.a k‖^2 ≤ R^2 := bound
  have h2 : ‖x.a k‖^2 * (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) ≤ R^2 := by
    rwa [mul_comm] at h1
  have h3 : ‖x.a k‖^2 * 1 ≤ ‖x.a k‖^2 * (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) := by
    apply mul_le_mul_of_nonneg_left
    · have : 0 ≤ 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2) := by positivity
      linarith
    · exact sq_nonneg _
  calc ‖x.a k‖^2
      = ‖x.a k‖^2 * 1 := by ring
    _ ≤ ‖x.a k‖^2 * (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) := h3
    _ ≤ R^2 := h2

/-- Rounded coefficient is in box (key geometric lemma for 2D) -/
lemma rounded_in_box_2D {ε R : ℚ} {M : ℕ} {k : ℤ × ℤ} {c : ℂ}
    (hε : 0 < (ε : ℝ)) (hR : 0 < (R : ℝ)) (hk : k ≠ (0, 0))
    (hc : ‖c‖^2 ≤ (R : ℝ)^2) :
    roundCoeff (mesh2D ε M) c ∈ coeffBox ε R M k := by
  simp only [coeffBox, roundCoeff, Finset.mem_product, Finset.mem_Icc]
  let δ := mesh2D ε M
  let bound := coeffBound R k
  let rad := Nat.ceil (bound / δ) + 1

  have hδ : 0 < (δ : ℝ) := mesh2D_pos ε M (by exact_mod_cast hε : 0 < ε)
  have hbound : 0 ≤ (bound : ℝ) := by
    unfold bound coeffBound
    split_ifs
    · norm_num
    · exact_mod_cast le_of_lt hR
  have bound_eq_R : (bound : ℝ) = (R : ℝ) := by simp [bound, coeffBound, hk]

  -- Each component of c has magnitude ≤ ‖c‖ ≤ R
  have hc_norm : ‖c‖ ≤ (R : ℝ) := by
    calc ‖c‖
        = Real.sqrt (‖c‖^2) := by rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt ((R : ℝ)^2) := Real.sqrt_le_sqrt hc
      _ = (R : ℝ) := by rw [Real.sqrt_sq (by positivity)]
  have c_re_bound : |c.re| ≤ (R : ℝ) := by
    calc |c.re|
        ≤ ‖c‖ := Complex.abs_re_le_norm c
      _ ≤ (R : ℝ) := hc_norm
  have c_im_bound : |c.im| ≤ (R : ℝ) := by
    calc |c.im|
        ≤ ‖c‖ := Complex.abs_im_le_norm c
      _ ≤ (R : ℝ) := hc_norm

  -- Rounded coordinates satisfy bounds
  have rad_ge : (rad : ℝ) > (R : ℝ) / (δ : ℝ) := by
    calc (rad : ℝ)
        = ((Nat.ceil (bound / δ) + 1) : ℝ) := by unfold rad; norm_cast
      _ ≥ (bound / δ : ℚ) + 1 := by
          have : ((Nat.ceil (bound / δ)) : ℝ) ≥ (bound / δ : ℚ) := by
            exact_mod_cast Nat.le_ceil (bound / δ)
          linarith
      _ = (bound : ℝ) / (δ : ℝ) + 1 := by push_cast; ring
      _ = (R : ℝ) / (δ : ℝ) + 1 := by rw [bound_eq_R]
      _ > (R : ℝ) / (δ : ℝ) := by linarith

  constructor
  · -- Real part bound
    have : |c.re / (δ : ℝ)| ≤ (R : ℝ) / (δ : ℝ) := by
      rw [abs_div c.re (δ : ℝ)]
      have : |(δ : ℝ)| = (δ : ℝ) := abs_of_pos hδ
      rw [this]
      exact div_le_div_of_nonneg_right c_re_bound (le_of_lt hδ)
    constructor
    · -- Show -rad ≤ floor(c.re / δ)
      have rad_strong : (rad : ℝ) ≥ (R : ℝ) / (δ : ℝ) + 1 := by
        calc (rad : ℝ)
            = ((Nat.ceil (bound / δ) + 1) : ℝ) := by unfold rad; norm_cast
          _ ≥ (bound / δ : ℚ) + 1 := by
              have : ((Nat.ceil (bound / δ)) : ℝ) ≥ (bound / δ : ℚ) := by
                exact_mod_cast Nat.le_ceil (bound / δ)
              linarith
          _ = (bound : ℝ) / (δ : ℝ) + 1 := by push_cast; ring
          _ = (R : ℝ) / (δ : ℝ) + 1 := by rw [bound_eq_R]
      have h_abs : -(R : ℝ) / (δ : ℝ) ≤ c.re / (δ : ℝ) := by
        have h1 : -(|c.re / (δ : ℝ)|) ≤ c.re / (δ : ℝ) := neg_abs_le _
        have h2 : -((R : ℝ) / (δ : ℝ)) ≤ -(|c.re / (δ : ℝ)|) := by
          apply neg_le_neg
          exact this
        show -(R : ℝ) / (δ : ℝ) ≤ c.re / (δ : ℝ)
        calc -(R : ℝ) / (δ : ℝ)
            = -((R : ℝ) / (δ : ℝ)) := by ring
          _ ≤ -(|c.re / (δ : ℝ)|) := h2
          _ ≤ c.re / (δ : ℝ) := h1
      have h_chain : ((-rad : ℤ) : ℝ) ≤ c.re / (δ : ℝ) := by
        have : ((-rad : ℤ) : ℝ) = -(rad : ℝ) := by simp
        rw [this]
        calc -(rad : ℝ)
            ≤ -((R : ℝ) / (δ : ℝ) + 1) := by linarith [rad_strong]
          _ = -(R : ℝ) / (δ : ℝ) - 1 := by ring
          _ ≤ -(R : ℝ) / (δ : ℝ) := by linarith
          _ ≤ c.re / (δ : ℝ) := h_abs
      exact Int.le_floor.mpr h_chain
    · -- Show floor(c.re / δ) ≤ rad
      have h_upper : c.re / (δ : ℝ) ≤ (R : ℝ) / (δ : ℝ) := by
        linarith [le_abs_self (c.re / (δ : ℝ)), this]
      have h_lt : c.re / (δ : ℝ) < (rad : ℝ) := by linarith [h_upper, rad_ge]
      have floor_lt : ⌊c.re / (δ : ℝ)⌋ < (rad : ℤ) := by
        rw [Int.floor_lt]
        exact h_lt
      exact Int.le_of_lt_add_one (by omega : ⌊c.re / (δ : ℝ)⌋ < ↑rad + 1)
  · -- Imaginary part bound (symmetric)
    have : |c.im / (δ : ℝ)| ≤ (R : ℝ) / (δ : ℝ) := by
      rw [abs_div c.im (δ : ℝ)]
      have : |(δ : ℝ)| = (δ : ℝ) := abs_of_pos hδ
      rw [this]
      exact div_le_div_of_nonneg_right c_im_bound (le_of_lt hδ)
    constructor
    · -- Show -rad ≤ floor(c.im / δ)
      have rad_strong : (rad : ℝ) ≥ (R : ℝ) / (δ : ℝ) + 1 := by
        calc (rad : ℝ)
            = ((Nat.ceil (bound / δ) + 1) : ℝ) := by unfold rad; norm_cast
          _ ≥ (bound / δ : ℚ) + 1 := by
              have : ((Nat.ceil (bound / δ)) : ℝ) ≥ (bound / δ : ℚ) := by
                exact_mod_cast Nat.le_ceil (bound / δ)
              linarith
          _ = (bound : ℝ) / (δ : ℝ) + 1 := by push_cast; ring
          _ = (R : ℝ) / (δ : ℝ) + 1 := by rw [bound_eq_R]
      have h_abs : -(R : ℝ) / (δ : ℝ) ≤ c.im / (δ : ℝ) := by
        have h1 : -(|c.im / (δ : ℝ)|) ≤ c.im / (δ : ℝ) := neg_abs_le _
        have h2 : -((R : ℝ) / (δ : ℝ)) ≤ -(|c.im / (δ : ℝ)|) := by
          apply neg_le_neg
          exact this
        show -(R : ℝ) / (δ : ℝ) ≤ c.im / (δ : ℝ)
        calc -(R : ℝ) / (δ : ℝ)
            = -((R : ℝ) / (δ : ℝ)) := by ring
          _ ≤ -(|c.im / (δ : ℝ)|) := h2
          _ ≤ c.im / (δ : ℝ) := h1
      have h_chain : ((-rad : ℤ) : ℝ) ≤ c.im / (δ : ℝ) := by
        have : ((-rad : ℤ) : ℝ) = -(rad : ℝ) := by simp
        rw [this]
        calc -(rad : ℝ)
            ≤ -((R : ℝ) / (δ : ℝ) + 1) := by linarith [rad_strong]
          _ = -(R : ℝ) / (δ : ℝ) - 1 := by ring
          _ ≤ -(R : ℝ) / (δ : ℝ) := by linarith
          _ ≤ c.im / (δ : ℝ) := h_abs
      exact Int.le_floor.mpr h_chain
    · -- Show floor(c.im / δ) ≤ rad
      have h_upper : c.im / (δ : ℝ) ≤ (R : ℝ) / (δ : ℝ) := by
        linarith [le_abs_self (c.im / (δ : ℝ)), this]
      have h_lt : c.im / (δ : ℝ) < (rad : ℝ) := by linarith [h_upper, rad_ge]
      have floor_lt : ⌊c.im / (δ : ℝ)⌋ < (rad : ℤ) := by
        rw [Int.floor_lt]
        exact h_lt
      exact Int.le_of_lt_add_one (by omega : ⌊c.im / (δ : ℝ)⌋ < ↑rad + 1)

/-- Rounded grid point is in gridFinset (needs H¹ hypotheses) -/
lemma roundToGrid_mem_2D (ε R : ℚ) (M : ℕ) (x : ℓ2Z2) :
    roundToGrid2D ε R M x ∈ gridFinset2D ε R M := by
  classical
  refine Finset.mem_pi.mpr ?_
  intro k hk
  -- roundToGrid2D always returns a value in coeffBoxSubtype by construction
  simp only [coeffBoxSubtype]
  exact Finset.mem_attach _ _

/-- Rounding error bound (same as 1D, dimension-independent) -/
lemma round_error_2D (δ : ℚ) (hδ : 0 < (δ : ℝ)) (c : ℂ) :
    ‖c - ⟨(δ : ℝ) * (roundCoeff δ c).1, (δ : ℝ) * (roundCoeff δ c).2⟩‖
      ≤ Real.sqrt 2 * (δ : ℝ) := by
  simp only [roundCoeff]
  set n_re := Int.floor (c.re / (δ : ℝ))
  set n_im := Int.floor (c.im / (δ : ℝ))

  -- Error in each coordinate is at most δ
  have re_err : |c.re - (δ : ℝ) * n_re| ≤ (δ : ℝ) := by
    have h1 : c.re / (δ : ℝ) - 1 < n_re := Int.sub_one_lt_floor _
    have h2 : n_re ≤ c.re / (δ : ℝ) := Int.floor_le (c.re / (δ : ℝ))
    rw [abs_sub_le_iff]
    constructor
    · have eq1 : c.re - (δ : ℝ) * n_re = (δ : ℝ) * (c.re / (δ : ℝ) - n_re) := by field_simp
      rw [eq1]
      have bound : c.re / (δ : ℝ) - n_re < 1 := by linarith
      have : (δ : ℝ) * (c.re / (δ : ℝ) - n_re) < (δ : ℝ) * 1 := mul_lt_mul_of_pos_left bound hδ
      linarith
    · have eq1 : (δ : ℝ) * n_re - c.re = (δ : ℝ) * (n_re - c.re / (δ : ℝ)) := by field_simp
      rw [eq1]
      have bound : n_re - c.re / (δ : ℝ) ≤ 0 := by linarith
      have : (δ : ℝ) * (n_re - c.re / (δ : ℝ)) ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos (by linarith) bound
      linarith

  have im_err : |c.im - (δ : ℝ) * n_im| ≤ (δ : ℝ) := by
    have h1 : c.im / (δ : ℝ) - 1 < n_im := Int.sub_one_lt_floor _
    have h2 : n_im ≤ c.im / (δ : ℝ) := Int.floor_le (c.im / (δ : ℝ))
    rw [abs_sub_le_iff]
    constructor
    · have eq1 : c.im - (δ : ℝ) * n_im = (δ : ℝ) * (c.im / (δ : ℝ) - n_im) := by field_simp
      rw [eq1]
      have bound : c.im / (δ : ℝ) - n_im < 1 := by linarith
      have : (δ : ℝ) * (c.im / (δ : ℝ) - n_im) < (δ : ℝ) * 1 := mul_lt_mul_of_pos_left bound hδ
      linarith
    · have eq1 : (δ : ℝ) * n_im - c.im = (δ : ℝ) * (n_im - c.im / (δ : ℝ)) := by field_simp
      rw [eq1]
      have bound : n_im - c.im / (δ : ℝ) ≤ 0 := by linarith
      have : (δ : ℝ) * (n_im - c.im / (δ : ℝ)) ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos (by linarith) bound
      linarith

  -- Combined error via Pythagorean theorem
  have sum_bound : (c.re - (δ : ℝ) * n_re)^2 + (c.im - (δ : ℝ) * n_im)^2 ≤ 2 * (δ : ℝ)^2 := by
    have : (c.re - (δ : ℝ) * n_re)^2 ≤ (δ : ℝ)^2 := by
      calc (c.re - (δ : ℝ) * n_re)^2
          = |c.re - (δ : ℝ) * n_re|^2 := by rw [sq_abs]
        _ ≤ (δ : ℝ)^2 := by
            have h_neg : -(δ : ℝ) ≤ |c.re - (δ : ℝ) * n_re| := by
              linarith [abs_nonneg (c.re - (δ : ℝ) * n_re), hδ]
            exact sq_le_sq' h_neg re_err
    have : (c.im - (δ : ℝ) * n_im)^2 ≤ (δ : ℝ)^2 := by
      calc (c.im - (δ : ℝ) * n_im)^2
          = |c.im - (δ : ℝ) * n_im|^2 := by rw [sq_abs]
        _ ≤ (δ : ℝ)^2 := by
            have h_neg : -(δ : ℝ) ≤ |c.im - (δ : ℝ) * n_im| := by
              linarith [abs_nonneg (c.im - (δ : ℝ) * n_im), hδ]
            exact sq_le_sq' h_neg im_err
    linarith

  calc ‖c - ⟨(δ : ℝ) * n_re, (δ : ℝ) * n_im⟩‖
      = Real.sqrt ((c.re - (δ : ℝ) * n_re)^2 + (c.im - (δ : ℝ) * n_im)^2) := by
        -- Complex norm is sqrt of normSq, and normSq is sum of squares of components
        have h1 : ‖c - ⟨(δ : ℝ) * n_re, (δ : ℝ) * n_im⟩‖ = Real.sqrt (Complex.normSq (c - ⟨(δ : ℝ) * n_re, (δ : ℝ) * n_im⟩)) := rfl
        rw [h1, Complex.normSq_apply]
        simp [Complex.sub_re, Complex.sub_im]
        ring_nf
    _ ≤ Real.sqrt (2 * (δ : ℝ)^2) := Real.sqrt_le_sqrt sum_bound
    _ = Real.sqrt 2 * (δ : ℝ) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by linarith)]

/-! ## Main Soundness Theorem -/

/-- Helper: Convert a filtered finset to subtype finset for tail bound application -/
lemma tail_finset_convert {x : ℓ2Z2} (F : Finset (ℤ × ℤ)) (M : ℝ)
    (h : ∀ k ∈ F, M^2 < ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) :
    ∃ (G : Finset {k : ℤ × ℤ // M^2 < ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)}),
      Finset.sum G (fun g => ‖x.a g.val‖^2) = Finset.sum F (fun k => ‖x.a k‖^2) := by
  -- Use F.attach and map to subtype
  use F.attach.map ⟨fun ⟨k, hk⟩ => ⟨k, h k hk⟩, by
    intro ⟨k1, hk1⟩ ⟨k2, hk2⟩ heq
    simp only [Subtype.mk.injEq] at heq
    exact Subtype.ext heq⟩
  -- Prove sum equality
  rw [Finset.sum_map]
  conv_rhs => rw [← Finset.sum_attach]
  rfl

set_option maxHeartbeats 800000

/-- **Main soundness theorem for 2D**: Every mean-zero H¹-bounded sequence
    has an ε-close grid point (constructively proven via rounding).

    PROOF STRATEGY (mirrors 1D exactly):
    1. Choose M := M_of ε R to control tail error
    2. Define witness g := roundToGrid2D ε R M x
    3. Split error into tail + inside:
       - Tail (|k|² > M²): ≤ (ε/2)² using tail_bound_finitary_2D
       - Inside (|k|² ≤ M²): ≤ (ε/2)² using rounding error
    4. Total: (ε/2)² + (ε/2)² < ε²

    WITNESS STRUCTURE:
    - gridToSeq g is the C0 witness function
    - gridFinset2D is C5 (mathematical existence, not materialized)
    - The witness comes from roundToGrid2D (computable function)
-/
theorem gridFinset_sound_2D (ε R : ℚ) (hε : 0 < (ε : ℝ)) (hR : 0 < (R : ℝ))
    (x : ℓ2Z2) (hmean : x.meanZero) (hH1 : x.InH1Ball (R : ℝ)) :
    ∃ (g : GridPoint2D ε R (M_of ε R)),
      g ∈ gridFinset2D ε R (M_of ε R) ∧
      ∀ F : Finset (ℤ × ℤ),
        Finset.sum F (fun k => ‖x.a k - (gridToSeq ε R (M_of ε R) g).a k‖^2)
          < (ε : ℝ)^2 := by
  -- Step 1: Choose M using M_of to control tail error
  set M := M_of ε R with hMdef

  have hM : 0 < (M : ℝ) := by
    simpa [hMdef] using (Nat.cast_pos.mpr (M_of_pos ε R (Rat.cast_pos.mp hε) (Rat.cast_pos.mp hR)))

  have hM_ne : M ≠ 0 := by
    simpa [hMdef] using (Nat.pos_iff_ne_zero.mp (M_of_pos ε R (Rat.cast_pos.mp hε) (Rat.cast_pos.mp hR)))

  -- Step 2: Construct witness via rounding
  let g := roundToGrid2D ε R M x

  -- Step 3: Prove g ∈ gridFinset2D
  have g_in_grid : g ∈ gridFinset2D ε R M := by
    exact roundToGrid_mem_2D ε R M x

  use g, g_in_grid

  -- Step 4: Prove distance bound
  intro F

  -- Define center from grid point (evaluation in proof layer)
  let c := gridToSeq ε R M g

  -- Center evaluation lemmas
  have center_eq : ∀ k (hk : k ∈ IndexSet2D M),
      c.a k = ((g k hk).val.1 : ℂ) * ((mesh2D ε M : ℚ) : ℝ) +
              Complex.I * (((g k hk).val.2 : ℂ) * ((mesh2D ε M : ℚ) : ℝ)) := by
    intro k hk
    simp only [c, gridToSeq, dif_pos hk]

  have center_zero : ∀ k, k ∉ IndexSet2D M → c.a k = 0 := by
    intro k hk
    simp [c, gridToSeq, dif_neg hk]

  -- Split F into inside (IndexSet2D M) and outside
  let F_in := F.filter (fun k => k ∈ IndexSet2D M)
  let F_out := F.filter (fun k => k ∉ IndexSet2D M)

  -- Partition: F = F_in ∪ F_out
  have partition : F = F_in ∪ F_out := by
    ext k
    simp [F_in, F_out, Finset.mem_filter, Finset.mem_union]
    tauto

  have disj : Disjoint F_in F_out := by
    rw [Finset.disjoint_filter]
    intro k _ h1 h2
    exact h2 h1

  -- Split sum
  have sum_split :
      Finset.sum F (fun k => ‖x.a k - c.a k‖^2)
      = Finset.sum F_in (fun k => ‖x.a k - c.a k‖^2)
      + Finset.sum F_out (fun k => ‖x.a k - c.a k‖^2) := by
    rw [partition]
    exact Finset.sum_union disj

  -- INSIDE BOUND: Rounding error ≤ (ε/2)²
  have inside_bound :
      Finset.sum F_in (fun k => ‖x.a k - c.a k‖^2)
      ≤ ((ε : ℝ) / 2)^2 := by
    -- F_in ⊆ IndexSet2D M, so bound by sum over entire IndexSet2D M
    calc Finset.sum F_in (fun k => ‖x.a k - c.a k‖^2)
        ≤ Finset.sum (IndexSet2D M) (fun k => ‖x.a k - c.a k‖^2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            simp [F_in, Finset.mem_filter] at hk
            exact hk.2
          · intro k _ _
            exact sq_nonneg _
      _ ≤ Finset.sum (IndexSet2D M) (fun k => 2 * ((mesh2D ε M : ℚ) : ℝ)^2) := by
          apply Finset.sum_le_sum
          intro k hk
          -- Rewrite c.a k using center_eq
          have hk_mem : k ∈ IndexSet2D M := hk
          rw [center_eq k hk_mem]
          -- Apply rounding error bound
          -- Show rounded coefficient is in box
          have k_ne_zero : k ≠ (0, 0) := by
            rw [mem_IndexSet2D] at hk_mem
            exact hk_mem.2.2.2.2
          have coeff_bound : ‖x.a k‖^2 ≤ (R : ℝ)^2 := by
            by_cases hk_zero : k = (0, 0)
            · subst hk_zero
              rw [hmean]
              simp
              exact sq_nonneg _
            · exact coeff_bound_from_H1_2D hR hH1 k hk_zero
          have rounded_in : roundCoeff (mesh2D ε M) (x.a k) ∈ coeffBox ε R M k :=
            rounded_in_box_2D hε hR k_ne_zero coeff_bound
          have grid_eval : g k hk_mem = ⟨roundCoeff (mesh2D ε M) (x.a k), rounded_in⟩ := by
            dsimp [g, roundToGrid2D]
            rw [dif_pos rounded_in]
          rw [grid_eval]
          have err := round_error_2D (mesh2D ε M) (mesh2D_pos ε M (by exact_mod_cast hε : 0 < ε)) (x.a k)
          calc ‖x.a k - (((roundCoeff (mesh2D ε M) (x.a k)).1 : ℂ) * ((mesh2D ε M : ℚ) : ℝ) +
                          Complex.I * (((roundCoeff (mesh2D ε M) (x.a k)).2 : ℂ) * ((mesh2D ε M : ℚ) : ℝ)))‖^2
              = ‖x.a k - ⟨((mesh2D ε M : ℚ) : ℝ) * (roundCoeff (mesh2D ε M) (x.a k)).1,
                           ((mesh2D ε M : ℚ) : ℝ) * (roundCoeff (mesh2D ε M) (x.a k)).2⟩‖^2 := by
                -- Complex number equality: (n : ℂ) * (δ : ℝ) + I * (m : ℂ) * (δ : ℝ) = ⟨δ * n, δ * m⟩
                congr 2
                apply Complex.ext <;> simp [mul_comm]
            _ ≤ (Real.sqrt 2 * ((mesh2D ε M : ℚ) : ℝ))^2 := by
                -- Square both sides of the error bound
                have h_nonneg : 0 ≤ ‖x.a k - ⟨((mesh2D ε M : ℚ) : ℝ) * (roundCoeff (mesh2D ε M) (x.a k)).1,
                                                ((mesh2D ε M : ℚ) : ℝ) * (roundCoeff (mesh2D ε M) (x.a k)).2⟩‖ := norm_nonneg _
                calc ‖x.a k - ⟨((mesh2D ε M : ℚ) : ℝ) * (roundCoeff (mesh2D ε M) (x.a k)).1,
                                ((mesh2D ε M : ℚ) : ℝ) * (roundCoeff (mesh2D ε M) (x.a k)).2⟩‖^2
                    = ‖x.a k - ⟨((mesh2D ε M : ℚ) : ℝ) * (roundCoeff (mesh2D ε M) (x.a k)).1,
                                ((mesh2D ε M : ℚ) : ℝ) * (roundCoeff (mesh2D ε M) (x.a k)).2⟩‖ *
                      ‖x.a k - ⟨((mesh2D ε M : ℚ) : ℝ) * (roundCoeff (mesh2D ε M) (x.a k)).1,
                                ((mesh2D ε M : ℚ) : ℝ) * (roundCoeff (mesh2D ε M) (x.a k)).2⟩‖ := pow_two _
                  _ ≤ (Real.sqrt 2 * ((mesh2D ε M : ℚ) : ℝ)) *
                      (Real.sqrt 2 * ((mesh2D ε M : ℚ) : ℝ)) := mul_self_le_mul_self h_nonneg err
                  _ = (Real.sqrt 2 * ((mesh2D ε M : ℚ) : ℝ))^2 := (pow_two _).symm
            _ = 2 * ((mesh2D ε M : ℚ) : ℝ)^2 := by
                rw [mul_pow, Real.sq_sqrt (by norm_num)]
      _ = (IndexSet2D M).card * (2 * ((mesh2D ε M : ℚ) : ℝ)^2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((2 * M + 1)^2 : ℝ) * (2 * ((mesh2D ε M : ℚ) : ℝ)^2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast card_IndexSet2D_le M
      _ ≤ ((ε : ℝ) / 2)^2 := rounding_bound_mesh_2D ε M

  -- OUTSIDE BOUND: Tail error ≤ (ε/2)²
  have outside_bound :
      Finset.sum F_out (fun k => ‖x.a k - c.a k‖^2)
      ≤ ((ε : ℝ) / 2)^2 := by
    -- Further split F_out into k=(0,0) and tail
    let F_zero := F_out.filter (fun k => k = (0, 0))
    let F_tail := F_out.filter (fun k => k ≠ (0, 0))

    have partition_out : F_out = F_zero ∪ F_tail := by
      ext k
      simp [F_zero, F_tail, Finset.mem_filter, Finset.mem_union]
      tauto

    have disj_out : Disjoint F_zero F_tail := by
      rw [Finset.disjoint_filter]
      intro k _ h1 h2
      exact h2 h1

    have sum_split_out :
        Finset.sum F_out (fun k => ‖x.a k - c.a k‖^2)
        = Finset.sum F_zero (fun k => ‖x.a k - c.a k‖^2)
        + Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2) := by
      rw [partition_out]
      exact Finset.sum_union disj_out

    -- Zero mode contributes 0 (mean-zero condition)
    have zero_contrib : Finset.sum F_zero (fun k => ‖x.a k - c.a k‖^2) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp [F_zero, Finset.mem_filter] at hk
      have : k = (0, 0) := hk.2
      subst this
      have hx0 : x.a (0, 0) = 0 := hmean
      have hc0 : c.a (0, 0) = 0 := center_zero (0, 0) (by simp [IndexSet2D])
      simp [hx0, hc0]

    -- Tail bound: apply tail_bound_finitary_2D

    -- Key: k ∉ IndexSet2D M and k ≠ (0,0) implies |k|² > M²
    have tail_outside_ball : ∀ k ∈ F_tail, (M : ℝ)^2 < ((k.1 : ℝ)^2 + (k.2 : ℝ)^2) := by
        intro k hk
        simp [F_tail, F_out, Finset.mem_filter] at hk
        have hk_notin : k ∉ IndexSet2D M := hk.1.2
        have hk_ne : k ≠ (0, 0) := hk.2
        -- k ∉ IndexSet2D M and k ≠ (0,0) means k is outside [-M,M]²
        -- So at least one coordinate has |k_i| > M, giving k.1² + k.2² > M²
        rw [mem_IndexSet2D] at hk_notin
        push_neg at hk_notin
        -- Now hk_notin : -M ≤ k.1 → k.1 ≤ M → -M ≤ k.2 → k.2 ≤ M → k = (0, 0)
        by_cases h1 : k.1 < -(M : ℤ)
        · -- Case: k.1 < -M, so k.1^2 > M^2
          have : (M : ℝ)^2 < (k.1 : ℝ)^2 := by
            have hlt : (M : ℝ) < -(k.1 : ℝ) := by
              have h : k.1 < -(M : ℤ) := h1
              -- From integer inequality, derive real inequality
              have h1_real : (k.1 : ℝ) < (-(M : ℤ) : ℝ) := by exact_mod_cast h
              have cast_eq : (-(M : ℤ) : ℝ) = -(M : ℝ) := by norm_cast
              rw [cast_eq] at h1_real
              linarith
            calc (M : ℝ)^2 < (-(k.1 : ℝ))^2 := by nlinarith [hlt, sq_nonneg (M : ℝ), sq_nonneg (k.1 : ℝ)]
                        _ = (k.1 : ℝ)^2 := by ring
          have : (k.1 : ℝ)^2 + (k.2 : ℝ)^2 > (M : ℝ)^2 := by linarith [sq_nonneg (k.2 : ℝ)]
          exact this
        by_cases h2 : (M : ℤ) < k.1
        · -- Case: k.1 > M, so k.1^2 > M^2
          have : (M : ℝ)^2 < (k.1 : ℝ)^2 := by
            have hlt : (M : ℝ) < (k.1 : ℝ) := Int.cast_lt.mpr h2
            have hM_pos : 0 < (M : ℝ) := hM
            nlinarith [sq_nonneg (M : ℝ), sq_nonneg (k.1 : ℝ), hM_pos, hlt]
          have : (k.1 : ℝ)^2 + (k.2 : ℝ)^2 > (M : ℝ)^2 := by linarith [sq_nonneg (k.2 : ℝ)]
          exact this
        by_cases h3 : k.2 < -(M : ℤ)
        · -- Case: k.2 < -M, so k.2^2 > M^2
          have : (M : ℝ)^2 < (k.2 : ℝ)^2 := by
            have hlt : (M : ℝ) < -(k.2 : ℝ) := by
              have h : k.2 < -(M : ℤ) := h3
              -- From integer inequality, derive real inequality
              have h3_real : (k.2 : ℝ) < (-(M : ℤ) : ℝ) := by exact_mod_cast h
              have cast_eq : (-(M : ℤ) : ℝ) = -(M : ℝ) := by norm_cast
              rw [cast_eq] at h3_real
              linarith
            calc (M : ℝ)^2 < (-(k.2 : ℝ))^2 := by nlinarith [hlt, sq_nonneg (M : ℝ), sq_nonneg (k.2 : ℝ)]
                        _ = (k.2 : ℝ)^2 := by ring
          have : (k.1 : ℝ)^2 + (k.2 : ℝ)^2 > (M : ℝ)^2 := by linarith [sq_nonneg (k.1 : ℝ)]
          exact this
        by_cases h4 : (M : ℤ) < k.2
        · -- Case: k.2 > M, so k.2^2 > M^2
          have : (M : ℝ)^2 < (k.2 : ℝ)^2 := by
            have hlt : (M : ℝ) < (k.2 : ℝ) := Int.cast_lt.mpr h4
            have hM_pos : 0 < (M : ℝ) := hM
            nlinarith [sq_nonneg (M : ℝ), sq_nonneg (k.2 : ℝ), hM_pos, hlt]
          have : (k.1 : ℝ)^2 + (k.2 : ℝ)^2 > (M : ℝ)^2 := by linarith [sq_nonneg (k.1 : ℝ)]
          exact this
        -- All cases covered: if none of the four cases hold, then k is in [-M,M]²
        -- which means k = (0,0) by hk_notin, contradicting hk_ne
        exfalso
        have : k = (0, 0) := hk_notin (by omega) (by omega) (by omega) (by omega)
        exact hk_ne this

    have tail_contrib :
        Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2)
        ≤ ((ε : ℝ) / 2)^2 := by
      open scoped Classical in
      -- Centers vanish on tail, so error = ‖x.a k‖²
      have simplify : ∀ k ∈ F_tail, ‖x.a k - c.a k‖^2 = ‖x.a k‖^2 := by
        intro k hk
        simp [F_tail, F_out, Finset.mem_filter] at hk
        have : c.a k = 0 := center_zero k hk.1.2
        simp [this]

      -- Apply helper to convert F_tail to subtype finset
      obtain ⟨F_sub, h_sum⟩ := tail_finset_convert F_tail (M : ℝ) tail_outside_ball
      -- Apply tail bound
      have tail_bound := tail_bound_finitary_2D hH1 hM F_sub
      -- Use sum equality and bound
      calc Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2)
          = Finset.sum F_tail (fun k => ‖x.a k‖^2) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact simplify k hk
        _ = Finset.sum F_sub (fun g => ‖x.a g.val‖^2) := h_sum.symm
        _ ≤ (R : ℝ)^2 / (4 * Real.pi^2 * (M : ℝ)^2) := tail_bound
        _ ≤ ((ε : ℝ) / 2)^2 := tail_bound_M_of_2D hε hR

    calc Finset.sum F_out (fun k => ‖x.a k - c.a k‖^2)
        = Finset.sum F_zero (fun k => ‖x.a k - c.a k‖^2)
        + Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2) := sum_split_out
      _ = 0 + Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2) := by rw [zero_contrib]
      _ = Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2) := by ring
      _ ≤ ((ε : ℝ) / 2)^2 := tail_contrib

  -- COMBINE: inside + outside < ε²
  calc Finset.sum F (fun k => ‖x.a k - c.a k‖^2)
      = Finset.sum F_in (fun k => ‖x.a k - c.a k‖^2)
      + Finset.sum F_out (fun k => ‖x.a k - c.a k‖^2) := sum_split
    _ ≤ ((ε : ℝ) / 2)^2 + ((ε : ℝ) / 2)^2 := by linarith [inside_bound, outside_bound]
    _ = (ε : ℝ)^2 / 2 := by ring
    _ < (ε : ℝ)^2 := by linarith [sq_pos_of_pos hε]

/-! ## Budget Analysis for gridFinset_sound_2D

**xBudget** (extractable data - C0):
- ε, R : ℚ (rational parameters)
- M_of ε R : ℕ (computable cutoff)
- mesh2D ε M : ℚ (computable mesh size)
- IndexSet2D M : Finset (ℤ × ℤ) (finite frequency set)
- coeffBox : (k : ℤ × ℤ) → Finset (ℤ × ℤ) (finite boxes)
- roundCoeff : ℂ → ℤ × ℤ (floor operations)
- roundToGrid2D : ℓ2Z2 → GridPoint2D (witness constructor - C0)
- gridToSeq : GridPoint2D → ℓ2Z2 (evaluation function)
- **gridFinset2D : Finset (GridPoint2D)** - C5 mathematical finset (NOT materialized)

**vBudget** (proof - C0-C2):
- tail_bound_finitary_2D : proven constructively (dimension-free!)
- tail_bound_M_of_2D : rational inequality (C0-C2)
- rounding_bound_mesh_2D : finite arithmetic bound (C0-C2)
- Existence quantifier: C5 but witness comes from roundToGrid2D (C0 function)

**Critical Insight**:
The WITNESS FUNCTION roundToGrid2D is C0 (computable from x).
The WITNESS SET gridFinset2D is C5 (mathematical existence) but IRRELEVANT.
We never enumerate the grid - we only construct the one witness we need!

**Comparison to 1D**:
- Same proof structure (tail + inside split)
- Same tail bound formula (dimension-free!)
- Different mesh formula: ε/(4(2M+1)) vs ε/(2(2M+1))
  (accounts for (2M+1)² term in 2D)
- Same budget classification (C0 witness, C5 existence)

**Proof sketch for filling sorries**:

1. `tail_bound_M_of_2D`:
   - M > R/(π_lb·ε) by M_of definition
   - Therefore 2πM > 2R/ε
   - Square: (2πM)² > 4R²/ε²
   - Divide: R²/(2πM)² < ε²/4 = (ε/2)²

2. `rounding_bound_mesh_2D`:
   - Expand: 2·(2M+1)²·2·(ε/(4(2M+1)))² = 2·(2M+1)²·2·ε²/(16(2M+1)²)
   - Simplify: = 2·2·ε²/16 = ε²/4 < (ε/2)² ✓

3. `inside_bound`:
   - F_in ⊆ IndexSet2D M, card ≤ (2M+1)²
   - Each term: ‖x.a k - c.a k‖² ≤ 2δ² (rounding error)
   - Sum: ≤ (2M+1)²·2δ² ≤ (ε/2)² by rounding_bound_mesh_2D

4. `outside_bound`:
   - zero_contrib: x.a(0,0) = 0 (meanZero), c.a(0,0) = 0 (gridToSeq)
   - tail_contrib: Centers vanish outside IndexSet → ‖x.a k - c.a k‖² = ‖x.a k‖²
   - |k|² > M² for tail → apply tail_bound_finitary_2D → ≤ R²/(4π²M²)
   - Use tail_bound_M_of_2D → ≤ (ε/2)²

**Total Budget**: C0-C2 for witness construction + C5 for existence quantifier
-/

end RellichKondrachov2D.Seq
