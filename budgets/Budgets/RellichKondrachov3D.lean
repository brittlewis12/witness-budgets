import Budgets.RellichKondrachov3D.Seq
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Rellich-Kondrachov 3D: Main Soundness Theorem

This file proves the main constructive compactness result for 3D:
Every mean-zero H¹ function can be ε-approximated by a finite grid witness.

## Main results

* `gridFinset_sound_3D` - Main theorem: witness grid covers the H¹-ball

## Proof strategy

1. Choose M = M_of ε R to control tail error
2. Construct witness g = roundToGrid3D ε R M x
3. Split error into tail + inside:
   - Tail (|k|² > M²): ≤ (ε/2)² using dimension-free bound
   - Inside (|k|² ≤ M²): ≤ (ε/2)² using mesh3D rounding
4. Total: < ε²

This mirrors the 1D/2D proof structure exactly.

-/

open scoped BigOperators ComplexConjugate Real

namespace ℓ2Z3

open ℓ2Z3

/-! ## Helper lemmas for soundness theorem -/

/-- M_of is positive (key for positivity of M in tail bound) -/
lemma M_of_pos (ε R : ℚ) (_hε : 0 < ε) (_hR : 0 < R) : 0 < M_of ε R := by
  unfold M_of
  omega

/-- Conservative lower bound for π (used in tail bound) -/
def pi_rat_lb : ℚ := 3

/-- Tail bound holds with M_of choice (dimension-free!) -/
lemma tail_bound_M_of_3D {ε R : ℚ} (hε : 0 < (ε : ℝ)) (hR : 0 < (R : ℝ)) :
    (R : ℝ)^2 / (4 * Real.pi^2 * (M_of ε R : ℝ)^2) ≤ ((ε : ℝ) / 2)^2 := by
  set M := M_of ε R with hM_def

  -- M = ceil(R/(πε)) + 1, so M > R/(πε)
  have hM_pi : (M : ℝ) > (R : ℝ) / (Real.pi * (ε : ℝ)) := by
    unfold M_of at hM_def
    calc (M : ℝ)
        = (Nat.ceil ((R : ℝ) / (Real.pi * (ε : ℝ))) + 1 : ℕ) := by simp [M, hM_def]
      _ = (Nat.ceil ((R : ℝ) / (Real.pi * (ε : ℝ))) : ℝ) + 1 := by norm_cast
      _ > (R : ℝ) / (Real.pi * (ε : ℝ)) := by
          have h_ceil : (R : ℝ) / (Real.pi * (ε : ℝ)) ≤ Nat.ceil ((R : ℝ) / (Real.pi * (ε : ℝ))) := Nat.le_ceil _
          linarith

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

/-- Rounding error bound for inside region (3D version) -/
lemma rounding_bound_mesh_3D_strict (ε : ℚ) (M : ℕ) (hM : M ≠ 0) :
    ((2 * M + 1)^3 : ℝ) * (2 * ((mesh3D ε M : ℝ))^2) ≤ ((ε : ℝ) / 2)^2 := by
  unfold mesh3D
  -- Need M ≠ 0 for (2M+1) ≠ 0
  have card_pos : (0 : ℝ) < (2 * M + 1 : ℕ) := by
    have h : 0 < 2 * M + 1 := by omega
    exact_mod_cast h
  have card_sq_pos : (0 : ℝ) < ((2 * M + 1 : ℕ) : ℝ)^2 := by positivity
  -- Expand and simplify
  calc ((2 * M + 1)^3 : ℝ) * (2 * ((ε / (8 * (2 * M + 1)^2) : ℚ) : ℝ)^2)
      = ((2 * M + 1 : ℕ) : ℝ)^3 * (2 * ((ε : ℝ) / (8 * ((2 * M + 1 : ℕ) : ℝ)^2))^2) := by
        push_cast
        ring
    _ = ((2 * M + 1 : ℕ) : ℝ)^3 * (2 * (ε : ℝ)^2 / (64 * ((2 * M + 1 : ℕ) : ℝ)^4)) := by
        congr 1
        field_simp
        ring
    _ = ((2 * M + 1 : ℕ) : ℝ)^3 * ((ε : ℝ)^2 / (32 * ((2 * M + 1 : ℕ) : ℝ)^4)) := by
        ring
    _ = (ε : ℝ)^2 / (32 * ((2 * M + 1 : ℕ) : ℝ)) := by
        field_simp
    _ ≤ (ε : ℝ)^2 / 4 := by
        apply div_le_div_of_nonneg_left (sq_nonneg _)
        · norm_num
        · have : (4 : ℝ) ≤ 32 * ((2 * M + 1 : ℕ) : ℝ) := by
            calc (4 : ℝ) = 32 * (1/8) := by norm_num
                _ ≤ 32 * 1 := by linarith
                _ ≤ 32 * ((2 * M + 1 : ℕ) : ℝ) := by
                    apply mul_le_mul_of_nonneg_left _ (by norm_num)
                    have h : 1 ≤ 2 * M + 1 := by omega
                    exact_mod_cast h
          exact this
    _ = ((ε : ℝ) / 2)^2 := by ring

/-- Coefficient bound from H¹ norm for 3D -/
lemma coeff_bound_from_H1_3D {x : Seq3D} {R : ℝ} (_hR : 0 < R) (hx : InH1Ball R x)
    (k : ℤ × ℤ × ℤ) (_hk : k ≠ (0, (0, 0))) :
    ‖x.a k‖^2 ≤ R^2 := by
  have h_weight : 1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2) > 0 := by
    linarith [sq_nonneg (2 * Real.pi * (k.1 : ℝ)),
              sq_nonneg (2 * Real.pi * (k.2.1 : ℝ)),
              sq_nonneg (2 * Real.pi * (k.2.2 : ℝ))]
  have bound := hx {k}
  simp only [Finset.sum_singleton] at bound
  have h1 : (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2)) * ‖x.a k‖^2 ≤ R^2 := bound
  have h2 : ‖x.a k‖^2 * (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2)) ≤ R^2 := by
    rwa [mul_comm] at h1
  have h3 : ‖x.a k‖^2 * 1 ≤ ‖x.a k‖^2 * (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2)) := by
    apply mul_le_mul_of_nonneg_left
    · have : 0 ≤ 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2) := by positivity
      linarith
    · exact sq_nonneg _
  calc ‖x.a k‖^2
      = ‖x.a k‖^2 * 1 := by ring
    _ ≤ ‖x.a k‖^2 * (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2)) := h3
    _ ≤ R^2 := h2

/-- Rounded coefficient is in box (geometric lemma for 3D) -/
lemma rounded_in_box_3D {ε R : ℚ} {M : ℕ} {k : ℤ × ℤ × ℤ} {c : ℂ}
    (_hε : 0 < (ε : ℝ)) (_hR : 0 < (R : ℝ)) (_hk : k ≠ (0, (0, 0)))
    (_hc : ‖c‖^2 ≤ (R : ℝ)^2) :
    roundCoeff (mesh3D ε M) c ∈ coeffBox ε R M k := by
  simp only [coeffBox, roundCoeff, Finset.mem_product, Finset.mem_Icc]
  let δ := mesh3D ε M
  let bound := coeffBound R k
  let rad := Nat.ceil (bound / δ) + 1

  have hδ : 0 < (δ : ℝ) := mesh3D_pos ε M (by exact_mod_cast _hε : 0 < ε)
  have hbound : 0 ≤ (bound : ℝ) := by
    unfold bound coeffBound
    split_ifs
    · norm_num
    · exact_mod_cast le_of_lt _hR
  have bound_eq_R : (bound : ℝ) = (R : ℝ) := by simp [bound, coeffBound, _hk]

  -- Each component of c has magnitude ≤ ‖c‖ ≤ R
  have hc_norm : ‖c‖ ≤ (R : ℝ) := by
    calc ‖c‖
        = Real.sqrt (‖c‖^2) := by rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt ((R : ℝ)^2) := Real.sqrt_le_sqrt _hc
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

/-- `roundToGrid3D` always returns coefficients inside the prescribed box. -/
lemma roundToGrid_valid_3D (ε R : ℚ) (M : ℕ) (x : Seq3D)
    {k : ℤ × ℤ × ℤ} (hk : k ∈ IndexSet3D M) :
    ((roundToGrid3D ε R M x) k hk).val ∈ coeffBox ε R M k := by
  exact ((roundToGrid3D ε R M x) k hk).property

/-- Rounding error bound (dimension-independent) -/
lemma round_error_3D (δ : ℚ) (hδ : 0 < (δ : ℝ)) (c : ℂ) :
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
        have h1 : ‖c - ⟨(δ : ℝ) * n_re, (δ : ℝ) * n_im⟩‖ = Real.sqrt (Complex.normSq (c - ⟨(δ : ℝ) * n_re, (δ : ℝ) * n_im⟩)) := rfl
        rw [h1, Complex.normSq_apply]
        simp [Complex.sub_re, Complex.sub_im]
        ring_nf
    _ ≤ Real.sqrt (2 * (δ : ℝ)^2) := Real.sqrt_le_sqrt sum_bound
    _ = Real.sqrt 2 * (δ : ℝ) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by linarith)]

/-! ## Main Soundness Theorem -/

/-- Helper: Convert a filtered finset to subtype finset for tail bound application -/
lemma tail_finset_convert {x : Seq3D} (F : Finset (ℤ × ℤ × ℤ)) (M : ℝ)
    (h : ∀ k ∈ F, M^2 < ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2)) :
    ∃ (G : Finset {k : ℤ × ℤ × ℤ // M^2 < ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2)}),
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

/-- **Main soundness theorem for 3D**: Every mean-zero H¹-bounded sequence
    has an ε-close grid point (constructively proven via rounding).

    PROOF STRATEGY (mirrors 2D exactly):
    1. Choose M := M_of ε R to control tail error
    2. Define witness g := roundToGrid3D ε R M x
    3. Split error into tail + inside:
       - Tail (|k|² > M²): ≤ (ε/2)² using tail_bound_finitary_3D
       - Inside (|k|² ≤ M²): ≤ (ε/2)² using rounding error
    4. Total: (ε/2)² + (ε/2)² < ε²

    WITNESS STRUCTURE:
    - gridToSeq g is the C0 witness function
    - GridPoint3D is a function type (computable, not enumerated)
    - The witness comes from roundToGrid3D (computable function)
-/
theorem gridFinset_sound_3D (ε R : ℚ) (hε : 0 < (ε : ℝ)) (hR : 0 < (R : ℝ))
    (x : Seq3D) (hmean : meanZero x) (hH1 : InH1Ball (R : ℝ) x) :
    ∃ (g : GridPoint3D ε R (M_of ε R)),
      ∀ F : Finset (ℤ × ℤ × ℤ),
        Finset.sum F (fun k => ‖x.a k - (gridToSeq ε R (M_of ε R) g).a k‖^2)
          < (ε : ℝ)^2 := by
  -- Step 1: Choose M using M_of to control tail error
  set M := M_of ε R with hMdef

  have hM : 0 < (M : ℝ) := by
    simpa [hMdef] using (Nat.cast_pos.mpr (M_of_pos ε R (Rat.cast_pos.mp hε) (Rat.cast_pos.mp hR)))

  have hM_ne : M ≠ 0 := by
    simpa [hMdef] using (Nat.pos_iff_ne_zero.mp (M_of_pos ε R (Rat.cast_pos.mp hε) (Rat.cast_pos.mp hR)))

  -- Step 2: Construct witness via rounding
  let g := roundToGrid3D ε R M x

  use g

  -- Step 3: Prove distance bound for any finite set F
  intro F

  -- Define center from grid point
  let c := gridToSeq ε R M g

  -- Center evaluation lemmas (placeholder - needs gridToSeq implementation)
  have center_zero : ∀ k, k ∉ IndexSet3D M → c.a k = 0 := by
    intro k hk
    simp [c, gridToSeq, hk]

  -- Split F into inside (IndexSet3D M) and outside
  let F_in := F.filter (fun k => k ∈ IndexSet3D M)
  let F_out := F.filter (fun k => k ∉ IndexSet3D M)

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
    set δ := mesh3D ε M
    have hδ : 0 < (δ : ℝ) := mesh3D_pos ε M (by exact_mod_cast Rat.cast_pos.mp hε)

    -- Bound each coefficient's rounding error by 2·δ²
    have per_coeff_bound : ∀ k ∈ F_in, ‖x.a k - c.a k‖^2 ≤ 2 * (δ : ℝ)^2 := by
      intro k hk
      simp [F_in, Finset.mem_filter] at hk
      have hk_in : k ∈ IndexSet3D M := hk.2

      -- k ∈ IndexSet3D M means k ≠ (0,(0,0))
      have hk_ne_zero : k ≠ (0, (0, 0)) := by
        intro h_eq
        subst h_eq
        simp [IndexSet3D] at hk_in

      -- Get H¹ bound on coefficient
      have h_coeff_bound := coeff_bound_from_H1_3D hR hH1 k hk_ne_zero

      -- Apply rounded_in_box_3D to show roundCoeff is in the box
      have h_in_box : roundCoeff δ (x.a k) ∈ coeffBox ε R M k :=
        rounded_in_box_3D hε hR hk_ne_zero h_coeff_bound

      -- Therefore g stores the rounded coefficient (not the fallback)
      have g_eq : (g k hk_in).val = roundCoeff δ (x.a k) := by
        simp only [g, roundToGrid3D]
        rw [dif_pos h_in_box]

      -- Set up abbreviation for the rounded coefficient
      set p := roundCoeff δ (x.a k)

      -- Apply round_error_3D to get the key bound
      have round_err := round_error_3D δ hδ (x.a k)

      -- Show that c.a k equals the scaled rounded coefficient
      -- This uses that g stores p and gridToSeq scales it
      have c_is_scaled_p : c.a k =
          (⟨(δ : ℝ) * p.1, (δ : ℝ) * p.2⟩ : ℂ) := by
        -- Unfold definitions
        simp only [c, gridToSeq, dif_pos hk_in, δ]
        -- Use g_eq to substitute p
        have : (g k hk_in).val = p := g_eq
        rw [this]
        -- Now it's just Complex equality (mul_comm handles ↑p.1 * ↑δ = ↑δ * ↑p.1)
        apply Complex.ext <;> simp [mul_comm]

      rw [c_is_scaled_p]

      calc ‖x.a k - (⟨(δ : ℝ) * p.1, (δ : ℝ) * p.2⟩ : ℂ)‖^2
          ≤ (Real.sqrt 2 * (δ : ℝ))^2 := by
            have h_nonneg : 0 ≤ Real.sqrt 2 * (δ : ℝ) := by positivity
            have h_norm_nonneg : 0 ≤ ‖x.a k - (⟨(δ : ℝ) * p.1, (δ : ℝ) * p.2⟩ : ℂ)‖ := norm_nonneg _
            apply sq_le_sq' (by linarith [h_norm_nonneg, h_nonneg]) round_err
        _ = 2 * (δ : ℝ)^2 := by
            rw [mul_pow, Real.sq_sqrt (by norm_num)]

    -- Sum the per-coefficient bounds
    calc Finset.sum F_in (fun k => ‖x.a k - c.a k‖^2)
        ≤ Finset.sum F_in (fun k => 2 * (δ : ℝ)^2) := by
          apply Finset.sum_le_sum
          intro k hk
          exact per_coeff_bound k hk
      _ = F_in.card * (2 * (δ : ℝ)^2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (IndexSet3D M).card * (2 * (δ : ℝ)^2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : F_in ⊆ IndexSet3D M := by
            intro k hk
            simp [F_in, Finset.mem_filter] at hk
            exact hk.2
          exact_mod_cast Finset.card_le_card this
      _ ≤ (2 * M + 1)^3 * (2 * (δ : ℝ)^2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast card_IndexSet3D_le M
      _ ≤ ((ε : ℝ) / 2)^2 := rounding_bound_mesh_3D_strict ε M hM_ne

  -- OUTSIDE BOUND: Tail error ≤ (ε/2)²
  have outside_bound :
      Finset.sum F_out (fun k => ‖x.a k - c.a k‖^2)
      ≤ ((ε : ℝ) / 2)^2 := by
    -- Further split F_out into k=(0,0,0) and tail
    let F_zero := F_out.filter (fun k => k = (0, (0, 0)))
    let F_tail := F_out.filter (fun k => k ≠ (0, (0, 0)))

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
      have : k = (0, (0, 0)) := hk.2
      subst this
      have hx0 : x.a (0, (0, 0)) = 0 := hmean
      have hc0 : c.a (0, (0, 0)) = 0 := center_zero (0, (0, 0)) (by simp [IndexSet3D])
      simp [hx0, hc0]

    -- Tail bound: apply tail_bound_finitary_3D
    have tail_outside_ball : ∀ k ∈ F_tail, (M : ℝ)^2 < ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2) := by
        intro k hk
        simp [F_tail, F_out, Finset.mem_filter] at hk
        have hk_notin : k ∉ IndexSet3D M := hk.1.2
        have hk_ne : k ≠ (0, (0, 0)) := hk.2
        -- k ∉ IndexSet3D M and k ≠ (0,0,0) means k is outside [-M,M]³
        rw [mem_IndexSet3D] at hk_notin
        push_neg at hk_notin
        -- At least one coordinate has |k_i| > M
        by_cases h1 : k.1 < -(M : ℤ)
        · -- Case: k.1 < -M
          have : (M : ℝ)^2 < (k.1 : ℝ)^2 := by
            have hlt : (M : ℝ) < -(k.1 : ℝ) := by
              have h : k.1 < -(M : ℤ) := h1
              have h1_real : (k.1 : ℝ) < (-(M : ℤ) : ℝ) := by exact_mod_cast h
              have cast_eq : (-(M : ℤ) : ℝ) = -(M : ℝ) := by norm_cast
              rw [cast_eq] at h1_real
              linarith
            calc (M : ℝ)^2 < (-(k.1 : ℝ))^2 := by nlinarith [hlt, sq_nonneg (M : ℝ), sq_nonneg (k.1 : ℝ)]
                        _ = (k.1 : ℝ)^2 := by ring
          have : (k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2 > (M : ℝ)^2 := by
            linarith [sq_nonneg (k.2.1 : ℝ), sq_nonneg (k.2.2 : ℝ)]
          exact this
        by_cases h2 : (M : ℤ) < k.1
        · -- Case: k.1 > M
          have : (M : ℝ)^2 < (k.1 : ℝ)^2 := by
            have hlt : (M : ℝ) < (k.1 : ℝ) := Int.cast_lt.mpr h2
            nlinarith [sq_nonneg (M : ℝ), sq_nonneg (k.1 : ℝ), hM, hlt]
          have : (k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2 > (M : ℝ)^2 := by
            linarith [sq_nonneg (k.2.1 : ℝ), sq_nonneg (k.2.2 : ℝ)]
          exact this
        by_cases h3 : k.2.1 < -(M : ℤ)
        · -- Case: k.2.1 < -M
          have : (M : ℝ)^2 < (k.2.1 : ℝ)^2 := by
            have hlt : (M : ℝ) < -(k.2.1 : ℝ) := by
              have h : k.2.1 < -(M : ℤ) := h3
              have h3_real : (k.2.1 : ℝ) < (-(M : ℤ) : ℝ) := by exact_mod_cast h
              have cast_eq : (-(M : ℤ) : ℝ) = -(M : ℝ) := by norm_cast
              rw [cast_eq] at h3_real
              linarith
            calc (M : ℝ)^2 < (-(k.2.1 : ℝ))^2 := by nlinarith [hlt, sq_nonneg (M : ℝ), sq_nonneg (k.2.1 : ℝ)]
                        _ = (k.2.1 : ℝ)^2 := by ring
          have : (k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2 > (M : ℝ)^2 := by
            linarith [sq_nonneg (k.1 : ℝ), sq_nonneg (k.2.2 : ℝ)]
          exact this
        by_cases h4 : (M : ℤ) < k.2.1
        · -- Case: k.2.1 > M
          have : (M : ℝ)^2 < (k.2.1 : ℝ)^2 := by
            have hlt : (M : ℝ) < (k.2.1 : ℝ) := Int.cast_lt.mpr h4
            nlinarith [sq_nonneg (M : ℝ), sq_nonneg (k.2.1 : ℝ), hM, hlt]
          have : (k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2 > (M : ℝ)^2 := by
            linarith [sq_nonneg (k.1 : ℝ), sq_nonneg (k.2.2 : ℝ)]
          exact this
        by_cases h5 : k.2.2 < -(M : ℤ)
        · -- Case: k.2.2 < -M
          have : (M : ℝ)^2 < (k.2.2 : ℝ)^2 := by
            have hlt : (M : ℝ) < -(k.2.2 : ℝ) := by
              have h : k.2.2 < -(M : ℤ) := h5
              have h5_real : (k.2.2 : ℝ) < (-(M : ℤ) : ℝ) := by exact_mod_cast h
              have cast_eq : (-(M : ℤ) : ℝ) = -(M : ℝ) := by norm_cast
              rw [cast_eq] at h5_real
              linarith
            calc (M : ℝ)^2 < (-(k.2.2 : ℝ))^2 := by nlinarith [hlt, sq_nonneg (M : ℝ), sq_nonneg (k.2.2 : ℝ)]
                        _ = (k.2.2 : ℝ)^2 := by ring
          have : (k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2 > (M : ℝ)^2 := by
            linarith [sq_nonneg (k.1 : ℝ), sq_nonneg (k.2.1 : ℝ)]
          exact this
        by_cases h6 : (M : ℤ) < k.2.2
        · -- Case: k.2.2 > M
          have : (M : ℝ)^2 < (k.2.2 : ℝ)^2 := by
            have hlt : (M : ℝ) < (k.2.2 : ℝ) := Int.cast_lt.mpr h6
            nlinarith [sq_nonneg (M : ℝ), sq_nonneg (k.2.2 : ℝ), hM, hlt]
          have : (k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2 > (M : ℝ)^2 := by
            linarith [sq_nonneg (k.1 : ℝ), sq_nonneg (k.2.1 : ℝ)]
          exact this
        -- All cases covered: if none hold, then k ∈ [-M,M]³, so k = (0,0,0)
        exfalso
        have : k = (0, (0, 0)) := hk_notin (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        exact hk_ne this

    have tail_contrib :
        Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2)
        ≤ ((ε : ℝ) / 2)^2 := by
      -- Centers vanish on tail, so error = ‖x.a k‖²
      have simplify : ∀ k ∈ F_tail, ‖x.a k - c.a k‖^2 = ‖x.a k‖^2 := by
        intro k hk
        simp [F_tail, F_out, Finset.mem_filter] at hk
        have : c.a k = 0 := center_zero k hk.1.2
        simp [this]

      -- Apply helper to convert F_tail to subtype finset
      obtain ⟨F_sub, h_sum⟩ := tail_finset_convert F_tail (M : ℝ) tail_outside_ball
      -- Apply tail bound
      have tail_bound := tail_bound_finitary_3D hH1 hM F_sub
      -- Use sum equality and bound
      calc Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2)
          = Finset.sum F_tail (fun k => ‖x.a k‖^2) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact simplify k hk
        _ = Finset.sum F_sub (fun g => ‖x.a g.val‖^2) := h_sum.symm
        _ ≤ (R : ℝ)^2 / (4 * Real.pi^2 * (M : ℝ)^2) := tail_bound
        _ ≤ ((ε : ℝ) / 2)^2 := tail_bound_M_of_3D hε hR

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

end ℓ2Z3
