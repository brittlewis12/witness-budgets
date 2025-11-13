import Budgets.RellichKondrachovD.Core
import Budgets.RellichKondrachovD.TailBound

/-
! Rellich–Kondrachov in arbitrary dimension: rounding estimates

This file establishes the rounding error bounds that turn the continuous
coefficients into a finite witness.

## Main results
* `round_error_d` : each coefficient incurs an error at most `√2 · δ`.
* `coeff_bound_from_H1_d` : H¹ control yields pointwise bounds.
* `rounded_in_box_d` : the rounded coefficient lies in the prescribed box.
* `rounding_bound_mesh_d` : the chosen mesh satisfies the global budget
  `(2M+1)^d · 2δ² ≤ (ε / 2)²`.

These statements do not depend on the specific dimension and only rely on the
fact that rounding happens coordinatewise with the same mesh.
-/

open scoped BigOperators ComplexConjugate Real

namespace ℓ2ZD

open ℓ2ZD

/-! ## Rounding error per coefficient -/

/-- **Rounding error bound (dimension-independent)**

    For any complex number c and mesh size δ > 0, the floor-based rounding
    satisfies: ‖c - round(c)‖ ≤ √2 · δ

    This is the same bound in every dimension (works coordinatewise).

    PROOF STRATEGY:
    1. roundCoeff uses floor in Re/Im coordinates
    2. Floor property: n ≤ x/δ < n+1, so |x - δ·n| ≤ δ
    3. Both Re and Im errors ≤ δ
    4. Combined via Pythagorean: ‖error‖ ≤ √(δ² + δ²) = √2 · δ
-/
lemma round_error_d {d : ℕ} [NeZero d] (δ : ℚ) (hδ : 0 < (δ : ℝ)) (c : ℂ) :
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

/-! ## Coefficient magnitude bounds -/

/-- **Coefficient bound from H¹ norm**

    For k ≠ 0, the H¹ condition gives:
    ‖aₖ‖² ≤ R²

    This is because h1Weight(k) ≥ 1 for k ≠ 0.

    PROOF STRATEGY:
    1. H¹ bound (singleton): h1Weight(k) · ‖aₖ‖² ≤ R²
    2. h1Weight(k) = 1 + 4π²·normSq(k) ≥ 1
    3. Therefore: ‖aₖ‖² ≤ ‖aₖ‖² · h1Weight(k) ≤ R²
-/
lemma coeff_bound_from_H1_d {d : ℕ} [NeZero d] {x : SeqD d} {R : ℝ}
    (_hR : 0 < R) (hx : InH1Ball R x)
    (k : Lattice d) (_hk : k ≠ (fun _ => 0)) :
    ‖x.a k‖^2 ≤ R^2 := by
  have h_weight : h1Weight k > 0 := by
    unfold h1Weight normSq
    have : 0 ≤ 4 * Real.pi^2 * ∑ i, ((k i : ℝ)^2) := by positivity
    linarith
  have bound := hx {k}
  simp only [Finset.sum_singleton] at bound
  have h1 : h1Weight k * ‖x.a k‖^2 ≤ R^2 := bound
  have h2 : ‖x.a k‖^2 * h1Weight k ≤ R^2 := by
    rwa [mul_comm] at h1
  have h3 : ‖x.a k‖^2 * 1 ≤ ‖x.a k‖^2 * h1Weight k := by
    apply mul_le_mul_of_nonneg_left
    · have : h1Weight k = 1 + 4 * Real.pi^2 * normSq k := rfl
      rw [this]
      have : 0 ≤ 4 * Real.pi^2 * normSq k := by
        unfold normSq
        positivity
      linarith
    · exact sq_nonneg _
  calc ‖x.a k‖^2
      = ‖x.a k‖^2 * 1 := by ring
    _ ≤ ‖x.a k‖^2 * h1Weight k := h3
    _ ≤ R^2 := h2

/-! ## Coefficient box membership -/

/-- **Rounded coefficient is in box (geometric lemma)**

    If ‖c‖ ≤ R, then roundCoeff δ c ∈ coeffBox ε R M k.

    This is the key geometric property ensuring the rounded witness
    stays within the prescribed coefficient boxes.

    PROOF STRATEGY:
    1. Each component of c has magnitude ≤ ‖c‖ ≤ R
    2. Rounded coordinate: n = ⌊component/δ⌋
    3. Therefore: |n| ≤ ⌈R/δ⌉
    4. coeffBox has radius rad = ⌈R/δ⌉ + 1
    5. So n ∈ [-rad, rad]
-/
lemma rounded_in_box_d {d : ℕ} [NeZero d] {ε R : ℚ} {M : ℕ} {k : Lattice d} {c : ℂ}
    (hε : 0 < (ε : ℝ)) (hR : 0 < (R : ℝ)) (hk : k ≠ (fun _ => 0))
    (hc : ‖c‖^2 ≤ (R : ℝ)^2) :
    roundCoeff (meshD d ε M) c ∈ coeffBox ε R M k := by
  simp only [coeffBox, roundCoeff, Finset.mem_product, Finset.mem_Icc]
  let δ := meshD d ε M
  let bound := coeffBound R k
  let rad := Nat.ceil (bound / δ) + 1

  have hδ : 0 < (δ : ℝ) := meshD_pos d ε M (by exact_mod_cast hε)
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

/-- `roundToGridD` always returns coefficients inside the prescribed box. -/
lemma roundToGrid_valid_d {d : ℕ} [NeZero d] (ε R : ℚ) (M : ℕ) (x : SeqD d)
    {k : Lattice d} (hk : k ∈ IndexSetD d M) :
    ((roundToGridD ε R M x) k hk).val ∈ coeffBox ε R M k := by
  simp only [roundToGridD]
  split_ifs with h
  · exact h
  · exact zero_in_coeffBox ε R M k

/-! ## Total rounding error bound -/

/-- **Rounding error bound with meshD (dimension-parametric)**

    The mesh formula ensures:
    (2M+1)ᵈ × 2δ² ≤ (ε/2)²

    where δ = meshD d ε M = ε / (4 * (2M+1)^⌈d/2⌉)

    PROOF STRATEGY:
    1. Substitute mesh formula
    2. Simplify: (2M+1)ᵈ × 2 × (ε / (4(2M+1)^⌈d/2⌉))²
    3. Cancel powers: numerator has (2M+1)ᵈ, denominator has (2M+1)^(2⌈d/2⌉)
    4. Since 2⌈d/2⌉ ≥ d, the ratio is ≤ 1
    5. Final result: ≤ ε²/8 ≤ (ε/2)²

    The key is that 2⌈d/2⌉ - d ≥ 0 for all d ∈ ℕ.
-/
lemma rounding_bound_mesh_d {d : ℕ} [NeZero d] (ε : ℚ) (M : ℕ) (hM : M ≠ 0) :
    ((2 * M + 1)^d : ℝ) * (2 * ((meshD d ε M : ℝ))^2) ≤ ((ε : ℝ) / 2)^2 := by
  unfold meshD
  -- Need M ≠ 0 for (2M+1) ≠ 0
  have card_pos : (0 : ℝ) < (2 * M + 1 : ℕ) := by
    have h : 0 < 2 * M + 1 := by omega
    exact_mod_cast h

  -- Set up the ceiling exponent
  set exp := Nat.ceil ((d : ℚ) / 2) with hexp

  have exp_pos : (0 : ℝ) < ((2 * M + 1 : ℕ) : ℝ)^exp := by positivity

  -- Key lemma: 2*ceil(d/2) ≥ d for all d
  have two_exp_ge_d : 2 * exp ≥ d := by
    have h_le : (d : ℚ) / 2 ≤ exp := by
      simpa [exp, hexp] using (Nat.le_ceil ((d : ℚ) / 2))
    have h_mul := mul_le_mul_of_nonneg_left h_le (by norm_num : (0 : ℚ) ≤ 2)
    have h_two : 2 * ((d : ℚ) / 2) = (d : ℚ) := by field_simp
    have bound_rat : (d : ℚ) ≤ (2 : ℚ) * exp := by
      simpa [h_two, two_mul, mul_comm, mul_left_comm] using h_mul
    exact_mod_cast bound_rat

  -- Direct simplification showing the bound
  have h_pos : (0 : ℝ) < ((2 * M + 1 : ℕ) : ℝ)^d := by positivity
  have h_one_le : (1 : ℝ) ≤ ((2 * M + 1 : ℕ) : ℝ) := by
    have : 1 ≤ 2 * M + 1 := by omega
    exact_mod_cast this
  have h_simpl : (ε : ℝ)^2 * ((2 * M + 1 : ℕ) : ℝ)^d / (8 * ((2 * M + 1 : ℕ) : ℝ)^d)
                 = (ε : ℝ)^2 / 8 := by field_simp [h_pos.ne']

  -- Now we can proceed with a simpler calculation avoiding negative exponents
  calc ((2 * M + 1)^d : ℝ) * (2 * ((ε / (4 * (2 * M + 1)^exp) : ℚ) : ℝ)^2)
      = ((2 * M + 1 : ℕ) : ℝ)^d * (2 * ((ε : ℝ) / (4 * ((2 * M + 1 : ℕ) : ℝ)^exp))^2) := by
        push_cast
        ring
    _ = ((2 * M + 1 : ℕ) : ℝ)^d * (2 * (ε : ℝ)^2 / (16 * ((2 * M + 1 : ℕ) : ℝ)^(2*exp))) := by
        congr 1
        field_simp
        ring
    _ = ((2 * M + 1 : ℕ) : ℝ)^d * ((ε : ℝ)^2 / (8 * ((2 * M + 1 : ℕ) : ℝ)^(2*exp))) := by
        ring
    _ = (ε : ℝ)^2 * ((2 * M + 1 : ℕ) : ℝ)^d / (8 * ((2 * M + 1 : ℕ) : ℝ)^(2*exp)) := by
        ring
    _ ≤ (ε : ℝ)^2 * ((2 * M + 1 : ℕ) : ℝ)^d / (8 * ((2 * M + 1 : ℕ) : ℝ)^d) := by
        -- Use 2*exp ≥ d to get (2M+1)^(2*exp) ≥ (2M+1)^d
        apply div_le_div_of_nonneg_left
        · positivity
        · positivity
        · -- Power monotonicity: (2M+1)^d ≤ (2M+1)^(2*exp) when d ≤ 2*exp
          have base_ge : 1 ≤ 2 * M + 1 := by omega
          have h_pow : (2 * M + 1)^d ≤ (2 * M + 1)^(2 * exp) :=
            Nat.pow_le_pow_right base_ge two_exp_ge_d
          have : ((2 * M + 1 : ℕ) : ℝ)^d ≤ ((2 * M + 1 : ℕ) : ℝ)^(2 * exp) := by
            exact_mod_cast h_pow
          apply mul_le_mul_of_nonneg_left this (by norm_num)
    _ = (ε : ℝ)^2 / 8 := h_simpl
    _ ≤ ((ε : ℝ) / 2)^2 := by
        have h_eq : ((ε : ℝ) / 2)^2 = (ε : ℝ)^2 / 4 := by ring
        rw [h_eq]
        have : (ε : ℝ)^2 / 8 ≤ (ε : ℝ)^2 / 4 := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by norm_num)
        exact this

end ℓ2ZD
