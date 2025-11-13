import Budgets.RellichKondrachovD.Core
import Mathlib.Analysis.Real.Pi.Bounds

/-
! Rellich–Kondrachov in arbitrary dimension: tail bound

This file proves the elementary spectral inequality that controls the tail of a
sequence in any dimension.

## Main results
* `tail_bound_finitary_d` : for any finite set of indices outside the cube `[-M,M]^d`
  we have `∑ ‖a_k‖² ≤ R² / (4 π² M²)`.
* `tail_bound_M_of_d` : choosing `M = M_of ε R` forces the tail contribution
  below `(ε / 2)²`.

The argument is the same in every dimension: once `k` lies outside the cube we
obtain `∑ k_i² ≥ M²`, hence the H¹ weight dominates `4 π² M²` and the spectral
estimate follows.
-/

open scoped BigOperators ComplexConjugate Real

namespace ℓ2ZD

open ℓ2ZD

/-! ## Tail geometry -/

/-- Real-valued tail: outside the Euclidean ball of radius `M`. -/
def tailR {d : ℕ} (M : ℝ) (k : Lattice d) : Prop :=
  M^2 < normSq k

lemma tailR_weight_lower {d : ℕ} {M : ℝ} {k : Lattice d}
    (_hM : 0 < M) (hk : tailR (d:=d) M k) :
    4 * Real.pi^2 * M^2 ≤ h1Weight k := by
  unfold tailR at hk
  have hle : M^2 ≤ normSq k := le_of_lt hk
  unfold h1Weight
  have := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 4 * Real.pi^2)
  linarith

/-! ## Main tail bound -/

/-- **Dimension-free tail bound (finitary version)**

    For any finite set F of tail frequencies (outside [-M,M]ᵈ):
    ∑_{k ∈ F} ‖aₖ‖² ≤ R² / (4π²M²)

    This is the elementary spectral estimate that makes the entire workflow possible.
    It is **dimension-free**: the bound is identical in 1D, 2D, 3D, ..., d-D.

    PROOF STRATEGY:
    1. Each k in tail has normSq k ≥ M², hence h1Weight(k) ≥ 4π²M²
    2. From H¹ bound: h1Weight(k) · ‖aₖ‖² ≤ R²
    3. Therefore: ‖aₖ‖² ≤ R² / h1Weight(k) ≤ R² / (4π²M²)
    4. Sum over F: ∑ ‖aₖ‖² ≤ |F| · R² / (4π²M²)
    5. But we can do better: sum of weighted terms gives single R²/(4π²M²) bound
-/
theorem tail_bound_finitary_d
  {d : ℕ} [NeZero d] {R M : ℝ} {x : SeqD d}
  (hH1 : InH1Ball R x) (hM : 0 < M)
  (F : Finset {k : Lattice d // tailR (d:=d) M k}) :
  ∑ k ∈ F, ‖x.a k.1‖^2 ≤ R^2 / (4 * Real.pi^2 * M^2) := by
  classical
  -- Abbreviate the positive constant c = 4π² M²
  set c : ℝ := 4 * Real.pi^2 * M^2 with hc
  have c_pos : 0 < c := by positivity
  have c_nonneg : 0 ≤ c := le_of_lt c_pos

  -- Pointwise: c ≤ h1Weight(k) on the tail
  have h_lb : ∀ k ∈ F, c ≤ h1Weight k.1 := by
    intro k hk
    simpa [hc] using tailR_weight_lower (d:=d) hM k.property

  -- Per term: c * s ≤ h1Weight * s
  have per : ∀ k ∈ F,
      c * ‖x.a k.1‖^2 ≤ h1Weight k.1 * ‖x.a k.1‖^2 := by
    intro k hk
    refine mul_le_mul_of_nonneg_right (h_lb k hk) (by positivity)

  -- Sum the per-term bounds
  have h_mul_sum :
      c * ∑ k ∈ F, ‖x.a k.1‖^2
      ≤ ∑ k ∈ F, h1Weight k.1 * ‖x.a k.1‖^2 := by
    simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using
      Finset.sum_le_sum per

  -- Convert weighted sum over subtype to sum over image
  have inj_on : Set.InjOn Subtype.val (F : Set {k : Lattice d // tailR M k}) := by
    intro a ha b hb h
    apply Subtype.ext
    exact h
  have sum_image :
      ∑ k ∈ F, h1Weight k.1 * ‖x.a k.1‖^2
        = ∑ k ∈ F.image Subtype.val, h1Weight k * ‖x.a k‖^2 := by
    classical
    rw [Finset.sum_image inj_on]

  -- Apply H¹ bound
  have hH1_image : ∑ k ∈ F.image Subtype.val, h1Weight k * ‖x.a k‖^2 ≤ R^2 :=
    hH1 (F.image Subtype.val)

  -- Final calculation
  have step1 : (∑ k ∈ F, ‖x.a k.1‖^2) * c ≤ ∑ k ∈ F, h1Weight k.1 * ‖x.a k.1‖^2 := by
    convert h_mul_sum using 1; ring

  have step2 : ∑ k ∈ F, h1Weight k.1 * ‖x.a k.1‖^2
                = ∑ k ∈ F.image Subtype.val, h1Weight k * ‖x.a k‖^2 := sum_image

  calc
    ∑ k ∈ F, ‖x.a k.1‖^2
        ≤ (∑ k ∈ F, h1Weight k.1 * ‖x.a k.1‖^2) / c := by
          rw [le_div_iff₀ (by positivity : 0 < c)]
          convert step1 using 1
    _ = (∑ k ∈ F.image Subtype.val, h1Weight k * ‖x.a k‖^2) / c := by
          rw [step2]
    _ ≤ R^2 / c := by
          apply div_le_div_of_nonneg_right hH1_image c_nonneg
    _ = R^2 / (4 * Real.pi^2 * M^2) := by rw [hc]

/-! ## Tail bound with M_of -/

/-- M_of is positive (key for positivity of M in tail bound) -/
lemma M_of_pos (ε R : ℚ) (hε : 0 < ε) (hR : 0 < R) : 0 < M_of ε R := by
  unfold M_of
  have : 0 < R / (Real.pi * ε) := by
    apply div_pos
    · exact_mod_cast hR
    · apply mul_pos Real.pi_pos
      exact_mod_cast hε
  have : 0 ≤ Nat.ceil (R / (Real.pi * ε)) := Nat.zero_le _
  omega

/-- Conservative lower bound for π (used in tail bound) -/
def pi_rat_lb : ℚ := 3

/-- **Tail bound holds with M_of choice (dimension-free!)**

    When M = M_of ε R, the tail bound yields exactly (ε/2)²:
    R² / (4π²M²) ≤ (ε/2)²

    This is the same formula in every dimension.

    PROOF STRATEGY:
    1. M = ⌈R/(πε)⌉ + 1, so M > R/(πε)
    2. Therefore: 2πM > 2R/ε
    3. Squaring: 4π²M² > 4R²/ε²
    4. Inverting: R²/(4π²M²) < ε²/4 = (ε/2)²
-/
lemma tail_bound_M_of_d {d : ℕ} [NeZero d] {ε R : ℚ}
    (hε : 0 < (ε : ℝ)) (hR : 0 < (R : ℝ)) :
    (R : ℝ)^2 / (4 * Real.pi^2 * (M_of ε R : ℝ)^2) ≤ ((ε : ℝ) / 2)^2 := by
  set M := M_of ε R with hM_def

  have hM_pi : (M : ℝ) > (R : ℝ) / (Real.pi * (ε : ℝ)) := by
    unfold M_of at hM_def
    calc (M : ℝ)
        = (Nat.ceil ((R : ℝ) / (Real.pi * (ε : ℝ))) + 1 : ℕ) := by simp [M, hM_def]
      _ = (Nat.ceil ((R : ℝ) / (Real.pi * (ε : ℝ))) : ℝ) + 1 := by norm_cast
      _ > (R : ℝ) / (Real.pi * (ε : ℝ)) := by
          have h_ceil : (R : ℝ) / (Real.pi * (ε : ℝ)) ≤ Nat.ceil ((R : ℝ) / (Real.pi * (ε : ℝ))) :=
            Nat.le_ceil _
          linarith

  have hM_scaled : 2 * Real.pi * (M : ℝ) > 2 * (R : ℝ) / (ε : ℝ) := by
    have h2 : Real.pi * (ε : ℝ) * (M : ℝ) > (R : ℝ) := by
      calc Real.pi * (ε : ℝ) * (M : ℝ)
          = (Real.pi * (ε : ℝ)) * (M : ℝ) := by ring
        _ > (Real.pi * (ε : ℝ)) * ((R : ℝ) / (Real.pi * (ε : ℝ))) := by
            apply mul_lt_mul_of_pos_left hM_pi (by positivity)
        _ = (R : ℝ) := by field_simp
    calc 2 * Real.pi * (M : ℝ)
        = 2 * (Real.pi * (M : ℝ)) := by ring
      _ > 2 * ((R : ℝ) / (ε : ℝ)) := by
          apply mul_lt_mul_of_pos_left _ (by norm_num)
          calc Real.pi * (M : ℝ)
              = (Real.pi * (ε : ℝ) * (M : ℝ)) / (ε : ℝ) := by field_simp
            _ > (R : ℝ) / (ε : ℝ) := by exact div_lt_div_of_pos_right h2 hε
      _ = 2 * (R : ℝ) / (ε : ℝ) := by ring

  have tail_bd : (R : ℝ)^2 / (4 * Real.pi^2 * (M : ℝ)^2) < ((ε : ℝ) / 2)^2 := by
    have denom_eq : 4 * Real.pi^2 * (M : ℝ)^2 = (2 * Real.pi * (M : ℝ))^2 := by ring
    rw [denom_eq]
    have h_sq : (2 * (R : ℝ) / (ε : ℝ))^2 < (2 * Real.pi * (M : ℝ))^2 := by
      have h1 : 0 < 2 * (R : ℝ) / (ε : ℝ) := by positivity
      have h2 : 0 < 2 * Real.pi * (M : ℝ) := by
        have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
        have hM_pos : 0 < (M : ℕ) := M_of_pos ε R (Rat.cast_pos.mp hε) (Rat.cast_pos.mp hR)
        have : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
        apply mul_pos (mul_pos (by norm_num) hpi) this
      have h3 := hM_scaled
      have h_diff : 0 < 2 * Real.pi * (M : ℝ) - 2 * (R : ℝ) / (ε : ℝ) := by linarith
      nlinarith [h1, h2, h_diff, sq_nonneg (2 * Real.pi * (M : ℝ) - 2 * (R : ℝ) / (ε : ℝ))]
    calc (R : ℝ)^2 / ((2 * Real.pi * (M : ℝ))^2)
        < (R : ℝ)^2 / ((2 * (R : ℝ) / (ε : ℝ))^2) := by
          apply div_lt_div_of_pos_left (sq_pos_of_pos hR) (sq_pos_of_pos (by positivity)) h_sq
      _ = (R : ℝ)^2 / (4 * (R : ℝ)^2 / (ε : ℝ)^2) := by congr 1; ring
      _ = ((ε : ℝ) / 2)^2 := by field_simp; ring
  exact le_of_lt tail_bd

end ℓ2ZD
