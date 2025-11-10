import Budgets.RellichKondrachov1D
import Budgets.RellichKondrachov1D.Seq

/-!
# L2Bridge: connecting L² functions to constructive Fourier sequences

`Seq.lean` works with explicit Fourier coefficient sequences `ℓ2Z`, while
`RellichKondrachov1D.lean` states the classical theorem for bona fide
functions in `L2_Torus1`.  This file links the two viewpoints:

* construct `L2_to_seq : L2_Torus1 → ℓ2Z`,
* show Parseval (`L2_seq_isometry`) and the induced distance identity,
* prove that mean-zero / H¹-ball hypotheses transfer to the sequence layer, and
* restate the constructive witness theorem so it can be invoked directly
  on analytic inputs.

All statements here are `noncomputable`: they live entirely in the proof layer
and do not affect the extractable `WitnessPkg` defined in `Seq.lean`.
-/

open scoped BigOperators ComplexConjugate

namespace RellichKondrachov1D
namespace L2Bridge

open RellichKondrachov1D
open RellichKondrachov1D.Seq
open RellichKondrachov1D.Seq.ℓ2Z

noncomputable section

/-- Map an L² function on the torus to its Fourier coefficient sequence. -/
def L2_to_seq (u : L2_Torus1) : ℓ2Z where
  a := fun k => fourierCoeff u k
  summable_sq := by
    classical
    have _ : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
    simpa using (hasSum_sq_fourierCoeff (T := (1 : ℝ)) (f := u)).summable

/-- Parseval (squared) for the coefficient sequence. -/
lemma L2_seq_isometry (u : L2_Torus1) :
    ‖u‖^2 = ∑' k : ℤ, ‖(L2_to_seq u).a k‖^2 := by
  classical
  have _ : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have parseval :=
    tsum_sq_fourierCoeff (T := (1 : ℝ)) (f := u)
  have norm_eq := L2_sqNorm_eq_integral_sq u
  have : ∑' k : ℤ, ‖fourierCoeff u k‖^2 = ‖u‖^2 := by
    simpa [norm_eq] using parseval
  simpa [L2_to_seq] using this.symm

/-- Mean-zero is preserved when passing to sequences. -/
lemma bridge_preserves_mean_zero (u : L2_Torus1) (h : u ∈ MeanZeroL2) :
    (L2_to_seq u).meanZero := by
  unfold L2_to_seq ℓ2Z.meanZero
  exact (meanZero_iff_fourierCoeff_zero_eq_zero u).mp h

private def h1Weight (u : L2_Torus1) (k : ℤ) : ℝ :=
  (1 + (2 * Real.pi * (k : ℝ))^2) * ‖fourierCoeff u k‖^2

private lemma h1Weight_nonneg (u : L2_Torus1) (k : ℤ) :
    0 ≤ h1Weight u k := by
  have hk : 0 ≤ (2 * Real.pi * (k : ℝ))^2 := by exact sq_nonneg _
  have hcoeff : 0 ≤ 1 + (2 * Real.pi * (k : ℝ))^2 :=
    add_nonneg zero_le_one hk
  exact mul_nonneg hcoeff (sq_nonneg _)

private lemma h1Weight_sum_eq (u : L2_Torus1) (F : Finset ℤ) :
    ENNReal.ofReal (∑ k ∈ F, h1Weight u k) =
      ∑ k ∈ F, ENNReal.ofReal (h1Weight u k) := by
  classical
  refine ENNReal.ofReal_sum_of_nonneg
      (s := F) (f := fun k => h1Weight u k) ?_
  intro k hk
  exact h1Weight_nonneg u k

private lemma H1normSq_le_of_bound
    {u : L2_Torus1} {R : ℝ} (hR : 0 ≤ R) (h : InH1Ball R u) :
    H1normSq u ≤ ENNReal.ofReal (R^2) := by
  have hfin := h.1
  have hnorm := h.2
  have hsq :
      (H1norm u)^2 ≤ R^2 := by
    have hunonneg := H1norm_nonneg u
    have := (sq_le_sq₀ hunonneg hR).2 hnorm
    simpa [sq] using this
  have hnonneg_toReal : 0 ≤ (H1normSq u).toReal :=
    ENNReal.toReal_nonneg
  have hsq_eq :
      (H1norm u)^2 = (H1normSq u).toReal := by
    unfold H1norm
    exact Real.sq_sqrt hnonneg_toReal
  have htoReal :
      (H1normSq u).toReal ≤ R^2 := by
    simpa [hsq_eq] using hsq
  have hx : H1normSq u = ENNReal.ofReal ((H1normSq u).toReal) :=
    (ENNReal.ofReal_toReal hfin).symm
  have hRsq : 0 ≤ R^2 := sq_nonneg R
  have hcoer :
      ENNReal.ofReal ((H1normSq u).toReal) ≤ ENNReal.ofReal (R^2) :=
    (ENNReal.ofReal_le_ofReal_iff hRsq).2 htoReal
  calc H1normSq u
      = ENNReal.ofReal ((H1normSq u).toReal) := hx
    _ ≤ ENNReal.ofReal (R^2) := hcoer

/-- The H¹ ball condition transfers to the constructive sequence layer. -/
lemma bridge_preserves_H1Ball
    (u : L2_Torus1) {R : ℝ} (hR : 0 ≤ R) (h : InH1Ball R u) :
    (L2_to_seq u).InH1Ball R := by
  classical
  constructor
  intro F
  have hsum_le :
      ENNReal.ofReal (∑ k ∈ F, h1Weight u k) ≤ H1normSq u := by
    calc ENNReal.ofReal (∑ k ∈ F, h1Weight u k)
        = ∑ k ∈ F, ENNReal.ofReal (h1Weight u k) := h1Weight_sum_eq u F
      _ ≤ ∑' k : ℤ, ENNReal.ofReal (h1Weight u k) :=
          ENNReal.sum_le_tsum (s := F) (f := fun k => ENNReal.ofReal (h1Weight u k))
      _ = H1normSq u := rfl
  have hupper := H1normSq_le_of_bound hR h
  have htotal :
      (∑ k ∈ F, h1Weight u k) ≤ R^2 := by
    have := le_trans hsum_le hupper
    have hRsq : 0 ≤ R^2 := sq_nonneg R
    exact (ENNReal.ofReal_le_ofReal_iff hRsq).1 this
  convert htotal using 1

/-- Parseval also yields a distance identity for differences. -/
lemma bridge_preserves_distance (u v : L2_Torus1) :
    ‖u - v‖^2 =
      ∑' k : ℤ, ‖(L2_to_seq u).a k - (L2_to_seq v).a k‖^2 := by
  classical
  have h := L2_seq_isometry (u - v)
  have hfun :
      (fun k => ‖(L2_to_seq (u - v)).a k‖^2)
        = (fun k => ‖(L2_to_seq u).a k - (L2_to_seq v).a k‖^2) := by
    funext k
    have hk :
        (L2_to_seq (u - v)).a k =
          (L2_to_seq u).a k - (L2_to_seq v).a k := by
      change fourierCoeff (u - v) k = fourierCoeff u k - fourierCoeff v k
      simpa using fourierCoeff_sub' u v k
    simp [hk]
  simpa [hfun] using h

/-- Finite partial sums of the coefficient distance are bounded by the L² distance. -/
lemma bridge_distance_finitary (u v : L2_Torus1) (F : Finset ℤ) :
    Finset.sum F (fun k => ‖(L2_to_seq u).a k - (L2_to_seq v).a k‖^2)
      ≤ ‖u - v‖^2 := by
  classical
  have hsumm :
      Summable (fun k : ℤ =>
        ‖(L2_to_seq u).a k - (L2_to_seq v).a k‖^2) := by
    have := (L2_to_seq (u - v)).summable_sq
    have hfun :
        (fun k => ‖(L2_to_seq (u - v)).a k‖^2)
          = (fun k => ‖(L2_to_seq u).a k - (L2_to_seq v).a k‖^2) := by
      funext k
      have hk :
          (L2_to_seq (u - v)).a k =
            (L2_to_seq u).a k - (L2_to_seq v).a k := by
        change fourierCoeff (u - v) k = fourierCoeff u k - fourierCoeff v k
        simpa using fourierCoeff_sub' u v k
      simp [hk]
    simpa [hfun] using this
  have htotal := bridge_preserves_distance u v
  have hsum :=
      hsumm.sum_le_tsum (s := F)
        (by intro k hk; exact sq_nonneg _)
  simpa [htotal] using hsum

/-- Restatement: the constructive witness works directly for L² inputs. -/
lemma witness_soundness_via_bridge
    (ε R : ℚ) (hε : 0 < (ε : ℝ)) (hR : 0 < (R : ℝ))
    (u : L2_Torus1) (hmean : u ∈ MeanZeroL2)
    (hH1 : InH1Ball (R : ℝ) u) :
    ∃ (g : ℓ2Z.GridPoint ε R (ℓ2Z.M_of ε R)),
      g ∈ ℓ2Z.gridFinset ε R (ℓ2Z.M_of ε R) ∧
      ∀ F : Finset ℤ,
        Finset.sum F
          (fun k => ‖(L2_to_seq u).a k - (ℓ2Z.gridToSeq ε R (ℓ2Z.M_of ε R) g).a k‖^2)
          < (ε : ℝ)^2 := by
  classical
  have h_seq_mean := bridge_preserves_mean_zero u hmean
  have h_seq_H1 := bridge_preserves_H1Ball u hR.le hH1
  have := ℓ2Z.gridFinset_sound ε R hε hR (L2_to_seq u) h_seq_mean h_seq_H1
  exact this

end

end RellichKondrachov1D.L2Bridge
