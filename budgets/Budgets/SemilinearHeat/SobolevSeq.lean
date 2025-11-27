import Budgets.RellichKondrachovD.Core

/-!
# Semilinear Heat PDE (1D) – Sobolev sequence models

This file refines the base `SeqD` sequence model with the weighted summability
assumptions corresponding to H¹ and H⁻¹ Sobolev norms.  The resulting types
will be used as the `X`/`Y` spaces in the Aubin–Lions triple for the
semilinear heat equation.
-/

namespace SemilinearHeat

open scoped BigOperators
open ℓ2ZD

noncomputable section

/-- Fixed spatial dimension for the `(0,1)` Dirichlet problem. -/
@[reducible] def spatialDim : ℕ := 1

instance : NeZero spatialDim := ⟨by decide⟩

/-- Base ℓ² sequence model (L² on the interval). -/
@[reducible] def DirichletSeq : Type := SeqD spatialDim

/-- H¹ sequences: L² sequences whose weighted energy is finite. -/
structure H1Seq extends SeqD spatialDim where
  summable_h1 : Summable (fun k => h1Weight k * ‖toSeqD.a k‖^2)

namespace H1Seq

@[simp] def coeff (u : H1Seq) : Lattice spatialDim → ℂ :=
  u.toSeqD.a

lemma summable_sq_coeff (u : H1Seq) :
    Summable (fun k => ‖u.coeff k‖^2) :=
  u.toSeqD.summable_sq

lemma summable_h1_coeff (u : H1Seq) :
    Summable (fun k => h1Weight k * ‖u.coeff k‖^2) :=
  u.summable_h1

end H1Seq

/-- H⁻¹ sequences: weighted ℓ² with the reciprocal weight. -/
structure Hminus1Seq where
  coeff : Lattice spatialDim → ℂ
  summable_hminus : Summable (fun k => hminusWeight k * ‖coeff k‖^2)

namespace Hminus1Seq

lemma summable_hminus_coeff (u : Hminus1Seq) :
    Summable (fun k => hminusWeight k * ‖u.coeff k‖^2) :=
  u.summable_hminus

end Hminus1Seq

/-- Every Dirichlet sequence determines a H⁻¹ sequence since
`hminusWeight ≤ 1` makes the weighted sum converge. -/
lemma summable_hminus_of_dirichlet (u : DirichletSeq) :
    Summable (fun k => hminusWeight k * ‖u.a k‖^2) := by
  classical
  refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (hminusWeight_nonneg _)
      (sq_nonneg _)) (fun k => ?_) u.summable_sq
  have hle : hminusWeight k ≤ 1 := hminusWeight_le_one (d := spatialDim) k
  have hnonneg : 0 ≤ ‖u.a k‖^2 := sq_nonneg _
  have := mul_le_mul_of_nonneg_right hle hnonneg
  simpa using this

/-- Canonical embedding from L² to H⁻¹. -/
def DirichletSeq.toHminus (u : DirichletSeq) : Hminus1Seq where
  coeff := u.a
  summable_hminus := summable_hminus_of_dirichlet u

end

end SemilinearHeat
