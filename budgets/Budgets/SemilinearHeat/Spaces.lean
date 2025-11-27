import Budgets.SemilinearHeat.SobolevSeq
import Budgets.RellichKondrachovInterval
import Budgets.AubinLions

/-!
# Semilinear Heat PDE (1D) – Space/measure aliases and Aubin–Lions wrapper

This module records the basic objects that will be reused throughout the
semilinear heat development:

* spatial domain/measure on `[0,1]` (re-exporting the QRK notation),
* sequence-based models for `H := L²(0,1)`, `X := H₀¹(0,1)`, `Y := H⁻¹(0,1)`,
* convenient aliases for budget/admissible data coming from the
  quantitative Aubin–Lions infrastructure,
* a 1D wrapper around `AubinLions.quantitative_aubin_lions` that we will
  invoke later once the Galerkin approximations are in place.

Everything is kept purely algebraic (sequence model) so that subsequent files
can focus on PDE-specific arguments without re-deriving the generic witnesses.
-/

open MeasureTheory Set

namespace SemilinearHeat

open RellichKondrachovInterval AubinLions

noncomputable section

/-- Spatial dimension for the `(0,1)` interval problem. -/
@[simp] lemma spatialDim_coe : (spatialDim : ℕ) = 1 := rfl

/-- Closed unit interval `[0,1]` viewed as the PDE domain. -/
def domain : Set ℝ := interval01Set

/-- Notation for the spatial domain. -/
notation "Ω₁" => SemilinearHeat.domain

@[simp] lemma mem_domain {x : ℝ} : x ∈ domain ↔ 0 ≤ x ∧ x ≤ 1 := Iff.rfl

/-- Lebesgue measure restricted to `[0,1]`. -/
def spatialMeasure : Measure ℝ := mu01

/-- Notation for the restricted measure. -/
notation "μ₀₁" => SemilinearHeat.spatialMeasure

/-- Alias for the Hilbert space `H = L²(0,1)` in the sequence model. -/
@[reducible] def HSpace : Type := DirichletSeq

/-- Alias for the Sobolev space `X = H₀¹(0,1)` in the sequence model. -/
@[reducible] def XSpace : Type := H1Seq

/-- Alias for the dual space `Y = H⁻¹(0,1)` in the sequence model. -/
@[reducible] def YSpace : Type := Hminus1Seq

/-- Canonical embedding `X → H`. -/
@[simp] def embedXtoH : XSpace → HSpace := fun u => u.toSeqD

/-- Canonical embedding `H → Y`. -/
@[simp] def embedHtoY : HSpace → YSpace := fun u => DirichletSeq.toHminus u

@[simp] lemma embedXtoH_apply (u : XSpace) : embedXtoH u = u.toSeqD := rfl

@[simp] lemma embedHtoY_apply (u : HSpace) : (embedHtoY u).coeff = u.a := rfl

/-- Alias for the Aubin–Lions budget parameters (ε, R, S, T). -/
abbrev Params := BudgetParams

/-- Alias for the admissible curves specialized to the interval dimension. -/
abbrev Curve (P : Params) := Admissible spatialDim P

abbrev TimeGrid := AubinLions.TimeGrid

/-- Specialized 1D version of the quantitative Aubin–Lions theorem. -/
theorem quantitative_aubin_lions_interval
    (P : Params) (A : Curve P) (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    (hsegments : 0 < tg.segments)
    (hbudget : (tg.segments : ℝ) * ((timeModulusIntegralConstant
        (d := spatialDim) (ℓ2ZD.M_of P.ε P.R) : ℝ) * (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2) +
        2 * ((tg.mesh : ℚ) : ℝ) * (tg.segments : ℝ) * (P.ε : ℝ)^2
      ≤ (P.ε : ℝ)^2) :
    (∫ t in Set.Icc (0 : ℝ) (P.horizon : ℝ),
        Finset.sum (ℓ2ZD.cube spatialDim (ℓ2ZD.M_of P.ε P.R)) (fun k =>
          ‖(curveExtended P A t).a k -
            (witnessAtTime' P A tg hcompat t).a k‖^2) : ℝ)
      ≤ (P.ε : ℝ)^2 := by
  simpa [spatialDim] using
    (AubinLions.quantitative_aubin_lions (d := spatialDim)
        P A tg hcompat hsegments hbudget)

end

end SemilinearHeat
