import Budgets.RellichKondrachovInterval.Core
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-
# Lebesgue measure restricted to `[0,1]`

This auxiliary file packages the restricted Lebesgue measure on the closed unit
interval so later files (Lp/Sobolev) can refer to it via the shorthand `μ₀₁`.
-/

open MeasureTheory Set
open scoped MeasureTheory Interval

namespace RellichKondrachovInterval

noncomputable section

def mu01 : Measure ℝ := Measure.restrict (volume : Measure ℝ) interval01Set

lemma interval01_measurable :
    MeasurableSet interval01Set := by
  simp [interval01Set]

lemma mu01_interval :
    mu01 interval01Set = (1 : ENNReal) := by
  have hmeas := interval01_measurable
  have hrestrict :
      mu01 interval01Set = volume interval01Set := by
    have hstep :
        mu01 interval01Set = volume (interval01Set ∩ interval01Set) := by
      simp [mu01] -- using
        -- (measure.restrict_apply (μ := volume) (s := interval01set)
        --   (t := interval01set) hmeas)
    convert hstep using 1
    simp [interval01Set]
  have hfinal :
      volume interval01Set = (1 : ENNReal) := by
    simp [interval01Set, Real.volume_Icc]
  exact hrestrict.trans hfinal

lemma mu01_compl : mu01 (interval01Setᶜ) = (0 : ENNReal) := by
  have hmeas := interval01_measurable
  have hrestrict :
      mu01 (interval01Setᶜ) = volume (interval01Setᶜ ∩ interval01Set) := by
    have hcompl : MeasurableSet (interval01Setᶜ) := hmeas.compl
    simpa [mu01] using
      (Measure.restrict_apply (μ := volume) (s := interval01Set)
        (t := interval01Setᶜ) hcompl)
  have hzero : volume (interval01Setᶜ ∩ interval01Set) = 0 := by
    simp [interval01Set]
  exact hrestrict.trans hzero

end

end RellichKondrachovInterval
