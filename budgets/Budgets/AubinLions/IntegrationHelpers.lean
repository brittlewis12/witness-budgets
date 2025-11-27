import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Order.DenselyOrdered

namespace AubinLions.IntegrationHelpers

open MeasureTheory Set

/-- If f ≤ g almost everywhere on a set, then their integrals satisfy the same inequality.
This is mathematically standard (see any measure theory textbook on monotone integration).
We delegate the proof to indicator functions and integral monotonicity lemmas in mathlib. -/
lemma integral_on_le_of_ae_le
    {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : IntegrableOn f s volume)
    (hg : IntegrableOn g s volume)
    (hs : MeasurableSet s)  -- Added for simplicity
    (hfg : ∀ᵐ t ∂volume, t ∈ s → f t ≤ g t) :
    ∫ t in s, f t ∂volume ≤ ∫ t in s, g t ∂volume := by
  exact setIntegral_mono_on_ae hf hg hs hfg

/-- A bounded, almost everywhere strongly measurable function on a finite-measure set
is integrable. This is a standard measure theory fact that follows from boundedness
and measurability: bounded functions are integrable on finite-measure sets. -/
lemma integrable_of_aestronglyMeasurable_bounded
    {f : ℝ → ℝ} {s : Set ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict s))
    (hms : MeasurableSet s)
    (hbound : ∃ C, ∀ t ∈ s, |f t| ≤ C)
    (hs : volume s < ⊤) :
    IntegrableOn f s volume := by
  obtain ⟨C, hC⟩ := hbound
  -- Use the indicator function interpretation of IntegrableOn
  -- For a measurable set s, IntegrableOn f s means the indicator function is integrable
  have h_norm_bound : ∀ᵐ x ∂(volume.restrict s), ‖f x‖ ≤ |C| := by
    -- With MeasurableSet s, we can use ae_restrict_mem
    filter_upwards [ae_restrict_mem hms] with x hx_in_s
    calc ‖f x‖
        = |f x| := Real.norm_eq_abs (f x)
      _ ≤ C := hC x hx_in_s
      _ ≤ |C| := le_abs_self C
  exact IntegrableOn.of_bound hs hf (|C|) h_norm_bound

/-- The integral over a finite union of pairwise a.e.-disjoint measurable sets
equals the sum of integrals. This follows from the standard additivity property
of the Lebesgue integral. -/
lemma integral_finset_union
    {ι : Type*} [Fintype ι] {f : ℝ → ℝ}
    {S : ι → Set ℝ}
    (hS_meas : ∀ i, MeasurableSet (S i))
    (hS_disj : Pairwise (fun i j => volume (S i ∩ S j) = 0))
    (hf : ∀ i, IntegrableOn f (S i) volume) :
    ∫ t in (⋃ i, S i), f t ∂volume = ∑ i, ∫ t in S i, f t ∂volume := by
  -- Convert to a.e. disjoint
  have hS_disj' : Pairwise (Function.onFun (AEDisjoint volume) S) := fun i j hij => hS_disj hij
  -- Get integrability on the union
  haveI : Finite ι := Fintype.finite inferInstance
  have hf_union : IntegrableOn f (⋃ i, S i) volume := integrableOn_finite_iUnion.mpr hf
  -- Use the a.e. version of the union integral formula
  rw [integral_iUnion_ae (fun i => (hS_meas i).nullMeasurableSet) hS_disj' hf_union]
  -- Convert from tsum to finsum
  simp only [tsum_fintype]

/-- The boundary (frontier) of a closed interval [a,b] with a < b has measure zero.
The frontier consists of exactly two points {a, b}, and singletons have measure zero
in the Lebesgue measure. -/
lemma measure_frontier_Icc_zero {a b : ℝ} (h : a < b) :
    volume (frontier (Set.Icc a b)) = 0 := by
  rw [frontier_Icc h.le]
  exact measure_union_null (measure_singleton a) (measure_singleton b)

end AubinLions.IntegrationHelpers
