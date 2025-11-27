import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Order.Lattice
import Budgets.AubinLions.TimeGridAPI
import Budgets.AubinLions.Core
import Budgets.RellichKondrachovD.Soundness
import Budgets.RellichKondrachovInterval.Measure
import Budgets.ConstructiveQ

/-!
# Integration Lemmas for Quantitative Aubin-Lions

This module provides basic integration lemmas for constant functions on time slabs,
used in Phase 3 of the Quantitative Aubin-Lions theorem.

## Main lemmas

* `integral_const_Icc`: Integration of scalar constant over [a,b]
* `integral_const_norm_sq_Icc`: Integration of ‖x‖² (constant norm) over [a,b]
* `integral_const_slab`: Integration of constant over time slab

## Strategy

We work with scalar-valued functions (ℝ) rather than attempting Bochner integration
in the SeqD space directly. This matches the coefficient-wise approach established
in Witness.lean.
-/

namespace AubinLions

open MeasureTheory Set
open scoped ENNReal

section ScalarIntegration

/-- Integration of a scalar constant over a closed interval [a,b]. -/
lemma integral_const_Icc (a b : ℝ) (h : a ≤ b) (c : ℝ) :
    ∫ _ in Set.Icc a b, c ∂volume = (b - a) * c := by
  rw [setIntegral_const]
  rw [Real.volume_real_Icc_of_le h]
  rw [smul_eq_mul]

/-- Integration of ‖x‖² (constant) over a closed interval [a,b].
This is just `integral_const_Icc` specialized to the case where c represents a squared norm. -/
lemma integral_const_norm_sq_Icc (a b : ℝ) (h : a ≤ b) (c : ℝ) :
    ∫ _ in Set.Icc a b, c ∂volume = (b - a) * c :=
  integral_const_Icc a b h c

end ScalarIntegration

section SlabIntegration

/-- Integration of a constant over a time slab equals mesh * constant. -/
lemma integral_const_slab (tg : TimeGrid) (i : Fin tg.segments) (c : ℝ) :
    ∫ _ in TimeGrid.slabReal tg i, c ∂volume = ((tg.mesh : ℚ) : ℝ) * c := by
  unfold TimeGrid.slabReal
  have h_le : ((tg.endpoint i.castSucc : ℚ) : ℝ) ≤ ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ) := by
    have := TimeGrid.endpoint_le_succ tg i
    exact_mod_cast this
  rw [integral_const_Icc _ _ h_le]
  have h_length := TimeGrid.slabReal_length tg i
  rw [mul_comm, ← h_length]
  ring

/-- Integration of the squared norm of a constant vector over a slab. -/
lemma integral_const_norm_sq_slab {E : Type*} [SeminormedAddCommGroup E]
    (tg : TimeGrid) (i : Fin tg.segments) (v : E) :
    ∫ _ in TimeGrid.slabReal tg i, ‖v‖^2 ∂volume
      = ((tg.mesh : ℚ) : ℝ) * ‖v‖^2 := by
  exact integral_const_slab tg i (‖v‖^2)

end SlabIntegration

/-! ## Spatial integration over the unit interval -/

section SpatialIntegration

open RellichKondrachovInterval

lemma integral_const_unit_interval (c : ℝ) :
    ∫ _ in interval01Set, c ∂mu01 = c := by
  have hconst :
      ∫ _ in interval01Set, c ∂mu01
        = (mu01 interval01Set).toReal • c :=
    setIntegral_const (μ := mu01) (s := interval01Set) (c := c)
  have htoReal :
      (mu01 interval01Set).toReal = 1 := by
    simp [mu01_interval, ENNReal.toReal_one]
  simpa [htoReal, smul_eq_mul] using hconst

lemma integral_const_norm_sq_unit_interval {E : Type*}
    [SeminormedAddCommGroup E] (v : E) :
    ∫ _ in interval01Set, ‖v‖^2 ∂mu01 = ‖v‖^2 := by
  simpa using integral_const_unit_interval (‖v‖^2)

end SpatialIntegration

section TimeModulusBounds

/-! ### Helper lemmas for time-modulus integration -/

/-- Helper lemma: a time t in a slab is within the horizon interval. -/
lemma slab_mem_interval (tg : TimeGrid) {P : BudgetParams} (hcompat : tg.horizon = P.horizon)
    (i : Fin tg.segments) (t : ℝ) (ht : t ∈ TimeGrid.slabReal tg i) :
    t ∈ Set.Icc (0 : ℝ) (P.horizon : ℝ) := by
  unfold TimeGrid.slabReal at ht
  have h_left : 0 ≤ ((tg.endpoint i.castSucc : ℚ) : ℝ) := by
    have : tg.endpoint 0 ≤ tg.endpoint i.castSucc :=
      TimeGrid.endpoint_mono tg (Fin.zero_le i.castSucc)
    calc 0 = ((tg.endpoint 0 : ℚ) : ℝ) := by simp [TimeGrid.endpoint_zero tg]
         _ ≤ ((tg.endpoint i.castSucc : ℚ) : ℝ) := by exact_mod_cast this
  have h_right : ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ) ≤ (P.horizon : ℝ) := by
    have : tg.endpoint (TimeGrid.rightIdx tg i) ≤ tg.endpoint (Fin.last tg.segments) := by
      apply TimeGrid.endpoint_mono tg
      unfold TimeGrid.rightIdx; exact Fin.le_last _
    calc ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ)
        ≤ ((tg.endpoint (Fin.last _) : ℚ) : ℝ) := by exact_mod_cast this
      _ = ((tg.horizon : ℚ) : ℝ) := by rw [TimeGrid.endpoint_last tg]
      _ = (P.horizon : ℝ) := by rw [← hcompat]
  constructor
  · linarith [h_left, ht.1]
  · linarith [h_right, ht.2]

/-- The absolute difference between a time t in slab i and the node time is
bounded by the mesh size. -/
lemma time_diff_le_mesh (tg : TimeGrid) (i : Fin tg.segments)
    (t : ℝ) (ht : t ∈ TimeGrid.slabReal tg i) :
    |t - ((tg.node i : ℚ) : ℝ)| ≤ ((tg.mesh : ℚ) : ℝ) := by
  unfold TimeGrid.slabReal at ht
  have h_cast := TimeGrid.endpoint_castSucc tg i
  have h_length := TimeGrid.slabReal_length tg i
  rw [h_cast] at ht h_length
  have ht_bounds : ((tg.node i : ℚ) : ℝ) ≤ t ∧
                    t ≤ ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ) := ht
  have h_diff_nonneg : 0 ≤ t - ((tg.node i : ℚ) : ℝ) := by linarith [ht_bounds.1]
  have h_diff_le : t - ((tg.node i : ℚ) : ℝ) ≤ ((tg.mesh : ℚ) : ℝ) := by
    calc t - ((tg.node i : ℚ) : ℝ)
        ≤ ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ) - ((tg.node i : ℚ) : ℝ) := by
          linarith [ht_bounds.2]
      _ = ((tg.mesh : ℚ) : ℝ) := h_length
  rw [abs_of_nonneg h_diff_nonneg]
  exact h_diff_le

/-- Integral of the linear function |t - a| over [a, a+h] equals h²/2. -/
lemma integral_abs_diff_Icc (a h : ℝ) (hh : 0 ≤ h) :
    ∫ t in Set.Icc a (a + h), |t - a| = h^2 / 2 := by
  -- For t ∈ [a, a+h] with h ≥ 0, we have t ≥ a, so |t - a| = t - a
  have h_abs : ∀ t ∈ Set.Icc a (a + h), |t - a| = t - a := by
    intro t ht
    exact abs_of_nonneg (by linarith [ht.1])
  -- Rewrite the integral using this simplification
  have step1 : ∫ t in Set.Icc a (a + h), |t - a| = ∫ t in Set.Icc a (a + h), (t - a) := by
    apply setIntegral_congr_fun measurableSet_Icc h_abs
  rw [step1]
  -- Convert Icc to Ioc (they're equal for Lebesgue measure)
  rw [integral_Icc_eq_integral_Ioc]
  -- Convert set integral to interval integral
  rw [← intervalIntegral.integral_of_le (by linarith : a ≤ a + h)]
  -- Use change of variables: ∫_{a}^{a+h} (t - a) dt = ∫_{0}^{h} u du
  rw [show (∫ t in a..(a + h), t - a) = ∫ u in 0..h, u by
    simp only [intervalIntegral.integral_comp_sub_right (fun x => x) a, sub_self]
    congr 1
    ring]
  -- Apply integral_id: ∫ u in 0..h, u = (h² - 0²) / 2
  rw [integral_id]
  ring

/-! ### Curve extension for integration -/

/-- Extension of the admissible curve to all of ℝ, zero outside [0, horizon].
This avoids dependent type issues in integrands. -/
noncomputable def curveExtended {d : ℕ} (P : BudgetParams) (A : Admissible d P) : ℝ → ℓ2ZD.SeqD d :=
  fun t => if h : t ∈ Set.Icc (0 : ℝ) (P.horizon : ℝ)
           then A.curve ⟨t, h⟩
           else zeroSeqD d

/-- The extended curve equals the original curve on slabs. -/
lemma curveExtended_eq_on_slab {d : ℕ} (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    (i : Fin tg.segments) (t : ℝ) (ht : t ∈ TimeGrid.slabReal tg i) :
    curveExtended P A t = A.curve ⟨t, slab_mem_interval tg hcompat i t ht⟩ := by
  unfold curveExtended
  have h_mem := slab_mem_interval tg hcompat i t ht
  simp only [dif_pos h_mem]

/-- Coefficient-level equality on slabs. -/
lemma curveExtended_coeff_eq_on_slab {d : ℕ} (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    (i : Fin tg.segments) (t : ℝ) (ht : t ∈ TimeGrid.slabReal tg i) (k : ℓ2ZD.Lattice d) :
    (curveExtended P A t).a k = (A.curve ⟨t, slab_mem_interval tg hcompat i t ht⟩).a k := by
  rw [curveExtended_eq_on_slab P A tg hcompat i t ht]

/-- Helper value: clamp a time into `[0, horizon]`. -/
private def horizonClampVal (P : BudgetParams) (t : ℝ) : ℝ :=
  min (max t 0) (P.horizon : ℝ)

private lemma horizonClampVal_mem (P : BudgetParams) (t : ℝ) :
    horizonClampVal P t ∈ Set.Icc (0 : ℝ) (P.horizon : ℝ) := by
  have h_max_nonneg : 0 ≤ max t 0 :=
    le_max_of_le_right (show 0 ≤ (0 : ℝ) from le_rfl)
  have h_hor_nonneg : 0 ≤ (P.horizon : ℝ) := le_of_lt P.horizon_pos
  have h_min_nonneg : 0 ≤ min (max t 0) (P.horizon : ℝ) :=
    le_min h_max_nonneg h_hor_nonneg
  exact ⟨h_min_nonneg, min_le_right _ _⟩

/-- Clamp a real time into `[0, horizon]`. -/
private noncomputable def horizonClamp (P : BudgetParams) (t : ℝ) :
    Set.Icc (0 : ℝ) (P.horizon : ℝ) :=
  ⟨horizonClampVal P t, horizonClampVal_mem P t⟩

private lemma horizonClamp_eq_self {P : BudgetParams} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (P.horizon : ℝ)) :
    horizonClamp P t = ⟨t, ht⟩ := by
  have hmax : max t 0 = t := max_eq_left ht.1
  have hmin : min (max t 0) (P.horizon : ℝ) = t := by
    calc
      min (max t 0) (P.horizon : ℝ)
          = min t (P.horizon : ℝ) := by simp [hmax]
      _ = t := min_eq_left ht.2
  apply Subtype.ext
  simp [horizonClamp, horizonClampVal, hmin]

private lemma horizonClamp_continuous (P : BudgetParams) :
    Continuous fun t : ℝ => horizonClamp P t := by
  classical
  refine Continuous.subtype_mk ?_ (fun t => horizonClampVal_mem P t)
  have hmax : Continuous fun t : ℝ => max t (0 : ℝ) :=
    continuous_id.max continuous_const
  have hmin : Continuous fun t : ℝ => min (max t 0) (P.horizon : ℝ) :=
    hmax.min continuous_const
  simpa [horizonClamp, horizonClampVal] using hmin

/-- Each coefficient of the extended curve is a.e. strongly measurable. -/
lemma curveExtended_coeff_aestronglyMeasurable {d : ℕ}
    (P : BudgetParams) (A : Admissible d P) (k : ℓ2ZD.Lattice d) :
    AEStronglyMeasurable (fun t : ℝ => (curveExtended P A t).a k) volume := by
  classical
  let g : ℝ → ℂ := fun t => (A.curve (horizonClamp P t)).a k
  have hg_cont : Continuous g :=
    (A.curve_coeff_continuous k).comp (horizonClamp_continuous P)
  have hg_meas : AEStronglyMeasurable g volume := hg_cont.aestronglyMeasurable
  have hset : MeasurableSet (Set.Icc (0 : ℝ) (P.horizon : ℝ)) := measurableSet_Icc
  have h_indicator :
      (fun t : ℝ => (curveExtended P A t).a k)
        = Set.indicator (Set.Icc (0 : ℝ) (P.horizon : ℝ)) g := by
    funext t
    classical
    by_cases ht : t ∈ Set.Icc (0 : ℝ) (P.horizon : ℝ)
    · have hclamp :
        horizonClamp P t = ⟨t, ht⟩ := horizonClamp_eq_self (P := P) ht
      simp [curveExtended, g, ht, Set.indicator_of_mem, hclamp]
    · simp [curveExtended, g, ht, Set.indicator_of_notMem]
  simpa [h_indicator] using (hg_meas.indicator hset)

/-! ### Main time-modulus bounds -/

/-- For any time t in a slab and finite set of lattice points F, the time-modulus
bound from the admissible curve provides a pointwise error estimate from the
node time. -/
lemma pointwise_time_modulus_bound
    {d : ℕ} (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    (i : Fin tg.segments) (t : ℝ) (ht : t ∈ TimeGrid.slabReal tg i)
    (F : Finset (ℓ2ZD.Lattice d)) :
    Finset.sum F (fun k => ℓ2ZD.hminusWeight k * ‖(A.curve ⟨t, by
      -- t is in slab i ⊆ [0, horizon]
      unfold TimeGrid.slabReal at ht
      have ht_bounds := ht
      have h_left : 0 ≤ ((tg.endpoint i.castSucc : ℚ) : ℝ) := by
        have : tg.endpoint 0 ≤ tg.endpoint i.castSucc :=
          TimeGrid.endpoint_mono tg (Fin.zero_le i.castSucc)
        calc 0 = ((tg.endpoint 0 : ℚ) : ℝ) := by simp [TimeGrid.endpoint_zero tg]
             _ ≤ ((tg.endpoint i.castSucc : ℚ) : ℝ) := by exact_mod_cast this
      have h_right : ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ) ≤ (P.horizon : ℝ) := by
        have : tg.endpoint (TimeGrid.rightIdx tg i) ≤ tg.endpoint (Fin.last tg.segments) := by
          apply TimeGrid.endpoint_mono tg
          unfold TimeGrid.rightIdx; exact Fin.le_last _
        calc ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ)
            ≤ ((tg.endpoint (Fin.last _) : ℚ) : ℝ) := by exact_mod_cast this
          _ = ((tg.horizon : ℚ) : ℝ) := by rw [TimeGrid.endpoint_last tg]
          _ = (P.horizon : ℝ) := by rw [← hcompat]
      constructor
      · linarith [h_left, ht_bounds.1]
      · linarith [h_right, ht_bounds.2]⟩).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)
      ≤ (P.S : ℝ)^2 * |t - ((tg.node i : ℚ) : ℝ)| := by
  -- Construct subtype elements
  have t_mem : t ∈ Set.Icc (0 : ℝ) (P.horizon : ℝ) := by
    unfold TimeGrid.slabReal at ht
    have ht_bounds := ht
    have h_left : 0 ≤ ((tg.endpoint i.castSucc : ℚ) : ℝ) := by
      have : tg.endpoint 0 ≤ tg.endpoint i.castSucc :=
        TimeGrid.endpoint_mono tg (Fin.zero_le i.castSucc)
      calc 0 = ((tg.endpoint 0 : ℚ) : ℝ) := by simp [TimeGrid.endpoint_zero tg]
           _ ≤ ((tg.endpoint i.castSucc : ℚ) : ℝ) := by exact_mod_cast this
    have h_right : ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ) ≤ (P.horizon : ℝ) := by
      have : tg.endpoint (TimeGrid.rightIdx tg i) ≤ tg.endpoint (Fin.last tg.segments) := by
        apply TimeGrid.endpoint_mono tg
        unfold TimeGrid.rightIdx; exact Fin.le_last _
      calc ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ)
          ≤ ((tg.endpoint (Fin.last _) : ℚ) : ℝ) := by exact_mod_cast this
        _ = ((tg.horizon : ℚ) : ℝ) := by rw [TimeGrid.endpoint_last tg]
        _ = (P.horizon : ℝ) := by rw [← hcompat]
    constructor
    · linarith [h_left, ht_bounds.1]
    · linarith [h_right, ht_bounds.2]

  have node_mem : ((tg.node i : ℚ) : ℝ) ∈ Set.Icc (0 : ℝ) (P.horizon : ℝ) := by
    constructor
    · have := TimeGrid.node_nonneg tg i; exact_mod_cast this
    · have := TimeGrid.node_le_horizon tg i
      calc ((tg.node i : ℚ) : ℝ) ≤ ((tg.horizon : ℚ) : ℝ) := by exact_mod_cast this
                                  _ = (P.horizon : ℝ) := by rw [← hcompat]

  set t_sub : Set.Icc (0 : ℝ) (P.horizon : ℝ) := ⟨t, t_mem⟩
  set node_sub : Set.Icc (0 : ℝ) (P.horizon : ℝ) := ⟨((tg.node i : ℚ) : ℝ), node_mem⟩

  -- Apply timeModulus
  by_cases h_order : ((tg.node i : ℚ) : ℝ) ≤ t
  · have h_abs : |t - ((tg.node i : ℚ) : ℝ)| = t - ((tg.node i : ℚ) : ℝ) :=
      abs_of_nonneg (by linarith)
    rw [h_abs]
    have h_sample : A.sampleAtNodes tg hcompat i = A.curve node_sub := by
      unfold Admissible.sampleAtNodes; simp [node_sub]
    rw [h_sample]
    have h_order_sub : (node_sub : ℝ) ≤ (t_sub : ℝ) := by simpa [node_sub, t_sub] using h_order
    convert A.timeModulus h_order_sub F using 2
  · have h_order' : t ≤ ((tg.node i : ℚ) : ℝ) := le_of_not_ge h_order
    have h_abs : |t - ((tg.node i : ℚ) : ℝ)| = ((tg.node i : ℚ) : ℝ) - t := by
      rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [h_abs]
    have h_sample : A.sampleAtNodes tg hcompat i = A.curve node_sub := by
      unfold Admissible.sampleAtNodes; simp [node_sub]
    rw [h_sample]
    have h_order_sub : (t_sub : ℝ) ≤ (node_sub : ℝ) := by simpa [node_sub, t_sub] using h_order'
    convert A.timeModulus h_order_sub F using 1
    congr 1; ext k
    congr 1
    rw [← norm_neg]; congr 1; ring_nf

/-- Integrating the pointwise time-modulus bound over a slab gives a bound
proportional to the slab length squared (mesh²). -/
lemma slab_integral_time_modulus_bound
    {d : ℕ} (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    (i : Fin tg.segments)
    (F : Finset (ℓ2ZD.Lattice d)) :
    ∫ t in TimeGrid.slabReal tg i,
      Finset.sum F (fun k => ℓ2ZD.hminusWeight k *
        ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)
      ≤ (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2 / 2 := by
  -- Step 0: Define integrand functions for clarity
  let f : ℝ → ℝ := fun t =>
    Finset.sum F (fun k =>
      ℓ2ZD.hminusWeight k *
        ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)

  let g : ℝ → ℝ := fun t =>
    (P.S : ℝ)^2 * |t - ((tg.node i : ℚ) : ℝ)|

  change ∫ t in TimeGrid.slabReal tg i, f t ≤ (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2 / 2

  -- Step 1a: Nonnegativity (easy)
  have hf_nonneg : ∀ t ∈ TimeGrid.slabReal tg i, 0 ≤ f t := by
    intro t ht
    unfold f
    refine Finset.sum_nonneg ?_
    intro k hk
    exact mul_nonneg (ℓ2ZD.hminusWeight_nonneg k) (sq_nonneg _)

  have hg_nonneg : ∀ t ∈ TimeGrid.slabReal tg i, 0 ≤ g t := by
    intro t ht
    unfold g
    exact mul_nonneg (sq_nonneg _) (abs_nonneg _)

  -- Step 1b: g is integrable (continuous on compact)
  have hg_int : IntegrableOn g (TimeGrid.slabReal tg i) volume := by
    have h_cont : Continuous g :=
      continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const))
    -- Rewrite slabReal as Icc
    unfold TimeGrid.slabReal
    exact h_cont.integrableOn_Icc
  have h_slab_meas : MeasurableSet (TimeGrid.slabReal tg i) := by
    unfold TimeGrid.slabReal
    exact measurableSet_Icc
  have h_slab_vol_fin : volume (TimeGrid.slabReal tg i) < ∞ := by
    unfold TimeGrid.slabReal
    exact measure_Icc_lt_top

  -- Step 1c: Establish pointwise bound f ≤ g
  have h_pointwise : ∀ t ∈ TimeGrid.slabReal tg i, f t ≤ g t := by
    intro t ht
    unfold f g
    -- Use existing pointwise_time_modulus_bound
    have h_orig := pointwise_time_modulus_bound P A tg hcompat i t ht F
    convert h_orig using 1
    congr 1
    ext k
    rw [curveExtended_coeff_eq_on_slab P A tg hcompat i t ht k]

  -- Step 1d: f is integrable (0 ≤ f ≤ g, g integrable)
  let f_cont : ℝ → ℝ := fun t =>
    Finset.sum F (fun k =>
      ℓ2ZD.hminusWeight k *
        ‖(A.curve (horizonClamp P t)).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)
  have hf_cont : Continuous f_cont := by
    classical
    unfold f_cont
    apply continuous_finset_sum
    intro k hk
    have hcurve :
        Continuous fun t : ℝ => (A.curve (horizonClamp P t)).a k :=
      (A.curve_coeff_continuous k).comp (horizonClamp_continuous P)
    have hconst :
        Continuous fun _ : ℝ => (A.sampleAtNodes tg hcompat i).a k :=
      continuous_const
    have hdiff := hcurve.sub hconst
    have hnorm := hdiff.norm
    have hsq := hnorm.pow 2
    exact continuous_const.mul hsq
  have hf_eq_on :
      ∀ t ∈ TimeGrid.slabReal tg i, f t = f_cont t := by
    intro t ht
    unfold f f_cont
    have ht_interval := slab_mem_interval tg hcompat i t ht
    have hclamp := horizonClamp_eq_self (P := P) (t := t) ht_interval
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hcoeff := curveExtended_coeff_eq_on_slab (d := d) P A tg hcompat i t ht k
    simp [hcoeff, hclamp]
  have hf_eq :
      f =ᵐ[volume.restrict (TimeGrid.slabReal tg i)] f_cont :=
    ae_restrict_of_forall_mem h_slab_meas hf_eq_on
  have hf_cont_meas : AEStronglyMeasurable f_cont volume :=
    hf_cont.aestronglyMeasurable
  have hf_cont_restrict :
      AEStronglyMeasurable f_cont (volume.restrict (TimeGrid.slabReal tg i)) :=
    hf_cont_meas.mono_measure (Measure.restrict_le_self)
  have hf_meas_restrict :
      AEStronglyMeasurable f (volume.restrict (TimeGrid.slabReal tg i)) :=
    hf_cont_restrict.congr hf_eq.symm
  have hf_int : IntegrableOn f (TimeGrid.slabReal tg i) volume := by
    refine IntegrableOn.of_bound h_slab_vol_fin
      hf_meas_restrict ((P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)) ?_
    -- Bounded: |f t| ≤ (P.S)^2 * mesh for t in slab
    apply ae_restrict_of_forall_mem h_slab_meas
    intro t ht
    have h_mesh_bound : |t - ((tg.node i : ℚ) : ℝ)| ≤ ((tg.mesh : ℚ) : ℝ) :=
      time_diff_le_mesh tg i t ht
    specialize h_pointwise t ht
    calc ‖f t‖
        ≤ Finset.sum F (fun k => ‖ℓ2ZD.hminusWeight k *
            ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2‖) := by
              unfold f; apply norm_sum_le
      _ = Finset.sum F (fun k => ℓ2ZD.hminusWeight k *
            ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) := by
              congr 1
              ext k
              rw [norm_mul]
              have h_weight_nonneg : 0 ≤ ℓ2ZD.hminusWeight k := ℓ2ZD.hminusWeight_nonneg k
              have h_sq_nonneg :
                  0 ≤ ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2 :=
                sq_nonneg _
              rw [Real.norm_of_nonneg h_weight_nonneg, Real.norm_of_nonneg h_sq_nonneg]
      _ = f t := rfl
      _ ≤ g t := h_pointwise
      _ ≤ (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ) := by
          unfold g
          apply mul_le_mul_of_nonneg_left h_mesh_bound
          apply sq_nonneg

  -- Step 2: Use integral monotonicity
  have h_mono : ∫ t in TimeGrid.slabReal tg i, f t ≤
                ∫ t in TimeGrid.slabReal tg i, g t := by
    apply setIntegral_mono_on₀
    · exact hf_int
    · exact hg_int
    · exact h_slab_meas.nullMeasurableSet
    · exact h_pointwise

  -- Step 3: Evaluate ∫ g
  have h_integral_eval : ∫ t in TimeGrid.slabReal tg i, g t =
      (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2 / 2 := by
    unfold g
    rw [integral_const_mul]
    -- Use existing integral_abs_diff_Icc lemma
    have h_cast := TimeGrid.endpoint_castSucc tg i
    have h_length := TimeGrid.slabReal_length tg i
    rw [h_cast] at h_length
    have h_mesh_nonneg : 0 ≤ ((tg.mesh : ℚ) : ℝ) := by
      have := TimeGrid.mesh_pos tg
      linarith
    have h_integral : ∫ t in TimeGrid.slabReal tg i, |t - ((tg.node i : ℚ) : ℝ)| =
        ((tg.mesh : ℚ) : ℝ)^2 / 2 := by
      calc ∫ t in TimeGrid.slabReal tg i, |t - ((tg.node i : ℚ) : ℝ)|
          = ∫ t in Set.Icc ((tg.node i : ℚ) : ℝ) ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ),
              |t - ((tg.node i : ℚ) : ℝ)| := by
            congr 1
            unfold TimeGrid.slabReal
            rw [h_cast]
        _ = ∫ t in Set.Icc ((tg.node i : ℚ) : ℝ) (((tg.node i : ℚ) : ℝ) + ((tg.mesh : ℚ) : ℝ)),
              |t - ((tg.node i : ℚ) : ℝ)| := by
            have h_eq : ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ) =
                ((tg.node i : ℚ) : ℝ) + ((tg.mesh : ℚ) : ℝ) := by
              rw [← h_length]
              ring
            rw [h_eq]
        _ = ((tg.mesh : ℚ) : ℝ)^2 / 2 := integral_abs_diff_Icc _ _ h_mesh_nonneg
    rw [h_integral]
    ring

  -- Step 4: Combine
  calc ∫ t in TimeGrid.slabReal tg i, f t
      ≤ ∫ t in TimeGrid.slabReal tg i, g t := h_mono
    _ = (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2 / 2 := h_integral_eval

end TimeModulusBounds

section Inequalities

variable {α : Type*} [NormedAddCommGroup α]

lemma norm_sq_le_quad (x y z : α) :
    ‖x - z‖^2 ≤ 2 * ‖x - y‖^2 + 2 * ‖y - z‖^2 := by
  classical
  have htriangle :
      ‖(x - y) + (y - z)‖ ≤ ‖x - y‖ + ‖y - z‖ :=
    norm_add_le _ _
  have hpow :
      ‖x - z‖^2 ≤ (‖x - y‖ + ‖y - z‖)^2 := by
    have h_eq : x - z = (x - y) + (y - z) := by abel
    calc ‖x - z‖^2
        = ‖(x - y) + (y - z)‖^2 := by rw [h_eq]
      _ ≤ (‖x - y‖ + ‖y - z‖)^2 := by
        nlinarith [htriangle, norm_nonneg (x - y + (y - z)), norm_nonneg (x - y), norm_nonneg (y - z)]
  have hsq :=
    sq_nonneg (‖x - y‖ - ‖y - z‖)
  have hcross :
      2 * ‖x - y‖ * ‖y - z‖ ≤ ‖x - y‖^2 + ‖y - z‖^2 := by
    have h_expand : (‖x - y‖ - ‖y - z‖)^2 =
        ‖x - y‖^2 - 2 * ‖x - y‖ * ‖y - z‖ + ‖y - z‖^2 := by ring
    rw [h_expand] at hsq
    linarith
  have hsum :
      (‖x - y‖ + ‖y - z‖)^2
        ≤ 2 * ‖x - y‖^2 + 2 * ‖y - z‖^2 := by
    calc (‖x - y‖ + ‖y - z‖)^2
        = ‖x - y‖^2 + 2 * ‖x - y‖ * ‖y - z‖ + ‖y - z‖^2 := by ring
      _ ≤ ‖x - y‖^2 + (‖x - y‖^2 + ‖y - z‖^2) + ‖y - z‖^2 := by linarith
      _ = 2 * ‖x - y‖^2 + 2 * ‖y - z‖^2 := by ring
  exact le_trans hpow hsum

/-- Triangle inequality for squared norms: ‖x - y‖² ≤ 2‖x‖² + 2‖y‖² -/
lemma norm_sq_diff_le (x y : α) :
    ‖x - y‖^2 ≤ 2 * ‖x‖^2 + 2 * ‖y‖^2 := by
  -- Use norm_sq_le_quad with z = 0
  have h := norm_sq_le_quad x (0 : α) y
  simp only [sub_zero, zero_sub, norm_neg] at h
  exact h

end Inequalities

section NodeRounding

variable {d : ℕ} [NeZero d]

/-- Choose a grid witness at each time node using the QRK-D rounding theorem. -/
noncomputable def nodeWitness (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon) :
    SpaceTimeGridPoint d P.ε P.R (ℓ2ZD.M_of P.ε P.R) tg :=
  ⟨fun i =>
    Classical.choose
      (ℓ2ZD.gridFinset_sound_d_proof
        (d := d) P.ε P.R
        (by exact_mod_cast P.hε)
        (by exact_mod_cast P.hR)
        (A.sampleAtNodes tg hcompat i)
        (Admissible.sampleAtNodes_meanZero (A := A) tg hcompat i)
        (Admissible.sampleAtNodes_inH1 (A := A) tg hcompat i))⟩

lemma node_round_error (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon) :
    ∀ i : Fin tg.segments,
      ∀ F : Finset (ℓ2ZD.Lattice d),
        Finset.sum F
            (fun k =>
              ‖(A.sampleAtNodes tg hcompat i).a k
                  - (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                      ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2)
          < (P.ε : ℝ)^2 := by
  intro i F
  classical
  have := (Classical.choose_spec
    (ℓ2ZD.gridFinset_sound_d_proof
        (d := d) P.ε P.R
        (by exact_mod_cast P.hε)
        (by exact_mod_cast P.hR)
        (A.sampleAtNodes tg hcompat i)
        (Admissible.sampleAtNodes_meanZero (A := A) tg hcompat i)
        (Admissible.sampleAtNodes_inH1 (A := A) tg hcompat i)))
  simpa [nodeWitness] using this F

/-- Convert BudgetParams ℚ values to ConstructiveQ for extraction.
    This enables axiom reduction by using ConstructiveQ arithmetic instead of ℚ. -/
def εToConstructiveQ (ε : ℚ) : ConstructiveQ.Q :=
  ConstructiveQ.normalize ε.num ε.den

def RToConstructiveQ (R : ℚ) : ConstructiveQ.Q :=
  ConstructiveQ.normalize R.num R.den

/-- Helper lemma: Converting ε to ConstructiveQ and back gives ε.
    This is provable because normalize preserves the rational value. -/
lemma constructiveQ_roundtrip_ε (ε : ℚ) :
    ℓ2ZD.constructiveQ_to_rat (εToConstructiveQ ε) = ε := by
  unfold εToConstructiveQ ℓ2ZD.constructiveQ_to_rat
  have h := normalize_preserves_value ε.num ε.den (Rat.den_ne_zero ε)
  simpa [h] using Rat.num_div_den ε

/-- Helper lemma: Converting R to ConstructiveQ and back gives R.
    This is provable because normalize preserves the rational value. -/
lemma constructiveQ_roundtrip_R (R : ℚ) :
    ℓ2ZD.constructiveQ_to_rat (RToConstructiveQ R) = R := by
  unfold RToConstructiveQ ℓ2ZD.constructiveQ_to_rat
  have h := normalize_preserves_value R.num R.den (Rat.den_ne_zero R)
  simpa [h] using Rat.num_div_den R

/-- The constructive and classical rounding produce the same grid points -/
lemma roundToGridD_equivalence {d : ℕ} (ε R : ℚ) (M : ℕ) (x : ℓ2ZD.SeqD d)
    (k : ℓ2ZD.Lattice d) (hk : k ∈ ℓ2ZD.IndexSetD d M) :
    (ℓ2ZD.roundToGridD_C (εToConstructiveQ ε) (RToConstructiveQ R) M x k hk).val =
    (ℓ2ZD.roundToGridD ε R M x k hk).val := by
  unfold ℓ2ZD.roundToGridD_C ℓ2ZD.roundToGridD

  -- Both use the same mesh value (via meshD_C_eq_meshD)
  have hδ : ℓ2ZD.constructiveQ_to_rat (ℓ2ZD.meshD_C d (εToConstructiveQ ε) M) =
            ℓ2ZD.meshD d ε M := by
    rw [ℓ2ZD.meshD_C_eq_meshD]
    rw [constructiveQ_roundtrip_ε]

  -- Both round using the same δ value
  simp only [hδ]

  -- The rounded value is the same
  let rounded := ℓ2ZD.roundCoeff (ℓ2ZD.meshD d ε M) (x.a k)

  -- Check membership in equivalent boxes (coeffBoxList vs coeffBox have same elements)
  have box_equiv : rounded ∈ ℓ2ZD.coeffBoxList (ℓ2ZD.constructiveQ_to_rat (εToConstructiveQ ε))
                              (ℓ2ZD.constructiveQ_to_rat (RToConstructiveQ R)) M k ↔
                   rounded ∈ ℓ2ZD.coeffBox ε R M k := by
    rw [constructiveQ_roundtrip_ε, constructiveQ_roundtrip_R]
    -- Use the fact that coeffBoxList.toFinset = coeffBox
    have : (ℓ2ZD.coeffBoxList ε R M k).toFinset = ℓ2ZD.coeffBox ε R M k :=
      ℓ2ZD.coeffBoxList_eq_coeffBox ε R M k
    rw [← this]
    simp only [List.mem_toFinset]

  -- Both branches produce the same result
  split_ifs with h1 h2
  · -- Both in box: same value
    rfl
  · -- C in box, classical not: contradiction
    rw [← box_equiv] at h2
    contradiction
  · -- C not in box, classical in: contradiction
    rw [box_equiv] at h1
    contradiction
  · -- Both not in box: both use (0,0)
    rfl

/-- The constructive witness reconstruction equals the classical one -/
lemma witness_reconstruction_equivalence {d : ℕ} (ε R : ℚ) (M : ℕ)
    (sample : ℓ2ZD.SeqD d) (k : ℓ2ZD.Lattice d) :
    (ℓ2ZD.gridToSeqD_C (εToConstructiveQ ε) (RToConstructiveQ R) M
      (ℓ2ZD.roundToGridD_C (εToConstructiveQ ε) (RToConstructiveQ R) M sample)).a k =
    (ℓ2ZD.gridToSeqD ε R M
      (ℓ2ZD.roundToGridD ε R M sample)).a k := by
  -- Unfold the definitions of gridToSeqD_C and gridToSeqD
  unfold ℓ2ZD.gridToSeqD_C ℓ2ZD.gridToSeqD

  -- Case split on whether k is in the index set
  by_cases hk : k ∈ ℓ2ZD.IndexSetD d M
  · -- k in IndexSetD: both compute using the same formula
    simp only [dif_pos hk]

    -- The mesh values are equal
    have hδ : ℓ2ZD.constructiveQ_to_rat (ℓ2ZD.meshD_C d (εToConstructiveQ ε) M) =
              ℓ2ZD.meshD d ε M := by
      rw [ℓ2ZD.meshD_C_eq_meshD]
      rw [constructiveQ_roundtrip_ε]

    -- The grid points are equal
    have hp : (ℓ2ZD.roundToGridD_C (εToConstructiveQ ε) (RToConstructiveQ R) M sample k hk).val =
              (ℓ2ZD.roundToGridD ε R M sample k hk).val :=
      roundToGridD_equivalence ε R M sample k hk

    -- Rewrite using these equalities
    rw [hp, hδ]

  · -- k not in IndexSetD: both return 0
    simp only [dif_neg hk]

/-- Constructive space-time grid point using ConstructiveQ infrastructure.
    This version uses GridPointD_C (List-based, ConstructiveQ) to eliminate 2/3 Classical.choice sources. -/
structure SpaceTimeGridPoint_C (d : ℕ) (ε R : ℚ) (M : ℕ) (tg : TimeGrid) where
  coeffs : Fin tg.segments → ℓ2ZD.GridPointD_C d (εToConstructiveQ ε) (RToConstructiveQ R) M

/-- Constructive witness selection: uses roundToGridD_C with ConstructiveQ + List infrastructure.
    This version eliminates 2/3 Classical.choice sources (ℚ arithmetic, Finset operations)
    while keeping extraction fully C0-compatible. Only Classical.choice from Complex.floor remains. -/
noncomputable def nodeWitness_C (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon) :
    SpaceTimeGridPoint_C d P.ε P.R (ℓ2ZD.M_of P.ε P.R) tg :=
  ⟨fun i => ℓ2ZD.roundToGridD_C (εToConstructiveQ P.ε) (RToConstructiveQ P.R)
              (ℓ2ZD.M_of P.ε P.R) (A.sampleAtNodes tg hcompat i)⟩

set_option maxHeartbeats 800000

/-- Constructive witness error bound: matches the Classical.choose version exactly.

    **Proof strategy**: The theorem gridFinset_sound_d_proof internally constructs
    the witness as `g := roundToGridD ε R M x` (line 88 of Soundness.lean), then proves
    the error bound for this specific g. Since nodeWitness_C uses the same roundToGridD_C
    construction (which is mathematically equivalent to roundToGridD), the bound follows
    by the same argument.

    **TODO**: Complete this proof by either:
    1. Extracting a direct lemma from Soundness.lean that states the property for
       roundToGridD_C explicitly (avoiding the existential), or
    2. Using a custom tactic to apply the proof modulo witness equality.

    For now, this is marked as axiom-free but incomplete. The mathematical content
    is identical to node_round_error (the Classical.choose version). -/
lemma node_round_error_C (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon) :
    ∀ i : Fin tg.segments,
      ∀ F : Finset (ℓ2ZD.Lattice d),
        Finset.sum F
            (fun k =>
              ‖(A.sampleAtNodes tg hcompat i).a k
                  - (ℓ2ZD.gridToSeqD_C (εToConstructiveQ P.ε) (RToConstructiveQ P.R)
                      (ℓ2ZD.M_of P.ε P.R)
                      ((nodeWitness_C P A tg hcompat).coeffs i)).a k‖^2)
          < (P.ε : ℝ)^2 := by
  intro i F

  /- Mathematical Proof Strategy:

     The theorem gridFinset_sound_d_proof proves that for any H¹-bounded sequence x
     with mean zero, the witness g := roundToGridD ε R M x satisfies the error bound.

     Our constructive witness uses roundToGridD_C, which differs from roundToGridD only in:
     1. Using ConstructiveQ instead of ℚ for parameters
     2. Using List.product instead of Finset.product for coefficient boxes
     3. Both use the SAME roundCoeff function and mesh parameter (via meshD_C_eq_meshD)

     Since the mathematical rounding algorithm is identical, the error bound applies. -/

  -- Apply the classical soundness theorem to get the existence of a good witness
  -- The key insight: We can use roundToGridD_sound directly (non-existential!)
  -- combined with witness_reconstruction_equivalence to show the constructive
  -- version matches the classical bound.

  -- Use our axiom to relate the constructive and classical witnesses
  have h_equiv : Finset.sum F (fun k =>
        ‖(A.sampleAtNodes tg hcompat i).a k -
          (ℓ2ZD.gridToSeqD_C (εToConstructiveQ P.ε) (RToConstructiveQ P.R)
            (ℓ2ZD.M_of P.ε P.R) ((nodeWitness_C P A tg hcompat).coeffs i)).a k‖^2)
      = Finset.sum F (fun k =>
          ‖(A.sampleAtNodes tg hcompat i).a k -
            (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
              (ℓ2ZD.roundToGridD P.ε P.R (ℓ2ZD.M_of P.ε P.R) (A.sampleAtNodes tg hcompat i))).a k‖^2) := by
    congr 1
    ext k
    congr 2
    unfold nodeWitness_C
    simp only []
    -- The axiom gives us equality of the reconstructed values
    rw [witness_reconstruction_equivalence P.ε P.R (ℓ2ZD.M_of P.ε P.R)
      (A.sampleAtNodes tg hcompat i) k]

  -- Rewrite and apply the classical bound
  rw [h_equiv]

  -- Apply the non-existential roundToGridD_sound directly!
  -- This gives us the exact bound we need without Classical.choice
  apply ℓ2ZD.roundToGridD_sound
  · exact_mod_cast P.hε
  · exact_mod_cast P.hR
  · exact Admissible.sampleAtNodes_meanZero (A := A) tg hcompat i
  · exact Admissible.sampleAtNodes_inH1 (A := A) tg hcompat i

end NodeRounding

end AubinLions
