import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Budgets.AubinLions.Integration
import Budgets.AubinLions.TimeGridAPI

/-!
# Phase 2: Piecewise Witness Function for Quantitative Aubin-Lions

This module implements the time-dependent witness function that approximates
admissible curves in L²(0,T; L²) space. The witness is piecewise constant,
with one spatial witness per time slab.

## Main definitions

* `witnessAtTime`: The piecewise constant function ℝ → SeqD d

## Main lemmas

* `witnessAtTime_eq_at_slab`: Pointwise evaluation on slabs
* `witnessAtTime'_coeff_aestronglyMeasurable`: Each coefficient function is a.e. strongly measurable
* `witnessAtTime_sq_sum_bounded`: The squared sum of coefficients is bounded

## Design notes

The witness function uses a classical choice to select which slab contains
a given time point. Since slabs partition [0, horizon] with disjoint interiors,
this is well-defined almost everywhere. For times outside [0, horizon], we
return the zero sequence.

We prove measurability at the coefficient level (each `t ↦ witness(t).a(k)` is
measurable) rather than trying to lift to a measurable space structure on SeqD.
-/

open scoped BigOperators Classical
open Set MeasureTheory

namespace AubinLions

open ℓ2ZD

variable {d : ℕ} [NeZero d]

/-! ## Witness function definition -/

/-- The piecewise constant witness function. For each time t, returns the
spatial witness corresponding to the slab containing t. For times outside
[0, horizon], returns the zero sequence.

We use open scoped Classical to make the existential decidable. -/
noncomputable def witnessAtTime (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon) (t : ℝ) : SeqD d :=
  if h : ∃ i : Fin tg.segments, t ∈ TimeGrid.slabReal tg i then
    let i := Classical.choose h
    evalSpaceSlice P.ε P.R (ℓ2ZD.M_of P.ε P.R)
      ((nodeWitness P A tg hcompat).coeffs i)
  else
    zeroSeqD d

/-- Alternative formulation: explicitly select the slab index. -/
noncomputable def witnessSlabIndex (tg : TimeGrid) (t : ℝ) : Option (Fin tg.segments) :=
  if h : ∃ i : Fin tg.segments, t ∈ TimeGrid.slabReal tg i then
    some (Classical.choose h)
  else
    none

/-- Witness defined via slab index selection. -/
noncomputable def witnessAtTime' (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon) (t : ℝ) : SeqD d :=
  match witnessSlabIndex tg t with
  | some i => evalSpaceSlice P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                ((nodeWitness P A tg hcompat).coeffs i)
  | none => zeroSeqD d

/-! ## Helper lemmas about slab membership -/

/-- For any t in [0, horizon], there exists exactly one slab containing it. -/
lemma exists_slab_of_mem_interval (tg : TimeGrid) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) ((tg.horizon : ℚ) : ℝ)) :
    ∃ i : Fin tg.segments, t ∈ TimeGrid.slabReal tg i := by
  have := TimeGrid.slabsReal_partition tg
  rw [← this] at ht
  simp only [mem_iUnion] at ht
  exact ht

/-- If t is in slab i, then the existential witness can be taken to be i. -/
lemma exists_slab_eq (tg : TimeGrid) (i : Fin tg.segments) {t : ℝ}
    (ht : t ∈ TimeGrid.slabReal tg i) :
    ∃ j : Fin tg.segments, t ∈ TimeGrid.slabReal tg j := ⟨i, ht⟩

/-- Slabs are pairwise disjoint except possibly at boundaries. -/
lemma slab_unique_interior (tg : TimeGrid) {i j : Fin tg.segments} {t : ℝ}
    (hi : t ∈ interior (TimeGrid.slabReal tg i))
    (hj : t ∈ interior (TimeGrid.slabReal tg j)) :
    i = j := by
  by_contra hij
  have hdisj := TimeGrid.slabsReal_disjoint_interior tg hij
  have : t ∈ interior (TimeGrid.slabReal tg i) ∩
              interior (TimeGrid.slabReal tg j) := ⟨hi, hj⟩
  rw [hdisj] at this
  exact this

/-- The witness function at time t in slab i equals the grid evaluation at i.
This holds when t is in the interior of slab i, ensuring uniqueness. -/
lemma witnessAtTime'_eq_at_slab_interior (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    (i : Fin tg.segments) {t : ℝ}
    (ht : t ∈ interior (TimeGrid.slabReal tg i)) :
    witnessAtTime' P A tg hcompat t =
      evalSpaceSlice P.ε P.R (ℓ2ZD.M_of P.ε P.R)
        ((nodeWitness P A tg hcompat).coeffs i) := by
  unfold witnessAtTime' witnessSlabIndex
  have hex : ∃ j : Fin tg.segments, t ∈ TimeGrid.slabReal tg j := by
    use i
    exact interior_subset ht
  simp only [hex, ↓reduceDIte]
  -- Need to show that Classical.choose hex = i
  -- This uses the fact that t is in the interior, so the slab is unique
  have hchoose : t ∈ TimeGrid.slabReal tg (Classical.choose hex) :=
    Classical.choose_spec hex
  -- Show that t is also in the interior of the chosen slab
  have ht_interior_choose : t ∈ interior (TimeGrid.slabReal tg (Classical.choose hex)) := by
    -- t is in slabReal (Classical.choose hex), so either in interior or on boundary
    by_contra h_not_interior
    -- If not in interior, then t is on the boundary
    -- But t ∈ interior (slabReal i), so t is strictly between endpoints of slab i
    have ht_bounds : ((tg.endpoint i.castSucc : ℚ) : ℝ) < t ∧
        t < ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ) := by
      unfold TimeGrid.slabReal at ht
      exact TimeGrid.Icc_mem_interior ht
    -- t in closed interval [a,b] but not in interior (a,b) means t = a or t = b
    have ht_boundary : t = ((tg.endpoint (Classical.choose hex).castSucc : ℚ) : ℝ) ∨
        t = ((tg.endpoint (TimeGrid.rightIdx tg (Classical.choose hex)) : ℚ) : ℝ) := by
      unfold TimeGrid.slabReal at hchoose
      have : t ∈ Set.Icc ((tg.endpoint (Classical.choose hex).castSucc : ℚ) : ℝ)
                          ((tg.endpoint (TimeGrid.rightIdx tg (Classical.choose hex)) : ℚ) : ℝ) :=
        hchoose
      simp only [Set.mem_Icc] at this
      by_contra h_not_endpoint
      push_neg at h_not_endpoint
      -- Then t is strictly between the endpoints
      have h_strict : ((tg.endpoint (Classical.choose hex).castSucc : ℚ) : ℝ) < t ∧
          t < ((tg.endpoint (TimeGrid.rightIdx tg (Classical.choose hex)) : ℚ) : ℝ) := by
        constructor
        · exact lt_of_le_of_ne this.1 (h_not_endpoint.1.symm)
        · exact lt_of_le_of_ne this.2 h_not_endpoint.2
      -- So t is in the interior
      have h_in_int : t ∈ interior (TimeGrid.slabReal tg (Classical.choose hex)) := by
        unfold TimeGrid.slabReal
        rw [interior_Icc]
        exact h_strict
      exact h_not_interior h_in_int
    -- But t is strictly between endpoints of slab i, so can't equal an endpoint
    -- Key insight: if t ∈ interior [a,b], then a < t < b, so t ≠ a and t ≠ b
    cases ht_boundary with
    | inl h_eq =>
        -- t = left endpoint of chosen slab
        -- From ht_bounds.1: left(i) < t
        -- From h_eq: t = left(chosen)
        -- So: left(i) < left(chosen)
        -- But this means t = left(chosen), and left(i) < t
        -- However, if t is an endpoint, it cannot be in the interior of any slab
        -- The contradiction is: t ∈ interior [left(i), right(i)] implies left(i) < t
        -- But t = left(chosen) says t is an endpoint
        -- These are incompatible: an interior point cannot equal a boundary point
        -- We have left(i) < t and t = left(chosen)
        -- So left(i) < left(chosen)
        -- But also t = left(chosen), which means t is an endpoint
        -- This contradicts t ∈ interior, which requires t ≠ any endpoint
        -- We have: left(i) < t from ht_bounds.1
        -- We have: t = left(chosen) from h_eq
        -- Therefore: left(i) < left(chosen)
        -- But by substituting back: left(i) < t and t = left(chosen) gives left(i) < left(chosen)
        -- And since t = left(chosen), we have left(chosen) < left(chosen), i.e., t < t
        -- From ht_bounds.1: left(i) < t
        -- From h_eq: t = left(chosen)
        -- This should give a contradiction, but the proof is complex
        -- The key insight: if t ∈ interior(slab i), then t is not an endpoint
        -- But h_eq says t is an endpoint, contradiction
        -- From ht: t ∈ interior (slabReal i), which means left(i) < t
        -- From h_eq: t = left(chosen)
        -- Contradiction: t is in interior of slab i but equals an endpoint
        -- If t is an endpoint, it cannot be in any slab's interior
        -- t ∈ interior(slab i) means left(i) < t < right(i)
        -- But t = left(chosen), which is an endpoint
        -- Endpoints are on the boundary of slabs, never in the interior
        have : t ∉ interior (TimeGrid.slabReal tg i) := by
          rw [h_eq]
          unfold TimeGrid.slabReal
          rw [interior_Icc]
          intro ⟨h_left, h_right⟩
          -- h_left : ((tg.endpoint i.castSucc : ℚ) : ℝ) < ((tg.endpoint (Classical.choose hex).castSucc : ℚ) : ℝ)
          -- h_right : ((tg.endpoint (Classical.choose hex).castSucc : ℚ) : ℝ) < ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ)
          -- Cast back to rationals
          have h_left_rat : (tg.endpoint i.castSucc : ℚ) < (tg.endpoint (Classical.choose hex).castSucc : ℚ) := by
            simpa using h_left
          have h_right_rat : (tg.endpoint (Classical.choose hex).castSucc : ℚ) < (tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) := by
            simpa using h_right
          -- Use strict monotonicity: endpoint is strictly monotone, so if endpoint j < endpoint k then j < k
          have h_fin_left : i.castSucc < (Classical.choose hex).castSucc := by
            by_contra h_ge
            push_neg at h_ge
            have := TimeGrid.endpoint_mono tg h_ge
            linarith
          have h_fin_right : (Classical.choose hex).castSucc < TimeGrid.rightIdx tg i := by
            by_contra h_ge
            push_neg at h_ge
            have := TimeGrid.endpoint_mono tg h_ge
            linarith
          -- Now i.castSucc < chosen.castSucc < rightIdx i in Fin ordering
          -- But i.castSucc.val = i.val and (rightIdx i).val = i.val + 1
          -- So i.val < chosen.castSucc.val < i.val + 1, impossible for natural numbers
          have h_val_left : i.castSucc.val < (Classical.choose hex).castSucc.val := h_fin_left
          have h_val_right : (Classical.choose hex).castSucc.val < (TimeGrid.rightIdx tg i).val := h_fin_right
          unfold TimeGrid.rightIdx at h_val_right
          simp [Fin.coe_castSucc] at h_val_left h_val_right
          omega
        exact this ht
    | inr h_eq =>
        -- Similar for right endpoint: t = right(chosen)
        -- If t is an endpoint, it cannot be in any slab's interior
        have : t ∉ interior (TimeGrid.slabReal tg i) := by
          rw [h_eq]
          unfold TimeGrid.slabReal
          rw [interior_Icc]
          intro ⟨h_left, h_right⟩
          -- h_left : ((tg.endpoint i.castSucc : ℚ) : ℝ) < ((tg.endpoint (TimeGrid.rightIdx tg (Classical.choose hex)) : ℚ) : ℝ)
          -- h_right : ((tg.endpoint (TimeGrid.rightIdx tg (Classical.choose hex)) : ℚ) : ℝ) < ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ)
          -- Cast back to rationals
          have h_left_rat : (tg.endpoint i.castSucc : ℚ) < (tg.endpoint (TimeGrid.rightIdx tg (Classical.choose hex)) : ℚ) := by
            simpa using h_left
          have h_right_rat : (tg.endpoint (TimeGrid.rightIdx tg (Classical.choose hex)) : ℚ) < (tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) := by
            simpa using h_right
          -- Use strict monotonicity
          have h_fin_left : i.castSucc < TimeGrid.rightIdx tg (Classical.choose hex) := by
            by_contra h_ge
            push_neg at h_ge
            have := TimeGrid.endpoint_mono tg h_ge
            linarith
          have h_fin_right : TimeGrid.rightIdx tg (Classical.choose hex) < TimeGrid.rightIdx tg i := by
            by_contra h_ge
            push_neg at h_ge
            have := TimeGrid.endpoint_mono tg h_ge
            linarith
          -- Now i.castSucc < rightIdx chosen < rightIdx i in Fin ordering
          -- In terms of values: i.val < chosen.val + 1 < i.val + 1
          -- This gives chosen.val < i.val and i.val ≤ chosen.val, contradiction
          have h_val_left : i.castSucc.val < (TimeGrid.rightIdx tg (Classical.choose hex)).val := h_fin_left
          have h_val_right : (TimeGrid.rightIdx tg (Classical.choose hex)).val < (TimeGrid.rightIdx tg i).val := h_fin_right
          unfold TimeGrid.rightIdx at h_val_left h_val_right
          simp [Fin.coe_castSucc] at h_val_left h_val_right
          omega
        exact this ht
  -- Now apply uniqueness of slabs with disjoint interiors
  have h_indices_eq := slab_unique_interior tg ht ht_interior_choose
  rw [h_indices_eq]

/-- If a point lies in `[a,b]` but not in `(a,b)`, then it is one of the endpoints. -/
lemma mem_Icc_not_Ioo_eq_left_or_right {a b t : ℝ}
    (hmem : t ∈ Set.Icc a b) (hnot : t ∉ Set.Ioo a b) :
    t = a ∨ t = b := by
  have h_le := hmem.1
  have h_ge := hmem.2
  by_contra hne
  push_neg at hne
  obtain ⟨hne_left, hne_right⟩ := hne
  have h_lt_left : a < t := lt_of_le_of_ne h_le hne_left.symm
  have h_lt_right : t < b := lt_of_le_of_ne h_ge hne_right
  exact hnot ⟨h_lt_left, h_lt_right⟩

/-- A point of a slab that is not in the interior must lie on one of the two endpoints. -/
lemma slab_mem_not_interior_endpoint (tg : TimeGrid) (i : Fin tg.segments) {t : ℝ}
    (ht_slab : t ∈ TimeGrid.slabReal tg i)
    (ht_not : t ∉ interior (TimeGrid.slabReal tg i)) :
    t = ((tg.endpoint i.castSucc : ℚ) : ℝ) ∨
      t = ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ) := by
  classical
  have := mem_Icc_not_Ioo_eq_left_or_right
    (a := ((tg.endpoint i.castSucc : ℚ) : ℝ))
    (b := ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ))
    (t := t)
  have hmem : t ∈ Set.Icc ((tg.endpoint i.castSucc : ℚ) : ℝ)
      ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ) := by
    simpa [TimeGrid.slabReal] using ht_slab
  have hnot' : t ∉ Set.Ioo ((tg.endpoint i.castSucc : ℚ) : ℝ)
      ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ) := by
    simpa [TimeGrid.slabReal, interior_Icc] using ht_not
  exact this hmem hnot'

/-- On each slab, the witness agrees almost everywhere with the grid value of that slab. -/
lemma witnessAtTime'_ae_eq_on_slab (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    (i : Fin tg.segments) :
    ∀ᵐ t ∂volume.restrict (TimeGrid.slabReal tg i),
      witnessAtTime' P A tg hcompat t =
        evalSpaceSlice P.ε P.R (ℓ2ZD.M_of P.ε P.R)
          ((nodeWitness P A tg hcompat).coeffs i) := by
  classical
  set slab := TimeGrid.slabReal tg i
  set constVal :=
    evalSpaceSlice P.ε P.R (ℓ2ZD.M_of P.ε P.R)
      ((nodeWitness P A tg hcompat).coeffs i)
  have h_interior_eq :
      ∀ ⦃t : ℝ⦄, t ∈ interior slab →
        witnessAtTime' P A tg hcompat t = constVal := by
    intro t ht
    simpa [slab, constVal]
      using witnessAtTime'_eq_at_slab_interior (P := P) (A := A) (tg := tg) hcompat i ht
  have hslab_meas : MeasurableSet slab := by
    unfold slab TimeGrid.slabReal
    exact measurableSet_Icc
  set left := ((tg.endpoint i.castSucc : ℚ) : ℝ)
  set right := ((tg.endpoint (TimeGrid.rightIdx tg i) : ℚ) : ℝ)
  let endpoints : Set ℝ := {t | t = left ∨ t = right}
  have h_bad_subset :
      ({t : ℝ | witnessAtTime' P A tg hcompat t ≠ constVal} ∩ slab)
        ⊆ endpoints := by
    intro t ht
    have hslab : t ∈ slab := ht.2
    have hneq : witnessAtTime' P A tg hcompat t ≠ constVal := ht.1
    have h_not_int : t ∉ interior slab := by
      intro hint
      exact hneq (h_interior_eq hint)
    have hboundary :=
      slab_mem_not_interior_endpoint (tg := tg) (i := i) hslab h_not_int
    cases hboundary with
    | inl h =>
        subst h
        exact Or.inl rfl
    | inr h =>
        subst h
        exact Or.inr rfl
  have h_endpoints_zero : volume endpoints = 0 := by
    have hA := measure_singleton (μ := volume) left
    have hB := measure_singleton (μ := volume) right
    have hendpoints_eq :
        endpoints = ({left} : Set ℝ) ∪ {right} := by
      ext t
      constructor
      · intro ht
        rcases ht with h | h
        · subst h; simp
        · subst h; simp
      · intro ht
        have : t = left ∨ t = right := by
          simpa [Set.mem_union, Set.mem_singleton_iff, Or.comm] using ht
        cases this with
        | inl h =>
            subst h; simp [endpoints]
        | inr h =>
            subst h; simp [endpoints]
    have h_union_le :
        volume endpoints ≤ volume {left} + volume {right} := by
      simpa [hendpoints_eq] using measure_union_le (μ := volume) ({left} : Set ℝ) {right}
    have : volume endpoints ≤ 0 := by
      simpa [hA, hB] using h_union_le
    exact le_antisymm this (zero_le _)
  have h_bad_inter_zero : volume
      ({t : ℝ | witnessAtTime' P A tg hcompat t ≠ constVal} ∩ slab) = 0 := by
    refine measure_mono_null h_bad_subset h_endpoints_zero
  have h_bad_zero :
      (volume.restrict slab)
          {t : ℝ | witnessAtTime' P A tg hcompat t ≠ constVal} = 0 := by
    simpa [Measure.restrict_apply, hslab_meas] using h_bad_inter_zero
  refine (ae_iff.2 ?_)
  simpa [constVal] using h_bad_zero
/-- The witness function is mean-zero at every time. -/
lemma witnessAtTime'_meanZero (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon) (t : ℝ) :
    meanZero (witnessAtTime' P A tg hcompat t) := by
  unfold witnessAtTime'
  split
  · -- t is in some slab
    exact evalSpaceSlice_meanZero P.ε P.R (ℓ2ZD.M_of P.ε P.R) _
  · -- t is outside [0, horizon]
    exact zeroSeqD_meanZero d

/-! ## Coefficient-level measurability -/

/-- For each coefficient k, the function t ↦ witness(t).a(k) is almost everywhere
strongly measurable. This is sufficient for all integration purposes in the
Quantitative Aubin-Lions theorem. -/
lemma witnessAtTime'_coeff_aestronglyMeasurable (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    (k : Lattice d) :
    AEStronglyMeasurable (fun t : ℝ => (witnessAtTime' P A tg hcompat t).a k) volume := by
  -- The function is piecewise constant on a finite partition
  -- For each slab i, the function equals (gridToSeqD ... (coeffs i)).a k
  -- Outside slabs, it equals 0
  --
  -- Strategy: Express as a finite sum of indicator functions on disjoint interiors
  -- ∑ i, Set.indicator (interior (slabReal i)) (fun _ => c_i)
  --
  -- Each indicator function on a measurable set is measurable
  -- Finite sums of measurable functions are measurable
  -- The sum agrees with our function a.e. (except on boundaries, which have measure zero)

  classical
  -- Each slab interior is measurable
  have slab_interior_measurable : ∀ i : Fin tg.segments,
      MeasurableSet (interior (TimeGrid.slabReal tg i)) := fun i => by
    unfold TimeGrid.slabReal
    exact isOpen_interior.measurableSet

  -- Define the indicator sum on interiors
  let f_sum := fun t : ℝ =>
    Finset.sum Finset.univ (fun i : Fin tg.segments =>
      Set.indicator (interior (TimeGrid.slabReal tg i))
        (fun _ => (evalSpaceSlice P.ε P.R (ℓ2ZD.M_of P.ε P.R)
          ((nodeWitness P A tg hcompat).coeffs i)).a k) t)

  -- The sum is measurable
  have f_sum_meas : Measurable f_sum := by
    apply Finset.measurable_sum
    intro i _
    exact Measurable.indicator measurable_const (slab_interior_measurable i)

  -- Define the boundary set (endpoints of all slabs)
  let boundary_set := ⋃ i : Fin tg.segments.succ,
    ({((tg.endpoint i : ℚ) : ℝ)} : Set ℝ)

  -- Show that the functions agree outside the boundary set
  have heq_outside : ∀ t ∉ boundary_set,
      (witnessAtTime' P A tg hcompat t).a k = f_sum t := by
    intro t ht_not_boundary
    unfold f_sum
    by_cases h : ∃ i : Fin tg.segments, t ∈ interior (TimeGrid.slabReal tg i)
    case pos =>
      obtain ⟨i, hi⟩ := h
      -- On the interior of slab i, the witness equals the grid evaluation at i
      have heq := witnessAtTime'_eq_at_slab_interior P A tg hcompat i hi
      rw [heq]
      -- The sum has exactly one non-zero term (the i-th term)
      rw [Finset.sum_eq_single i]
      · -- The i-th term
        rw [Set.indicator_of_mem hi]
      · -- Other terms are zero
        intro j _ hji
        rw [Set.indicator_of_notMem]
        intro hj
        -- j ≠ i but t is in both interiors - contradiction with disjoint interiors
        have := slab_unique_interior tg hi hj
        exact hji this.symm
      · -- Can't happen - i is in Finset.univ
        intro hi_notin
        exact absurd (Finset.mem_univ i) hi_notin
    case neg =>
      push_neg at h
      -- t is not in any interior, so all indicators are zero
      have hsum_zero : Finset.sum Finset.univ (fun j : Fin tg.segments =>
          Set.indicator (interior (TimeGrid.slabReal tg j))
            (fun _ => (evalSpaceSlice P.ε P.R (ℓ2ZD.M_of P.ε P.R)
              ((nodeWitness P A tg hcompat).coeffs j)).a k) t) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [Set.indicator_of_notMem]
        exact h j
      rw [hsum_zero]
      -- t is not in any interior AND not on a boundary, so it's completely outside [0, horizon]
      unfold witnessAtTime' witnessSlabIndex
      by_cases hex : ∃ j : Fin tg.segments, t ∈ TimeGrid.slabReal tg j
      case pos =>
        -- t is in some slab, so must be on a boundary
        -- But we assumed t is not on the boundary - contradiction
        simp only [hex, ↓reduceDIte]
        exfalso
        apply ht_not_boundary
        -- t is in slabReal j for some j, so it's between two endpoints
        obtain ⟨j, hj⟩ := hex
        unfold TimeGrid.slabReal at hj
        simp only [Set.mem_Icc] at hj
        -- Since t is not in the interior, it equals one of the endpoints
        -- We show this leads to t being in boundary_set, contradicting ht_not_boundary
        -- First check if t equals left endpoint
        by_cases h_left : t = ((tg.endpoint j.castSucc : ℚ) : ℝ)
        · -- t is the left endpoint, so it's in boundary_set
          apply Set.mem_iUnion.mpr
          use j.castSucc
          exact h_left
        -- Otherwise check if t equals right endpoint
        · by_cases h_right : t = ((tg.endpoint (TimeGrid.rightIdx tg j) : ℚ) : ℝ)
          · -- t is the right endpoint, so it's in boundary_set
            apply Set.mem_iUnion.mpr
            use TimeGrid.rightIdx tg j
            exact h_right
          -- Otherwise t is strictly between endpoints, so in interior
          · -- But this contradicts our assumption that t is not in any interior
            have h_in_interior : t ∈ interior (TimeGrid.slabReal tg j) := by
              unfold TimeGrid.slabReal
              rw [interior_Icc]
              exact ⟨lt_of_le_of_ne hj.1 (Ne.symm h_left), lt_of_le_of_ne hj.2 h_right⟩
            -- This contradicts h, which says t is not in any interior
            have : False := h j h_in_interior
            exact absurd this (not_false_eq_true ▸ trivial)
      case neg =>
        -- t is outside all slabs, so witness = 0
        simp only [hex, ↓reduceDIte]
        simp [zeroSeqD]

  -- Our function agrees with f_sum almost everywhere
  -- (they differ only on boundaries between slabs, which have measure zero)
  have hf_eq : ∀ᵐ t ∂volume, (witnessAtTime' P A tg hcompat t).a k = f_sum t := by
    -- Show boundary_set has measure zero
    have h_boundary_null : volume boundary_set = 0 := by
      -- Finite union of singletons has measure zero
      -- boundary_set is ⋃ i, {endpoint i}, a finite union
      unfold boundary_set
      -- Use that a finite union of measure-zero sets has measure zero
      apply measure_iUnion_null
      intro i
      exact measure_singleton _

    -- Conclude a.e. equality by showing they differ only on boundary_set
    -- The functions agree outside boundary_set, which has measure zero
    -- Therefore they agree almost everywhere
    rw [ae_iff]
    have : {t | (witnessAtTime' P A tg hcompat t).a k ≠ f_sum t} ⊆ boundary_set := by
      intro t ht
      by_contra h_not_in
      exact ht (heq_outside t h_not_in)
    have h_le : volume {t | (witnessAtTime' P A tg hcompat t).a k ≠ f_sum t} ≤ volume boundary_set :=
      measure_mono this
    rw [h_boundary_null] at h_le
    exact le_antisymm h_le (zero_le _)

  -- Complete the AEStronglyMeasurable proof using the witness f_sum
  -- We have:
  -- - f_sum : ℝ → ℂ is a measurable function (finite sum of indicators)
  -- - f_sum_meas : Measurable f_sum
  -- - hf_eq : witness =ᵐ[volume] f_sum (a.e. equality)
  --
  -- The constructor for AEStronglyMeasurable requires:
  -- - A strongly measurable function g
  -- - Proof that f =ᵐ[μ] g
  --
  -- Since Measurable implies StronglyMeasurable for ℝ → ℂ, we're done
  exact ⟨f_sum, f_sum_meas.stronglyMeasurable, hf_eq⟩

/-! ## Boundedness and integrability -/

/-- For any finite set F of lattice points, the sum of squared norms
of witness coefficients is uniformly bounded. -/
lemma witnessAtTime'_finset_bounded (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    (F : Finset (Lattice d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      Finset.sum F (fun k => ‖(witnessAtTime' P A tg hcompat t).a k‖^2) ≤ C := by
  -- The witness takes finitely many values (one per slab, plus zero outside)
  -- Each value comes from a grid witness that approximates an H¹-bounded sample
  -- Strategy: use H¹ bound on samples + approximation error bound

  -- The worst-case bound: use H¹ bound + approximation error
  -- For each slab i, the sample has ∑ h1Weight k * ‖sample.a k‖² ≤ R²
  -- Since h1Weight k ≥ 1, we have ∑ ‖sample.a k‖² ≤ R²
  -- The grid witness is within ε of the sample
  -- By triangle inequality: ‖grid.a k‖ ≤ ‖sample.a k‖ + ‖grid.a k - sample.a k‖
  -- So ∑ ‖grid.a k‖² ≤ 2∑‖sample.a k‖² + 2∑‖grid.a k - sample.a k‖²
  --                    ≤ 2R² + 2ε²

  use 2 * ((P.R : ℝ)^2 + (P.ε : ℝ)^2)
  constructor
  · -- Show C ≥ 0
    have hR_sq : 0 ≤ (P.R : ℝ)^2 := sq_nonneg _
    have hε_sq : 0 ≤ (P.ε : ℝ)^2 := sq_nonneg _
    have hsum : 0 ≤ (P.R : ℝ)^2 + (P.ε : ℝ)^2 := add_nonneg hR_sq hε_sq
    linarith
  · -- Show bound holds for all t
    intro t
    unfold witnessAtTime'
    -- Pattern match on witnessSlabIndex
    generalize h_idx : witnessSlabIndex tg t = opt_i
    cases opt_i with
    | none =>
      -- t outside [0, horizon] (witness = zero)
      simp only [zeroSeqD, norm_zero, sq, zero_mul, Finset.sum_const_zero]
      have hR_sq : 0 ≤ (P.R : ℝ)^2 := sq_nonneg _
      have hε_sq : 0 ≤ (P.ε : ℝ)^2 := sq_nonneg _
      have hsum : 0 ≤ (P.R : ℝ)^2 + (P.ε : ℝ)^2 := add_nonneg hR_sq hε_sq
      linarith
    | some i =>
      -- t is in slab i (witness = grid point)
      -- Get the sample at this node
      let sample := A.sampleAtNodes tg hcompat i
      -- Strategy: use triangle inequality ‖grid‖² ≤ 2‖sample‖² + 2‖grid - sample‖²

      -- First, bound the sample using InH1Ball
      have sample_inH1 : InH1Ball P.R (sample) :=
        Admissible.sampleAtNodes_inH1 (A := A) tg hcompat i
      have h_sample_bound : Finset.sum F (fun k => ‖sample.a k‖^2) ≤ (P.R : ℝ)^2 := by
        -- From InH1Ball: ∑ h1Weight k * ‖sample.a k‖² ≤ R²
        have h_h1 := sample_inH1 F
        unfold InH1Ball at h_h1
        -- Since h1Weight k ≥ 1, we have ‖sample.a k‖² ≤ h1Weight k * ‖sample.a k‖²
        have h_le : Finset.sum F (fun k => ‖sample.a k‖^2) ≤
            Finset.sum F (fun k => h1Weight k * ‖sample.a k‖^2) := by
          apply Finset.sum_le_sum
          intro k hk
          have h_wt : 1 ≤ h1Weight k := h1Weight_ge_one k
          have h_nonneg : 0 ≤ ‖sample.a k‖^2 := sq_nonneg _
          calc ‖sample.a k‖^2
              = 1 * ‖sample.a k‖^2 := by ring
            _ ≤ h1Weight k * ‖sample.a k‖^2 :=
              mul_le_mul_of_nonneg_right h_wt h_nonneg
        exact le_trans h_le h_h1

      -- Second, bound the approximation error using node_round_error
      have h_error : Finset.sum F (fun k =>
          ‖sample.a k - (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
            ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) < (P.ε : ℝ)^2 := by
        exact node_round_error P A tg hcompat i F

      -- Apply triangle inequality: ‖grid‖² ≤ 2‖sample‖² + 2‖grid - sample‖²
      have h_triangle : ∀ k : Lattice d,
          ‖(ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
            ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2
          ≤ 2 * ‖sample.a k‖^2 +
             2 * ‖sample.a k - (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
               ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2 := by
        intro k
        -- Use norm_sq_le_quad with x = grid.a k, y = sample.a k, z = 0
        -- This gives: ‖grid‖² ≤ 2‖grid - sample‖² + 2‖sample‖²
        have h_quad := norm_sq_le_quad
          ((ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
            ((nodeWitness P A tg hcompat).coeffs i)).a k)
          (sample.a k) (0 : ℂ)
        simp only [sub_zero] at h_quad
        -- h_quad: ‖grid‖² ≤ 2‖grid - sample‖² + 2‖sample‖²
        -- We need: ‖grid‖² ≤ 2‖sample‖² + 2‖sample - grid‖²
        -- Use commutativity of addition and norm_sub_rev
        have : ‖(ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                  ((nodeWitness P A tg hcompat).coeffs i)).a k - sample.a k‖^2 =
               ‖sample.a k - (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                  ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2 := by
          rw [norm_sub_rev]
        rw [this] at h_quad
        linarith

      -- Sum the triangle inequality over F
      calc Finset.sum F (fun k =>
              ‖(evalSpaceSlice P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2)
          = Finset.sum F (fun k =>
              ‖(ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) := by
            simp [evalSpaceSlice]
        _ ≤ Finset.sum F (fun k =>
              2 * ‖sample.a k‖^2 +
              2 * ‖sample.a k - (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) := by
            apply Finset.sum_le_sum
            intro k hk
            exact h_triangle k
        _ = 2 * Finset.sum F (fun k => ‖sample.a k‖^2) +
            2 * Finset.sum F (fun k =>
              ‖sample.a k - (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) := by
            simp only [← Finset.mul_sum, Finset.sum_add_distrib]
        _ ≤ 2 * (P.R : ℝ)^2 + 2 * (P.ε : ℝ)^2 := by
            have h_err_le : Finset.sum F (fun k =>
                ‖sample.a k - (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                  ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2)
                ≤ (P.ε : ℝ)^2 := le_of_lt h_error
            have h_mul_mono1 : 2 * Finset.sum F (fun k => ‖sample.a k‖^2) ≤
                2 * (P.R : ℝ)^2 := by
              apply mul_le_mul_of_nonneg_left h_sample_bound
              norm_num
            have h_mul_mono2 : 2 * Finset.sum F (fun k =>
                ‖sample.a k - (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                  ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2)
                ≤ 2 * (P.ε : ℝ)^2 := by
              apply mul_le_mul_of_nonneg_left h_err_le
              norm_num
            linarith
        _ = 2 * ((P.R : ℝ)^2 + (P.ε : ℝ)^2) := by ring

/-- The witness function has finite L² mass on [0, horizon]. -/
lemma witnessAtTime'_l2_bounded (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    (F : Finset (Lattice d)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Icc (0 : ℝ) ((tg.horizon : ℚ) : ℝ),
        Finset.sum F (fun k => ‖(witnessAtTime' P A tg hcompat t).a k‖^2) ≤ C := by
  obtain ⟨C, hC_nonneg, hC_bound⟩ := witnessAtTime'_finset_bounded P A tg hcompat F
  exact ⟨C, hC_nonneg, fun t _ => hC_bound t⟩

/-- Direct bound lemma: witness sum is bounded by 2*(R² + ε²) for any time t.
This is a corollary of witnessAtTime'_finset_bounded that avoids existential extraction. -/
lemma witnessAtTime'_sum_bound (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    (F : Finset (Lattice d)) (t : ℝ) :
    Finset.sum F (fun k => ‖(witnessAtTime' P A tg hcompat t).a k‖^2)
      ≤ 2 * ((P.R : ℝ)^2 + (P.ε : ℝ)^2) := by
  unfold witnessAtTime'
  -- Pattern match on witnessSlabIndex
  generalize h_idx : witnessSlabIndex tg t = opt_i
  cases opt_i with
  | none =>
    -- t outside [0, horizon] (witness = zero)
    simp only [zeroSeqD, norm_zero, sq, zero_mul, Finset.sum_const_zero]
    have hR_sq : 0 ≤ (P.R : ℝ)^2 := sq_nonneg _
    have hε_sq : 0 ≤ (P.ε : ℝ)^2 := sq_nonneg _
    have hsum : 0 ≤ (P.R : ℝ)^2 + (P.ε : ℝ)^2 := add_nonneg hR_sq hε_sq
    linarith
  | some i =>
    -- t is in slab i (witness = grid point)
    -- Get the sample at this node
    let sample := A.sampleAtNodes tg hcompat i
    -- Strategy: use triangle inequality ‖grid‖² ≤ 2‖sample‖² + 2‖grid - sample‖²

    -- First, bound the sample using InH1Ball
    have sample_inH1 : InH1Ball P.R (sample) :=
      Admissible.sampleAtNodes_inH1 (A := A) tg hcompat i
    have h_sample_bound : Finset.sum F (fun k => ‖sample.a k‖^2) ≤ (P.R : ℝ)^2 := by
      -- From InH1Ball: ∑ h1Weight k * ‖sample.a k‖² ≤ R²
      have h_h1 := sample_inH1 F
      unfold InH1Ball at h_h1
      -- Since h1Weight k ≥ 1, we have ‖sample.a k‖² ≤ h1Weight k * ‖sample.a k‖²
      have h_le : Finset.sum F (fun k => ‖sample.a k‖^2) ≤
          Finset.sum F (fun k => h1Weight k * ‖sample.a k‖^2) := by
        apply Finset.sum_le_sum
        intro k hk
        have h_wt : 1 ≤ h1Weight k := h1Weight_ge_one k
        have h_nonneg : 0 ≤ ‖sample.a k‖^2 := sq_nonneg _
        calc ‖sample.a k‖^2
            = 1 * ‖sample.a k‖^2 := by ring
          _ ≤ h1Weight k * ‖sample.a k‖^2 :=
            mul_le_mul_of_nonneg_right h_wt h_nonneg
      exact le_trans h_le h_h1

    -- Second, bound the approximation error using node_round_error
    have h_error : Finset.sum F (fun k =>
        ‖sample.a k - (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
          ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) < (P.ε : ℝ)^2 := by
      exact node_round_error P A tg hcompat i F

    -- Apply triangle inequality: ‖grid‖² ≤ 2‖sample‖² + 2‖grid - sample‖²
    have h_triangle : ∀ k : Lattice d,
        ‖(ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
          ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2
        ≤ 2 * ‖sample.a k‖^2 +
           2 * ‖sample.a k - (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
             ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2 := by
      intro k
      -- Use norm_sq_le_quad with x = grid.a k, y = sample.a k, z = 0
      -- This gives: ‖grid‖² ≤ 2‖grid - sample‖² + 2‖sample‖²
      have h_quad := norm_sq_le_quad
        ((ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
          ((nodeWitness P A tg hcompat).coeffs i)).a k)
        (sample.a k) (0 : ℂ)
      simp only [sub_zero] at h_quad
      -- h_quad: ‖grid‖² ≤ 2‖grid - sample‖² + 2‖sample‖²
      -- We need: ‖grid‖² ≤ 2‖sample‖² + 2‖sample - grid‖²
      -- Use commutativity of addition and norm_sub_rev
      have : ‖(ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                ((nodeWitness P A tg hcompat).coeffs i)).a k - sample.a k‖^2 =
             ‖sample.a k - (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2 := by
        rw [norm_sub_rev]
      rw [this] at h_quad
      linarith

    -- Sum the triangle inequality over F
    calc Finset.sum F (fun k =>
            ‖(evalSpaceSlice P.ε P.R (ℓ2ZD.M_of P.ε P.R)
              ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2)
        = Finset.sum F (fun k =>
            ‖(ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
              ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) := by
          simp [evalSpaceSlice]
      _ ≤ Finset.sum F (fun k =>
            2 * ‖sample.a k‖^2 +
            2 * ‖sample.a k - (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
              ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) := by
          apply Finset.sum_le_sum
          intro k hk
          exact h_triangle k
      _ = 2 * Finset.sum F (fun k => ‖sample.a k‖^2) +
          2 * Finset.sum F (fun k =>
            ‖sample.a k - (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
              ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) := by
          simp only [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 2 * (P.R : ℝ)^2 + 2 * (P.ε : ℝ)^2 := by
          have h_err_le : Finset.sum F (fun k =>
              ‖sample.a k - (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2)
              ≤ (P.ε : ℝ)^2 := le_of_lt h_error
          have h_mul_mono1 : 2 * Finset.sum F (fun k => ‖sample.a k‖^2) ≤
              2 * (P.R : ℝ)^2 := by
            apply mul_le_mul_of_nonneg_left h_sample_bound
            norm_num
          have h_mul_mono2 : 2 * Finset.sum F (fun k =>
              ‖sample.a k - (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2)
              ≤ 2 * (P.ε : ℝ)^2 := by
            apply mul_le_mul_of_nonneg_left h_err_le
            norm_num
          linarith
      _ = 2 * ((P.R : ℝ)^2 + (P.ε : ℝ)^2) := by ring

end AubinLions
