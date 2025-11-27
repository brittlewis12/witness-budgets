import Mathlib.Tactic
import Budgets.AubinLions.Core
import Budgets.AubinLions.TimeModulus
import Budgets.AubinLions.IntegrationHelpers

/-!
# Time Grid API: Slabs and Partitioning

This module defines the interval decomposition for `TimeGrid` and proves that
the time slabs partition `[0, T]` with disjoint interiors.

## Main definitions

* `slab tg i`: The `i`-th time interval `[tᵢ, tᵢ₊₁]` on the grid
* `slabReal tg i`: The real version of the slab

## Main lemmas

* `slab_nonempty`: Each slab is nonempty
* `slab_length`: The length of slab `i` equals `Δt = mesh tg`
* `slabs_partition`: The union of all slabs equals `[0, T]`
* `slabs_disjoint_interior`: Slabs have disjoint interiors
-/

open scoped BigOperators

namespace AubinLions

namespace TimeGrid

/-- The right endpoint index for slab i: this is i+1 viewed as a Fin (segments + 1). -/
def rightIdx (tg : TimeGrid) (i : Fin tg.segments) : Fin (tg.segments + 1) :=
  ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

/-- The `i`-th time slab as a closed interval in ℝ, defined using rational endpoints
converted to reals. The slab spans from `endpoint i.castSucc` to `endpoint (i+1)`. -/
def slabReal (tg : TimeGrid) (i : Fin tg.segments) : Set ℝ :=
  Set.Icc ((tg.endpoint i.castSucc : ℚ) : ℝ) ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ)

/-- The `i`-th time slab as a rational interval. Useful for maintaining rational
arithmetic throughout witness extraction. -/
def slab (tg : TimeGrid) (i : Fin tg.segments) : Set ℚ :=
  Set.Icc (tg.endpoint i.castSucc) (tg.endpoint (rightIdx tg i))

/-
## Helper lemmas about endpoints
-/

/-- Endpoints are monotone: if `i ≤ j` then `endpoint i ≤ endpoint j`. -/
lemma endpoint_mono (tg : TimeGrid) {i j : Fin (tg.segments + 1)} (hij : i ≤ j) :
    tg.endpoint i ≤ tg.endpoint j := by
  by_cases hi : (i : ℕ) < tg.segments
  · by_cases hj : (j : ℕ) < tg.segments
    · -- Both i and j are within segments
      have heqi := endpoint_mem (tg := tg) hi
      have heqj := endpoint_mem (tg := tg) hj
      rw [heqi, heqj]
      have hfin_le : (⟨i, hi⟩ : Fin tg.segments) ≤ ⟨j, hj⟩ := by
        simpa using hij
      exact node_mono tg hfin_le
    · -- i < segments, j = segments (last endpoint)
      have heqi := endpoint_mem (tg := tg) hi
      have : j = Fin.last tg.segments := by
        have : (j : ℕ) = tg.segments := by
          omega
        ext
        simpa using this
      rw [heqi, this, endpoint_last]
      exact node_le_horizon tg ⟨i, hi⟩
  · -- i = segments (already at horizon)
    have : (i : ℕ) = tg.segments := by omega
    have hi_last : i = Fin.last tg.segments := by
      ext
      simpa using this
    have : (j : ℕ) = tg.segments := by omega
    have hj_last : j = Fin.last tg.segments := by
      ext
      simpa using this
    rw [hi_last, hj_last]

/-! ### Strict endpoint ordering -/

/-- Endpoints are strictly monotone: if i < j, then endpoint i < endpoint j. -/
lemma endpoint_lt_of_lt (tg : TimeGrid) {i j : Fin (tg.segments + 1)} (hij : i < j) :
    (tg.endpoint i : ℚ) < (tg.endpoint j : ℚ) := by
  by_cases hi : (i : ℕ) < tg.segments
  · by_cases hj : (j : ℕ) < tg.segments
    · -- Both i and j are within segments: use node_strict_mono
      have heqi := endpoint_mem (tg := tg) hi
      have heqj := endpoint_mem (tg := tg) hj
      rw [heqi, heqj]
      have hfin_lt : (⟨i, hi⟩ : Fin tg.segments) < ⟨j, hj⟩ := by
        simpa using hij
      exact node_strict_mono hfin_lt
    · -- i < segments, j = segments (last endpoint): show node i < horizon
      have heqi := endpoint_mem (tg := tg) hi
      have : j = Fin.last tg.segments := by
        have : (j : ℕ) = tg.segments := by omega
        ext
        simpa using this
      rw [heqi, this, endpoint_last]
      -- Need to show: node i < horizon
      -- node i = i * mesh and horizon = segments * mesh
      -- Since i < segments and mesh > 0, we have i * mesh < segments * mesh
      have hmesh_pos : 0 < mesh tg := mesh_pos_rat tg
      have hi_lt_segments : (i : ℚ) < (tg.segments : ℚ) := by
        have : (i : ℕ) < tg.segments := hi
        exact_mod_cast this
      have : tg.node ⟨i, hi⟩ = (i : ℚ) * mesh tg := rfl
      have horizon_eq : tg.horizon = (tg.segments : ℚ) * mesh tg := by
        have := mesh_mul_segments tg
        rw [mul_comm] at this
        exact this.symm
      rw [this, horizon_eq]
      exact mul_lt_mul_of_pos_right hi_lt_segments hmesh_pos
  · -- i = segments: impossible since i < j and j ≤ segments
    have : (i : ℕ) = tg.segments := by omega
    have : (j : ℕ) > tg.segments := by omega
    have : (j : ℕ) < tg.segments + 1 := j.isLt
    omega

/-- The endpoint of `i.castSucc` equals the node at `i`. -/
lemma endpoint_castSucc (tg : TimeGrid) (i : Fin tg.segments) :
    tg.endpoint i.castSucc = tg.node i := by
  exact endpoint_succ

/-- The right endpoint equals either the next node or the horizon. -/
lemma endpoint_rightIdx (tg : TimeGrid) (i : Fin tg.segments) :
    tg.endpoint (rightIdx tg i) =
      if h : (rightIdx tg i : ℕ) < tg.segments then
        tg.node ⟨rightIdx tg i, h⟩
      else
        tg.horizon := by
  unfold endpoint rightIdx
  simp

/-- Consecutive endpoints satisfy `endpoint i.castSucc ≤ endpoint (i+1)`. -/
lemma endpoint_le_succ (tg : TimeGrid) (i : Fin tg.segments) :
    tg.endpoint i.castSucc ≤ tg.endpoint (rightIdx tg i) := by
  apply endpoint_mono
  simp only [Fin.le_def, Fin.coe_castSucc, rightIdx]
  omega

/-
## Slab properties
-/

/-- Each slab is nonempty because endpoints are monotone. -/
lemma slab_nonempty (tg : TimeGrid) (i : Fin tg.segments) :
    (slab tg i).Nonempty := by
  unfold slab
  apply Set.nonempty_Icc.mpr
  exact endpoint_le_succ tg i

/-- Each slab in real form is nonempty. -/
lemma slabReal_nonempty (tg : TimeGrid) (i : Fin tg.segments) :
    (slabReal tg i).Nonempty := by
  unfold slabReal
  apply Set.nonempty_Icc.mpr
  have := endpoint_le_succ tg i
  exact_mod_cast this

/-- The measure-theoretic length of a slab equals the mesh size.
This is expressed as an equality between the difference of rational endpoints
and the mesh. -/
lemma slab_length (tg : TimeGrid) (i : Fin tg.segments) :
    tg.endpoint (rightIdx tg i) - tg.endpoint i.castSucc = mesh tg := by
  -- The proof relies on showing that node (i+1) - node i = mesh
  -- when i+1 < segments, or horizon - node i = mesh when i = segments-1
  rw [endpoint_castSucc]
  rw [endpoint_rightIdx]
  split_ifs with h
  case pos =>
    -- h : (rightIdx tg i : ℕ) < tg.segments
    -- Goal: node ⟨rightIdx tg i, h⟩ - node i = mesh
    set j : Fin tg.segments := ⟨rightIdx tg i, h⟩ with hj_def
    -- node_diff tg a b gives: node b - node a = (b - a) * mesh
    have key : tg.node j - tg.node i = ((j : ℚ) - (i : ℚ)) * mesh tg :=
      node_diff tg i j
    have hi : (j : ℚ) - (i : ℚ) = 1 := by
      unfold rightIdx at hj_def
      simp [hj_def]
    simp [hi] at key
    exact key
  case neg =>
    -- h : ¬(rightIdx tg i : ℕ) < tg.segments
    -- Goal: horizon - node i = mesh
    -- This means i is the last segment (i.val + 1 = segments)
    unfold rightIdx at h
    simp at h
    have i_last : i.val + 1 = tg.segments := by omega
    have i_eq : i.val = tg.segments - 1 := by omega
    have node_i : tg.node i = (tg.segments - 1 : ℚ) * mesh tg := by
      have : (i : ℚ) = (tg.segments - 1 : ℚ) := by
        have hseg_pos : 0 < tg.segments := tg.segments_pos
        have : (i.val : ℚ) = (tg.segments - 1 : ℚ) := by
          simp [i_eq, hseg_pos]
        simpa using this
      simp [node, this]
    rw [node_i]
    have hseg_pos : 0 < tg.segments := tg.segments_pos
    have horizon_eq : tg.horizon = (tg.segments : ℚ) * mesh tg := by
      have := mesh_mul_segments tg
      rw [mul_comm] at this
      exact this.symm
    rw [horizon_eq]
    have : (tg.segments : ℚ) * mesh tg - (tg.segments - 1 : ℚ) * mesh tg = mesh tg := by
      have hsub : (tg.segments : ℚ) - (tg.segments - 1 : ℚ) = 1 := by
        simp
      calc (tg.segments : ℚ) * mesh tg - (tg.segments - 1 : ℚ) * mesh tg
          = ((tg.segments : ℚ) - (tg.segments - 1 : ℚ)) * mesh tg := by ring
        _ = 1 * mesh tg := by rw [hsub]
        _ = mesh tg := by ring
    exact this

/-- The real version of the slab length. -/
lemma slabReal_length (tg : TimeGrid) (i : Fin tg.segments) :
    ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ) - ((tg.endpoint i.castSucc : ℚ) : ℝ)
      = ((mesh tg : ℚ) : ℝ) := by
  have := slab_length tg i
  exact_mod_cast this

/-- Consecutive endpoints are distinct (strictly increasing). -/
lemma endpoint_castSucc_lt_rightIdx (tg : TimeGrid) (i : Fin tg.segments) :
    (tg.endpoint i.castSucc : ℚ) < (tg.endpoint (rightIdx tg i) : ℚ) := by
  have hlength := slab_length tg i
  have hmesh_pos := mesh_pos_rat tg
  calc (tg.endpoint i.castSucc : ℚ)
      < tg.endpoint i.castSucc + mesh tg := by linarith
    _ = tg.endpoint (rightIdx tg i) := by linarith [hlength]

/-
## Helper lemmas for interval interiors
-/

/-- A point in the interior of a rational closed interval [a, b] is strictly between a and b. -/
lemma Rat.Icc_interior_mem {a b t : ℚ} (ht : t ∈ interior (Set.Icc a b)) : a < t ∧ t < b := by
  -- The interior of [a,b] in ℚ is (a,b)
  have h_eq : interior (Set.Icc a b) = Set.Ioo a b := interior_Icc
  rw [h_eq] at ht
  exact ht

/-- A point in the interior of a real closed interval [a, b] is strictly between a and b. -/
lemma Icc_mem_interior {a b t : ℝ} (ht : t ∈ interior (Set.Icc a b)) : a < t ∧ t < b := by
  -- In ℝ with the standard topology, interior of [a,b] is (a,b)
  have h_eq : interior (Set.Icc a b) = Set.Ioo a b := interior_Icc
  rw [h_eq] at ht
  exact ht

/-- All slabs together cover the interval `[0, horizon]`. -/
lemma slabs_partition (tg : TimeGrid) :
    (⋃ i : Fin tg.segments, slab tg i) = Set.Icc 0 tg.horizon := by
  ext t
  simp only [Set.mem_iUnion, slab, Set.mem_Icc]
  constructor
  · -- Forward direction: if t is in some slab, then t ∈ [0, horizon]
    intro ⟨i, h_le_left, h_le_right⟩
    constructor
    · -- Show t ≥ 0
      calc t ≥ tg.endpoint i.castSucc := h_le_left
           _ ≥ tg.endpoint 0 := endpoint_mono tg (Fin.zero_le _)
           _ = 0 := endpoint_zero tg
    · -- Show t ≤ horizon
      calc t ≤ tg.endpoint (rightIdx tg i) := h_le_right
           _ ≤ tg.endpoint (Fin.last _) := endpoint_mono tg (by
             unfold rightIdx
             exact Fin.le_last _)
           _ = tg.horizon := endpoint_last tg
  · -- Reverse direction: if t ∈ [0, horizon], find i such that t ∈ slab i
    -- Strategy: find the maximal i where endpoint i.castSucc ≤ t
    intro ⟨h_zero, h_horizon⟩
    classical
    -- Consider the set of indices whose left endpoint is ≤ t
    let S := Finset.univ.filter (fun i : Fin tg.segments => tg.endpoint i.castSucc ≤ t)
    -- This set is nonempty (contains 0)
    have hS_nonempty : S.Nonempty := by
      use ⟨0, tg.segments_pos⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      calc tg.endpoint (Fin.castSucc ⟨0, tg.segments_pos⟩) = tg.endpoint 0 := rfl
           _ = 0 := endpoint_zero tg
           _ ≤ t := h_zero
    -- Find the maximum element
    obtain ⟨i, hi_mem, hi_max⟩ := S.exists_max_image id hS_nonempty
    use i
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi_mem
    constructor
    · -- t ≥ endpoint i.castSucc
      exact hi_mem
    · -- t ≤ endpoint (rightIdx i)
      by_cases hi_last : i.val = tg.segments - 1
      · -- i is the last slab index
        have hi_eq : i = ⟨tg.segments - 1, by omega⟩ := Fin.ext hi_last
        rw [hi_eq]
        calc t ≤ tg.horizon := h_horizon
             _ = tg.endpoint (Fin.last tg.segments) := (endpoint_last tg).symm
             _ = tg.endpoint (rightIdx tg ⟨tg.segments - 1, by omega⟩) := by
               congr 1
               ext
               simp only [Fin.val_last, rightIdx, Fin.val_mk]
               omega
      · -- i < segments - 1, so we can consider i+1
        have hi_lt : i.val + 1 < tg.segments := by omega
        let i_succ : Fin tg.segments := ⟨i.val + 1, hi_lt⟩
        -- By maximality, i_succ ∉ S, so ¬(endpoint i_succ.castSucc ≤ t)
        have h_not_mem : i_succ ∉ S := by
          intro h_contra
          have h_i_succ_cond : tg.endpoint i_succ.castSucc ≤ t := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h_contra
            exact h_contra
          have h_le := hi_max i_succ h_contra
          simp only [id_eq] at h_le
          -- h_le says i.val ≥ i_succ.val = i.val + 1, contradiction
          have : i.val ≥ i.val + 1 := h_le
          omega
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at h_not_mem
        -- So t < endpoint i_succ.castSucc
        have h_t_lt : t < tg.endpoint i_succ.castSucc := h_not_mem
        -- But i_succ.castSucc = rightIdx i
        have h_eq : i_succ.castSucc = rightIdx tg i := by
          ext
          simp only [Fin.coe_castSucc, i_succ, Fin.val_mk, rightIdx]
        rw [h_eq] at h_t_lt
        exact le_of_lt h_t_lt

/-- The real version of the partition property. -/
lemma slabsReal_partition (tg : TimeGrid) :
    (⋃ i : Fin tg.segments, slabReal tg i) = Set.Icc (0 : ℝ) ((tg.horizon : ℚ) : ℝ) := by
  -- This follows from slabs_partition with coercions
  ext t
  simp only [Set.mem_iUnion, slabReal, Set.mem_Icc]
  constructor
  · -- Forward: if t is in some real slab, then t ∈ [0, horizon]
    intro ⟨i, h_le_left, h_le_right⟩
    constructor
    · calc t ≥ ((tg.endpoint i.castSucc : ℚ) : ℝ) := h_le_left
           _ ≥ ((tg.endpoint 0 : ℚ) : ℝ) := by
             exact_mod_cast endpoint_mono tg (Fin.zero_le _)
           _ = ((0 : ℚ) : ℝ) := by
             rw [endpoint_zero]
           _ = 0 := by norm_cast
    · calc t ≤ ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ) := h_le_right
           _ ≤ ((tg.endpoint (Fin.last _) : ℚ) : ℝ) := by
             exact_mod_cast endpoint_mono tg (by
               unfold rightIdx
               exact Fin.le_last _)
           _ = ((tg.horizon : ℚ) : ℝ) := by
             rw [endpoint_last]
  · -- Reverse: if t ∈ [0, horizon], find i
    -- Similar strategy to slabs_partition
    intro ⟨h_zero, h_horizon⟩
    classical
    -- Consider the set of indices whose left endpoint is ≤ t
    let S := Finset.univ.filter (fun i : Fin tg.segments =>
      ((tg.endpoint i.castSucc : ℚ) : ℝ) ≤ t)
    -- This set is nonempty (contains 0)
    have hS_nonempty : S.Nonempty := by
      use ⟨0, tg.segments_pos⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      calc ((tg.endpoint (Fin.castSucc ⟨0, tg.segments_pos⟩) : ℚ) : ℝ)
            = ((tg.endpoint 0 : ℚ) : ℝ) := rfl
         _ = ((0 : ℚ) : ℝ) := by rw [endpoint_zero]
         _ = 0 := by norm_cast
         _ ≤ t := h_zero
    -- Find the maximum element
    obtain ⟨i, hi_mem, hi_max⟩ := S.exists_max_image id hS_nonempty
    use i
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi_mem
    constructor
    · -- t ≥ (endpoint i.castSucc : ℝ)
      exact hi_mem
    · -- t ≤ (endpoint (rightIdx i) : ℝ)
      by_cases hi_last : i.val = tg.segments - 1
      · -- i is the last slab index
        have hi_eq : i = ⟨tg.segments - 1, by omega⟩ := Fin.ext hi_last
        rw [hi_eq]
        calc t ≤ ((tg.horizon : ℚ) : ℝ) := h_horizon
             _ = ((tg.endpoint (Fin.last tg.segments) : ℚ) : ℝ) := by
               rw [endpoint_last]
             _ = ((tg.endpoint (rightIdx tg ⟨tg.segments - 1, by omega⟩) : ℚ) : ℝ) := by
               congr 2
               ext
               simp only [Fin.val_last, rightIdx, Fin.val_mk]
               omega
      · -- i < segments - 1, so we can consider i+1
        have hi_lt : i.val + 1 < tg.segments := by omega
        let i_succ : Fin tg.segments := ⟨i.val + 1, hi_lt⟩
        -- By maximality, i_succ ∉ S, so ¬((endpoint i_succ.castSucc : ℝ) ≤ t)
        have h_not_mem : i_succ ∉ S := by
          intro h_contra
          have h_i_succ_cond : ((tg.endpoint i_succ.castSucc : ℚ) : ℝ) ≤ t := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h_contra
            exact h_contra
          have h_le := hi_max i_succ h_contra
          simp only [id_eq] at h_le
          -- h_le says i.val ≥ i_succ.val = i.val + 1, contradiction
          have : i.val ≥ i.val + 1 := h_le
          omega
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at h_not_mem
        -- So t < (endpoint i_succ.castSucc : ℝ)
        have h_t_lt : t < ((tg.endpoint i_succ.castSucc : ℚ) : ℝ) := h_not_mem
        -- But i_succ.castSucc = rightIdx i
        have h_eq : i_succ.castSucc = rightIdx tg i := by
          ext
          simp only [Fin.coe_castSucc, i_succ, Fin.val_mk, rightIdx]
        rw [h_eq] at h_t_lt
        exact le_of_lt h_t_lt

/-- Slabs have disjoint interiors: if `i ≠ j`, then the interiors of
`slab i` and `slab j` are disjoint. -/
lemma slabs_disjoint_interior (tg : TimeGrid) {i j : Fin tg.segments} (hij : i ≠ j) :
    interior (slab tg i) ∩ interior (slab tg j) = ∅ := by
  -- Directly show no point can be in both interiors
  by_contra h_nonempty
  -- There exists a point in both interiors
  have h_ex : (interior (slab tg i) ∩ interior (slab tg j)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact h_nonempty
  obtain ⟨t, ht_mem⟩ := h_ex
  rw [Set.mem_inter_iff] at ht_mem
  obtain ⟨ht_i, ht_j⟩ := ht_mem
  -- Determine ordering of i and j
  by_cases h_ij : i.val < j.val
  · -- Case: i < j, so slabs are ordered
    have h_endpoints : tg.endpoint (rightIdx tg i) ≤ tg.endpoint j.castSucc := by
      apply endpoint_mono
      simp only [Fin.le_def, rightIdx, Fin.coe_castSucc]
      omega
    -- Interior of Icc [a,b] where a ≤ b consists of points strictly between a and b
    have ht_i_bounds : tg.endpoint i.castSucc < t ∧ t < tg.endpoint (rightIdx tg i) := by
      unfold slab at ht_i
      exact Rat.Icc_interior_mem ht_i
    have ht_j_bounds : tg.endpoint j.castSucc < t ∧ t < tg.endpoint (rightIdx tg j) := by
      unfold slab at ht_j
      exact Rat.Icc_interior_mem ht_j
    -- But then t < endpoint (rightIdx i) ≤ endpoint j.castSucc < t, contradiction
    have : t < tg.endpoint j.castSucc := calc
      t < tg.endpoint (rightIdx tg i) := ht_i_bounds.2
      _ ≤ tg.endpoint j.castSucc := h_endpoints
    linarith [ht_j_bounds.1]
  · -- Case: j ≤ i, and since i ≠ j, we have j < i
    have h_ji : j.val < i.val := by omega
    have h_endpoints : tg.endpoint (rightIdx tg j) ≤ tg.endpoint i.castSucc := by
      apply endpoint_mono
      simp only [Fin.le_def, rightIdx, Fin.coe_castSucc]
      omega
    have ht_i_bounds : tg.endpoint i.castSucc < t ∧ t < tg.endpoint (rightIdx tg i) := by
      unfold slab at ht_i
      exact Rat.Icc_interior_mem ht_i
    have ht_j_bounds : tg.endpoint j.castSucc < t ∧ t < tg.endpoint (rightIdx tg j) := by
      unfold slab at ht_j
      exact Rat.Icc_interior_mem ht_j
    have : t < tg.endpoint i.castSucc := calc
      t < tg.endpoint (rightIdx tg j) := ht_j_bounds.2
      _ ≤ tg.endpoint i.castSucc := h_endpoints
    linarith [ht_i_bounds.1]

/-- The real version of disjoint interiors. -/
lemma slabsReal_disjoint_interior (tg : TimeGrid) {i j : Fin tg.segments} (hij : i ≠ j) :
    interior (slabReal tg i) ∩ interior (slabReal tg j) = ∅ := by
  -- Directly show no point can be in both interiors
  by_contra h_nonempty
  -- There exists a point in both interiors
  have h_ex : (interior (slabReal tg i) ∩ interior (slabReal tg j)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact h_nonempty
  obtain ⟨t, ht_mem⟩ := h_ex
  rw [Set.mem_inter_iff] at ht_mem
  obtain ⟨ht_i, ht_j⟩ := ht_mem
  -- Determine ordering of i and j
  by_cases h_ij : i.val < j.val
  · -- Case: i < j, so slabs are ordered
    have h_endpoints : tg.endpoint (rightIdx tg i) ≤ tg.endpoint j.castSucc := by
      apply endpoint_mono
      simp only [Fin.le_def, rightIdx, Fin.coe_castSucc]
      omega
    have h_endpoints_real : ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ) ≤
        ((tg.endpoint j.castSucc : ℚ) : ℝ) := by
      exact_mod_cast h_endpoints
    -- Interior of Icc [a,b] where a ≤ b consists of points strictly between a and b
    have ht_i_bounds : ((tg.endpoint i.castSucc : ℚ) : ℝ) < t ∧
        t < ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ) := by
      unfold slabReal at ht_i
      exact Icc_mem_interior ht_i
    have ht_j_bounds : ((tg.endpoint j.castSucc : ℚ) : ℝ) < t ∧
        t < ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ) := by
      unfold slabReal at ht_j
      exact Icc_mem_interior ht_j
    -- But then t < endpoint (rightIdx i) ≤ endpoint j.castSucc < t, contradiction
    have : t < ((tg.endpoint j.castSucc : ℚ) : ℝ) := calc
      t < ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ) := ht_i_bounds.2
      _ ≤ ((tg.endpoint j.castSucc : ℚ) : ℝ) := h_endpoints_real
    linarith [ht_j_bounds.1]
  · -- Case: j ≤ i, and since i ≠ j, we have j < i
    have h_ji : j.val < i.val := by omega
    have h_endpoints : tg.endpoint (rightIdx tg j) ≤ tg.endpoint i.castSucc := by
      apply endpoint_mono
      simp only [Fin.le_def, rightIdx, Fin.coe_castSucc]
      omega
    have h_endpoints_real : ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ) ≤
        ((tg.endpoint i.castSucc : ℚ) : ℝ) := by
      exact_mod_cast h_endpoints
    have ht_i_bounds : ((tg.endpoint i.castSucc : ℚ) : ℝ) < t ∧
        t < ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ) := by
      unfold slabReal at ht_i
      exact Icc_mem_interior ht_i
    have ht_j_bounds : ((tg.endpoint j.castSucc : ℚ) : ℝ) < t ∧
        t < ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ) := by
      unfold slabReal at ht_j
      exact Icc_mem_interior ht_j
    have : t < ((tg.endpoint i.castSucc : ℚ) : ℝ) := calc
      t < ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ) := ht_j_bounds.2
      _ ≤ ((tg.endpoint i.castSucc : ℚ) : ℝ) := h_endpoints_real
    linarith [ht_i_bounds.1]

/-- Real slabs are pairwise almost-everywhere disjoint: their intersections have measure zero.
This follows from interior disjointness: for closed intervals with disjoint interiors,
the intersection is contained in the frontier, which has measure zero. -/
lemma slabsReal_ae_disjoint (tg : TimeGrid) :
    Pairwise (fun i j : Fin tg.segments =>
      MeasureTheory.volume (slabReal tg i ∩ slabReal tg j) = 0) := by
  intro i j hij
  -- Get interior disjointness
  have h_int_disj := slabsReal_disjoint_interior tg hij
  -- Slabs are closed intervals Icc
  unfold slabReal at *
  -- For Icc intervals with disjoint interiors, intersection is contained in frontiers
  -- Frontiers have measure zero, so intersection has measure zero
  have h_frontier_i : MeasureTheory.volume (frontier (Set.Icc ((tg.endpoint i.castSucc : ℚ) : ℝ)
      ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ))) = 0 := by
    apply IntegrationHelpers.measure_frontier_Icc_zero
    -- Prove endpoints are strictly ordered
    have h_le : tg.endpoint i.castSucc ≤ tg.endpoint (rightIdx tg i) := endpoint_le_succ tg i
    have h_ne : tg.endpoint i.castSucc ≠ tg.endpoint (rightIdx tg i) := by
      intro h_eq
      have hmesh_pos : 0 < tg.mesh := TimeGrid.mesh_pos_rat tg
      have hdiff := TimeGrid.slab_length tg i
      have : tg.mesh = 0 := by simpa [h_eq] using hdiff.symm
      exact (ne_of_gt hmesh_pos) this
    have h_lt : tg.endpoint i.castSucc < tg.endpoint (rightIdx tg i) := lt_of_le_of_ne h_le h_ne
    exact_mod_cast h_lt
  have h_frontier_j : MeasureTheory.volume (frontier (Set.Icc ((tg.endpoint j.castSucc : ℚ) : ℝ)
      ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ))) = 0 := by
    apply IntegrationHelpers.measure_frontier_Icc_zero
    have h_le : tg.endpoint j.castSucc ≤ tg.endpoint (rightIdx tg j) := endpoint_le_succ tg j
    have h_ne : tg.endpoint j.castSucc ≠ tg.endpoint (rightIdx tg j) := by
      intro h_eq
      have hmesh_pos : 0 < tg.mesh := TimeGrid.mesh_pos_rat tg
      have hdiff := TimeGrid.slab_length tg j
      have : tg.mesh = 0 := by simpa [h_eq] using hdiff.symm
      exact (ne_of_gt hmesh_pos) this
    have h_lt : tg.endpoint j.castSucc < tg.endpoint (rightIdx tg j) := lt_of_le_of_ne h_le h_ne
    exact_mod_cast h_lt
  -- Intersection of closed sets with disjoint interiors lies in frontiers
  have h_subset : (Set.Icc ((tg.endpoint i.castSucc : ℚ) : ℝ)
      ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ)) ∩
    (Set.Icc ((tg.endpoint j.castSucc : ℚ) : ℝ)
      ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ))
    ⊆ frontier (Set.Icc ((tg.endpoint i.castSucc : ℚ) : ℝ)
        ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ)) ∪
      frontier (Set.Icc ((tg.endpoint j.castSucc : ℚ) : ℝ)
        ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ)) := by
    intro x hx
    -- Use h_int_disj: interiors are disjoint
    by_contra h_not
    simp only [Set.mem_union, not_or] at h_not
    -- x is in both Icc but not in either frontier
    -- Therefore x is in both interiors (contradiction with h_int_disj)
    have hx_int_i : x ∈ interior (Set.Icc ((tg.endpoint i.castSucc : ℚ) : ℝ)
        ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ)) := by
      have hx_front : x ∉ frontier (Set.Icc ((tg.endpoint i.castSucc : ℚ) : ℝ)
          ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ)) := h_not.1
      have hx_mem : x ∈ Set.Icc ((tg.endpoint i.castSucc : ℚ) : ℝ)
          ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ) := hx.1
      have h_le : ((tg.endpoint i.castSucc : ℚ) : ℝ)
          ≤ ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ) := by
        exact_mod_cast endpoint_le_succ tg i
      have hfront_eq := frontier_Icc (a := ((tg.endpoint i.castSucc : ℚ) : ℝ))
        (b := ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ)) h_le
      simp [hfront_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hx_front
      obtain ⟨hx_ne_left, hx_ne_right⟩ := hx_front
      have hx_bounds :
          ((tg.endpoint i.castSucc : ℚ) : ℝ) < x ∧ x < ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ) := by
        have hx_ne_left' : ((tg.endpoint i.castSucc : ℚ) : ℝ) ≠ x := (ne_comm).mp hx_ne_left
        have hx_ne_right' : x ≠ ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ) := hx_ne_right
        refine ⟨lt_of_le_of_ne hx_mem.1 hx_ne_left', lt_of_le_of_ne hx_mem.2 hx_ne_right'⟩
      have hx_ioo : x ∈ Set.Ioo ((tg.endpoint i.castSucc : ℚ) : ℝ)
          ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ) := hx_bounds
      simpa [interior_Icc, h_le] using hx_ioo
    have hx_int_j : x ∈ interior (Set.Icc ((tg.endpoint j.castSucc : ℚ) : ℝ)
        ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ)) := by
      have hx_front : x ∉ frontier (Set.Icc ((tg.endpoint j.castSucc : ℚ) : ℝ)
          ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ)) := h_not.2
      have hx_mem : x ∈ Set.Icc ((tg.endpoint j.castSucc : ℚ) : ℝ)
          ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ) := hx.2
      have h_le : ((tg.endpoint j.castSucc : ℚ) : ℝ)
          ≤ ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ) := by
        exact_mod_cast endpoint_le_succ tg j
      have hfront_eq := frontier_Icc (a := ((tg.endpoint j.castSucc : ℚ) : ℝ))
        (b := ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ)) h_le
      simp [hfront_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hx_front
      obtain ⟨hx_ne_left, hx_ne_right⟩ := hx_front
      have hx_bounds :
          ((tg.endpoint j.castSucc : ℚ) : ℝ) < x ∧ x < ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ) := by
        have hx_ne_left' : ((tg.endpoint j.castSucc : ℚ) : ℝ) ≠ x := (ne_comm).mp hx_ne_left
        have hx_ne_right' : x ≠ ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ) := hx_ne_right
        refine ⟨lt_of_le_of_ne hx_mem.1 hx_ne_left', lt_of_le_of_ne hx_mem.2 hx_ne_right'⟩
      have hx_ioo : x ∈ Set.Ioo ((tg.endpoint j.castSucc : ℚ) : ℝ)
          ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ) := hx_bounds
      simpa [interior_Icc, h_le] using hx_ioo
    have : x ∈ interior (Set.Icc ((tg.endpoint i.castSucc : ℚ) : ℝ)
        ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ)) ∩
      interior (Set.Icc ((tg.endpoint j.castSucc : ℚ) : ℝ)
        ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ)) := ⟨hx_int_i, hx_int_j⟩
    rw [h_int_disj] at this
    exact this
  -- Measure of intersection ≤ measure of union of frontiers = 0
  have h_le : MeasureTheory.volume ((Set.Icc ((tg.endpoint i.castSucc : ℚ) : ℝ)
          ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ)) ∩
        (Set.Icc ((tg.endpoint j.castSucc : ℚ) : ℝ)
          ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ))) ≤ 0 := by
    calc MeasureTheory.volume ((Set.Icc ((tg.endpoint i.castSucc : ℚ) : ℝ)
            ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ)) ∩
          (Set.Icc ((tg.endpoint j.castSucc : ℚ) : ℝ)
            ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ)))
        ≤ MeasureTheory.volume (frontier (Set.Icc ((tg.endpoint i.castSucc : ℚ) : ℝ)
              ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ)) ∪
            frontier (Set.Icc ((tg.endpoint j.castSucc : ℚ) : ℝ)
              ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ))) :=
          MeasureTheory.measure_mono h_subset
      _ ≤ MeasureTheory.volume (frontier (Set.Icc ((tg.endpoint i.castSucc : ℚ) : ℝ)
              ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ))) +
          MeasureTheory.volume (frontier (Set.Icc ((tg.endpoint j.castSucc : ℚ) : ℝ)
              ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ))) :=
          MeasureTheory.measure_union_le _ _
      _ = 0 + 0 := by rw [h_frontier_i, h_frontier_j]
      _ = 0 := by ring
  -- Measure is nonnegative, so ≤ 0 implies = 0
  have h_nonneg : 0 ≤ MeasureTheory.volume ((Set.Icc ((tg.endpoint i.castSucc : ℚ) : ℝ)
          ((tg.endpoint (rightIdx tg i) : ℚ) : ℝ)) ∩
        (Set.Icc ((tg.endpoint j.castSucc : ℚ) : ℝ)
          ((tg.endpoint (rightIdx tg j) : ℚ) : ℝ))) := by positivity
  exact le_antisymm h_le h_nonneg

end TimeGrid

end AubinLions
