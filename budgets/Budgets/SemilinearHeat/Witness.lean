import Budgets.GridMapping
import Budgets.IntervalDyadic
import Budgets.RellichKondrachovD.Core
import Budgets.SemilinearHeat.Evolution
import Budgets.Witness.Arithmetic
import Budgets.Witness.Summation

/-!
# The Witness Bridge

This module defines the fundamental predicate `IsWitness` that connects
computational interval representations to mathematical rational sequences.

## Main definitions

- `intervalContains`: Predicate for rational number containment in an interval
- `IsWitness`: The bridge predicate connecting `StateArray` and `SeqD_Rat`

## Purpose

The `IsWitness` predicate establishes that an efficiently-computable interval array
(O(1) access) faithfully represents a mathematically-defined rational sequence
(with finite support). This is the key to witness extraction: we compute with
intervals and prove containment of the mathematical object.

## Design principles

- Simple and direct definitions (no unnecessary abstraction)
- Proof-friendly structure (easy to prove and use)
- Ready for sanity checks (initialDataArray witnesses initialData_math)
-/

namespace Witness

open GridMapping
open IntervalDyadic
open ℓ2ZD
open SemilinearHeat (spatialDim StateArray applyCubic_Array convolve_Array
                      cubeListLattice latticeToIdx idxToLattice
                      laplacianWeight_interval laplacianWeight_rat
                      eulerStep_Array pi_interval pi_rat_ub)

/-! ## The Bridge: IsWitness

The fundamental predicate connecting computational and mathematical representations.
-/


/-- A StateArray witnesses a SeqD_Rat if all coefficients are contained in intervals.

This is the bridge between:
- **Computational**: `Array (IntervalD × IntervalD)` with O(1) access
- **Mathematical**: `Lattice → (ℚ × ℚ)` with finite support

The predicate ensures:
1. Size consistency: array has the right number of elements (2M+1 for 1D)
2. Containment: for each mode k in the grid, the mathematical value is in the interval

Parameters:
- `M`: Mode cutoff (grid contains modes in [-M, M])
- `u_impl`: Computational interval array
- `u_math`: Mathematical rational sequence

The predicate is constructive (no classical axioms) and can be checked
computationally for finite M. -/
def IsWitness (M : ℕ) (u_impl : StateArray) (u_math : SeqD_Rat spatialDim) : Prop :=
  -- 1. Size check: array has right number of elements
  u_impl.size = 2 * M + 1 ∧
  -- 2. Containment: for each mode in the grid, the math value is in the interval
  (∀ (i : ℕ) (hi : i < u_impl.size),
    let k := GridMapping.fromIdx i M
    let (iv_re, iv_im) := u_impl[i]'hi
    let (q_re, q_im) := u_math.a k
    intervalContains iv_re q_re ∧ intervalContains iv_im q_im) ∧
  -- 3. Bounded support: modes outside the cube are zero
  (∀ (k : Lattice spatialDim), k ∉ ℓ2ZD.cube spatialDim M → u_math.a k = (0, 0))

/-! ## Axioms for Convolution Witness Theorem

These axioms encode assumptions about witness structure and grid mappings.
They should eventually be proven from the definitions, but are axiomatized
for now to complete the witness proof structure.
-/

-- Use the constant spatialDim = 1 from SemilinearHeat
-- (already brought into scope by open statement above)

/-- For spatialDim = 1, latticeToIdx and GridMapping.toIdx are the same -/
private lemma latticeToIdx_eq_toIdx (k : Lattice spatialDim) (M : ℕ) :
    SemilinearHeat.latticeToIdx k M = GridMapping.toIdx k M := by
  unfold SemilinearHeat.latticeToIdx GridMapping.toIdx
  -- Both compute (k 0 + M).toNat where 0 : Fin spatialDim
  -- k 0 and k ⟨0, NeZero.pos spatialDim⟩ are definitionally equal
  rfl

/-- For spatialDim = 1, any lattice point k has k i = k 0 for all i (since Fin 1 is singleton) -/
private lemma spatialDim_one_singleton (_k : Lattice spatialDim) (i : Fin spatialDim) :
    i = ⟨0, NeZero.pos spatialDim⟩ := by
  have h : spatialDim = 1 := rfl
  cases i
  rename_i val isLt
  -- After specializing to spatialDim = 1, i.val < 1, so i.val = 0
  have : val = 0 := by omega
  subst this
  rfl

/-- For lattice points k in the cube, toIdx and fromIdx are inverses -/
theorem fromIdx_latticeToIdx_cube (M : ℕ) (k : Lattice spatialDim)
    (hk : k ∈ SemilinearHeat.cubeListLattice M) :
    GridMapping.fromIdx (SemilinearHeat.latticeToIdx k M) M = k := by
  -- Rewrite using the equivalence
  rw [latticeToIdx_eq_toIdx]
  -- Apply GridMapping.fromIdx_toIdx
  apply GridMapping.fromIdx_toIdx
  · -- Need to show: -(M : ℤ) ≤ k 0 ∧ k 0 ≤ M
    -- k is in cubeListLattice M, which means k 0 ∈ [-M, M]
    simp only [SemilinearHeat.cubeListLattice, List.mem_map, List.mem_range] at hk
    -- hk: ∃ i < 2*M+1, k = (fun _ => (i:ℤ) - M)
    obtain ⟨i, hi_range, hk_eq⟩ := hk
    have hk0 : k ⟨0, NeZero.pos spatialDim⟩ = (i : ℤ) - M := by
      rw [← hk_eq]
    rw [hk0]
    omega
  · -- Need to show: ∀ i ≠ 0, k i = 0
    intro i hi
    -- For spatialDim = 1, there is only one index (0), so this is vacuous
    have : i = ⟨0, NeZero.pos spatialDim⟩ := spatialDim_one_singleton k i
    contradiction

/-- When the index is in bounds AND k is properly bounded, round-trip works.

    Note: We need the additional hypothesis that k 0 ≥ -M, because the condition
    latticeToIdx k M < 2*M+1 alone is not sufficient (if k 0 < -M, then toNat
    would give 0 < 2*M+1, but the round-trip fails).

    In the typical usage (convolution), this is true because k2 = k_i - k1 where
    both k_i and k1 are in [-M, M], and when the array access succeeds, we can
    derive that k2 must also be properly bounded. -/
theorem fromIdx_latticeToIdx_inbounds (M : ℕ) (k : Lattice spatialDim)
    (h_lower : -(M : ℤ) ≤ k ⟨0, NeZero.pos spatialDim⟩)
    (hk : SemilinearHeat.latticeToIdx k M < 2 * M + 1) :
    GridMapping.fromIdx (SemilinearHeat.latticeToIdx k M) M = k := by
  -- Rewrite using the equivalence
  rw [latticeToIdx_eq_toIdx]
  -- Apply GridMapping.fromIdx_toIdx
  apply GridMapping.fromIdx_toIdx
  · -- Need to show: -(M : ℤ) ≤ k 0 ∧ k 0 ≤ M
    -- We have h_lower : -(M : ℤ) ≤ k ⟨0, NeZero.pos spatialDim⟩
    have h_nonneg : 0 ≤ k ⟨0, NeZero.pos spatialDim⟩ + M := by omega
    -- Given non-negativity, toNat preserves the value
    unfold SemilinearHeat.latticeToIdx at hk
    -- hk: (k 0 + M).toNat < 2 * M + 1
    -- We need to connect k 0 to k ⟨0, NeZero.pos spatialDim⟩
    have hk0_eq : k 0 = k ⟨0, NeZero.pos spatialDim⟩ := rfl
    rw [hk0_eq] at hk
    constructor
    · -- -(M : ℤ) ≤ k ⟨0, NeZero.pos spatialDim⟩ follows from h_lower
      exact h_lower
    · -- k ⟨0, NeZero.pos spatialDim⟩ ≤ M follows from the index bound
      -- Since toNat preserves value when nonnegative, we have:
      -- (k0 + M).toNat = (k0 + M) as Nat (when k0 + M ≥ 0)
      -- So: ((k0 + M).toNat : ℤ) = k0 + M
      have h_tonat : ((k ⟨0, NeZero.pos spatialDim⟩ + M).toNat : ℤ) =
                     k ⟨0, NeZero.pos spatialDim⟩ + M := by
        have := Int.toNat_of_nonneg h_nonneg
        omega
      -- From hk, we have toNat < 2M+1, so when cast to ℤ:
      have : k ⟨0, NeZero.pos spatialDim⟩ + M < 2 * M + 1 := by
        omega
      omega
  · -- Need to show: ∀ i ≠ 0, k i = 0
    intro i hi
    have : i = ⟨0, NeZero.pos spatialDim⟩ := spatialDim_one_singleton k i
    contradiction

/-- If u witnesses v, then u_math has bounded support outside the cube.

This ensures that modes outside the witness cube are zero. -/
theorem witness_bounded_support {M : ℕ} {u_impl : StateArray} {u_math : SeqD_Rat spatialDim}
    (h : IsWitness M u_impl u_math) (k : Lattice spatialDim)
    (hk : k ∉ ℓ2ZD.cube spatialDim M) :
    u_math.a k = (0, 0) :=
  h.2.2 k hk


/-- When a lattice point is outside the witness cube, its coefficient is zero.

This is now a theorem that follows from the witness bounded support property.
Previously this was an axiom, but now it's derivable from IsWitness. -/
theorem out_of_cube_implies_zero (M : ℕ) (u_impl : StateArray) (u_math : ℓ2ZD.SeqD_Rat spatialDim)
    (h : IsWitness M u_impl u_math)
    (k : Lattice spatialDim)
    (hk : k ∉ ℓ2ZD.cube spatialDim M) :
    u_math.a k = (0, 0) :=
  witness_bounded_support h k hk

/-- cubeListLattice has no duplicates
-- TODO: BLOCKED - Lean elaborates the nested List.map to complex do-notation.
-- The mathematical property is true (List.range has no duplicates, and we apply
-- injective functions), but proving it requires extensive do-notation handling lemmas.
-- Now provable after map fusion refactor eliminates monadic elaboration issues. -/
lemma cubeListLattice_nodup (M : ℕ) :
    (SemilinearHeat.cubeListLattice M).Nodup := by
  unfold SemilinearHeat.cubeListLattice
  apply List.Nodup.map
  · -- Prove injectivity: (fun i => fun _ => (i:ℤ) - M) is injective
    intro i j hij
    -- hij : (fun _ => (i:ℤ) - M) = (fun _ => (j:ℤ) - M)
    have h_eq : ((i : ℤ) - (M : ℤ)) = ((j : ℤ) - (M : ℤ)) := by
      have := congr_fun hij ⟨0, by decide⟩
      exact this
    -- From equality of differences, deduce i = j
    have : (i : ℤ) = (j : ℤ) := by omega
    exact Nat.cast_injective this
  · -- List.range is nodup
    apply List.nodup_range

/-! ## Basic lemmas -/

/-- If u witnesses v, then u has the right size.

This is useful for array bounds checking in extraction code. -/
theorem witness_size {M : ℕ} {u_impl : StateArray} {u_math : SeqD_Rat spatialDim}
    (h : IsWitness M u_impl u_math) : u_impl.size = 2 * M + 1 :=
  h.1

/-- If u witnesses v, containment holds for all indices.

This is the main extraction lemma: given a witness and an index,
we can prove that the mathematical value is contained in the interval. -/
theorem witness_contains {M : ℕ} {u_impl : StateArray} {u_math : SeqD_Rat spatialDim}
    (h : IsWitness M u_impl u_math) (i : ℕ) (hi : i < u_impl.size) :
    let k := GridMapping.fromIdx i M
    let (iv_re, iv_im) := u_impl[i]'hi
    let (q_re, q_im) := u_math.a k
    intervalContains iv_re q_re ∧ intervalContains iv_im q_im :=
  h.2.1 i hi

/-! ## Helper lemmas for interval containment -/

/-- fromRat creates an interval that contains approximations of the target rational.
    For witness purposes, we need the slightly weaker property that an interval
    created with fromRat represents the mathematical value up to precision error. -/
private lemma fromRat_represents (q : ℚ) (p : ℕ) :
    ∃ x, IntervalDyadic.contains (IntervalDyadic.fromRat q p) x ∧
         |x - q| ≤ 1 / (2^p : ℚ) := by
  exact IntervalDyadic.fromRat_approximates q p

/-- For witness purposes, if fromRat creates an interval, that interval contains
    a value arbitrarily close to the target rational. This is sufficient for
    witnessing up to precision bounds. -/
private lemma fromRat_witnesses_rational (q : ℚ) (p : ℕ) :
    ∃ x, intervalContains (IntervalDyadic.fromRat q p) x ∧
         |x - q| ≤ 1 / (2^p : ℚ) := by
  obtain ⟨x, hx_contains, hx_close⟩ := fromRat_represents q p
  use x
  constructor
  · -- Show intervalContains from IntervalDyadic.contains
    unfold intervalContains IntervalDyadic.contains at *
    exact hx_contains
  · exact hx_close

/-! ## Sanity Check: Initial Data -/

/-- Computational initial data as Array: u₀(x) = A·sin(πx)
    For 1D: modes k=±1 have amplitude A, all others are zero -/
def initialDataArray (M : ℕ) (precision : ℕ) (amplitude : ℚ := 1/10) : StateArray :=
  let size := 2 * M + 1
  Array.ofFn (n := size) fun ⟨i, _⟩ =>
    let k : ℤ := (i : ℤ) - M
    if k = 1 ∨ k = -1 then
      (IntervalDyadic.fromRat amplitude precision, IntervalDyadic.zero)
    else
      (IntervalDyadic.zero, IntervalDyadic.zero)

/-- Mathematical initial data: u₀(x) = A·sin(πx) with amplitude A
    For 1D: coefficients at k=±1 are A, rest are zero -/
def initialData_math (amplitude : ℚ := 1/10) : SeqD_Rat spatialDim where
  a := fun k =>
    if k = (fun _ => (1 : ℤ)) then (amplitude, 0)
    else if k = (fun _ => (-1 : ℤ)) then (amplitude, 0)
    else (0, 0)
  finite_support := by
    -- The support is {k=1, k=-1}, which is finite
    have h_support : {k : Lattice spatialDim | (if k = (fun _ => (1 : ℤ)) then (amplitude, (0 : ℚ))
                                                 else if k = (fun _ => (-1 : ℤ)) then (amplitude, (0 : ℚ))
                                                 else ((0 : ℚ), (0 : ℚ))) ≠ ((0 : ℚ), (0 : ℚ))} ⊆
                      ({(fun _ => (1 : ℤ))} ∪ {(fun _ => (-1 : ℤ))} : Set (Lattice spatialDim)) := by
      intro k hk
      simp only [Set.mem_setOf_eq] at hk
      by_cases h1 : k = (fun _ => (1 : ℤ))
      · left; exact h1
      · by_cases h2 : k = (fun _ => (-1 : ℤ))
        · right; exact h2
        · exfalso
          simp [h1, h2] at hk
    have h_finite : Set.Finite ({(fun _ => (1 : ℤ))} ∪ {(fun _ => (-1 : ℤ))} : Set (Lattice spatialDim)) :=
      Set.Finite.union (Set.finite_singleton _) (Set.finite_singleton _)
    exact Set.Finite.subset h_finite h_support

/-- The computational initial data witnesses the mathematical initial data -/
theorem initialData_witnesses (M : ℕ) (precision : ℕ) (amplitude : ℚ := 1/10)
    (_hM : M ≥ 1) :
    IsWitness M
      (initialDataArray M precision amplitude)
      (initialData_math amplitude) := by
  unfold IsWitness
  constructor
  · -- Size check: array has 2M+1 elements
    unfold initialDataArray
    simp [Array.ofFn]
  constructor
  · -- Containment check
    intro i hi
    -- Define k for this index
    let k := GridMapping.fromIdx (d := spatialDim) i M
    -- Get the k value as an integer (for pattern matching in the array)
    let k_val : ℤ := (i : ℤ) - M
    -- The goal has the form: let k := ...; match arr[i] with | (iv_re, iv_im) => match math.a k with | (q_re, q_im) => contains iv_re q_re ∧ contains iv_im q_im
    -- We need to show this by cases on k_val

    by_cases h1_val : k_val = 1
    · -- Case k_val=1: array has (fromRat amplitude, zero), math has (amplitude, 0)
      -- First show that k = (fun _ => 1)
      have hk : k = (fun _ => (1 : ℤ)) := by
        unfold k GridMapping.fromIdx
        funext j
        by_cases hj : j = ⟨0, NeZero.pos spatialDim⟩
        · simp [hj, k_val, h1_val]
        · -- For j ≠ 0, the result is 0 in 1D, but we need k = fun _ => 1
          -- In 1D, j must be 0, so this case is impossible
          have : j.val < 1 := j.2
          interval_cases j.val
          · -- j.val = 0, so j = ⟨0, ...⟩, contradicting hj
            exfalso
            apply hj
            ext
            simp
      -- Simplify the array lookup
      show (let k := GridMapping.fromIdx (d := spatialDim) i M
            let (iv_re, iv_im) := (initialDataArray M precision amplitude)[i]'hi
            let (q_re, q_im) := (initialData_math amplitude).a k
            intervalContains iv_re q_re ∧ intervalContains iv_im q_im)
      -- Show array[i] = (fromRat amplitude precision, zero)
      have harr : (initialDataArray M precision amplitude)[i]'hi =
                  (IntervalDyadic.fromRat amplitude precision, IntervalDyadic.zero) := by
        unfold initialDataArray
        simp only [Array.getElem_ofFn]
        show (if k_val = 1 ∨ k_val = -1 then
                (IntervalDyadic.fromRat amplitude precision, IntervalDyadic.zero)
              else
                (IntervalDyadic.zero, IntervalDyadic.zero)) =
             (IntervalDyadic.fromRat amplitude precision, IntervalDyadic.zero)
        simp [h1_val]
      -- Show math.a k = (amplitude, 0)
      have hmath : (initialData_math amplitude).a k = (amplitude, 0) := by
        simp only [initialData_math, hk]
        rfl
      -- Now complete the proof
      simp [harr]
      have h_re : ((initialData_math amplitude).a k).1 = amplitude := by rw [hmath]
      have h_im : ((initialData_math amplitude).a k).2 = 0 := by rw [hmath]
      rw [h_re, h_im]
      exact ⟨fromRat_contains_rat amplitude precision, zero_contains_zero⟩
    · by_cases hn1_val : k_val = -1
      · -- Case k_val=-1: similar to k_val=1
        have hk : k = (fun _ => (-1 : ℤ)) := by
          unfold k GridMapping.fromIdx
          funext j
          by_cases hj : j = ⟨0, NeZero.pos spatialDim⟩
          · simp [hj, k_val, hn1_val]
          · -- For j ≠ 0, the result is 0 in 1D, but we need k = fun _ => -1
            -- In 1D, j must be 0, so this case is impossible
            have : j.val < 1 := j.2
            interval_cases j.val
            · -- j.val = 0, so j = ⟨0, ...⟩, contradicting hj
              exfalso
              apply hj
              ext
              simp
        -- Simplify the array lookup
        show (let k := GridMapping.fromIdx (d := spatialDim) i M
              let (iv_re, iv_im) := (initialDataArray M precision amplitude)[i]'hi
              let (q_re, q_im) := (initialData_math amplitude).a k
              intervalContains iv_re q_re ∧ intervalContains iv_im q_im)
        -- Show array[i] = (fromRat amplitude precision, zero)
        have harr : (initialDataArray M precision amplitude)[i]'hi =
                    (IntervalDyadic.fromRat amplitude precision, IntervalDyadic.zero) := by
          unfold initialDataArray
          simp only [Array.getElem_ofFn]
          show (if k_val = 1 ∨ k_val = -1 then
                  (IntervalDyadic.fromRat amplitude precision, IntervalDyadic.zero)
                else
                  (IntervalDyadic.zero, IntervalDyadic.zero)) =
               (IntervalDyadic.fromRat amplitude precision, IntervalDyadic.zero)
          simp [hn1_val]
        -- Show math.a k = (amplitude, 0)
        have hmath : (initialData_math amplitude).a k = (amplitude, 0) := by
          simp only [initialData_math, hk]
          rfl
        -- Now complete the proof
        simp [harr]
        have h_re : ((initialData_math amplitude).a k).1 = amplitude := by rw [hmath]
        have h_im : ((initialData_math amplitude).a k).2 = 0 := by rw [hmath]
        rw [h_re, h_im]
        exact ⟨fromRat_contains_rat amplitude precision, zero_contains_zero⟩
      · -- Case k_val ≠ ±1: array has (zero, zero), math has (0, 0)
        have hk_ne1 : k ≠ (fun _ => (1 : ℤ)) := by
          intro hk
          have : k_val = 1 := by
            unfold k GridMapping.fromIdx at hk
            have := congr_fun hk ⟨0, NeZero.pos spatialDim⟩
            exact this
          exact h1_val this
        have hk_ne_neg1 : k ≠ (fun _ => (-1 : ℤ)) := by
          intro hk
          have : k_val = -1 := by
            unfold k GridMapping.fromIdx at hk
            have := congr_fun hk ⟨0, NeZero.pos spatialDim⟩
            exact this
          exact hn1_val this
        -- Simplify the array lookup
        show (let k := GridMapping.fromIdx (d := spatialDim) i M
              let (iv_re, iv_im) := (initialDataArray M precision amplitude)[i]'hi
              let (q_re, q_im) := (initialData_math amplitude).a k
              intervalContains iv_re q_re ∧ intervalContains iv_im q_im)
        -- Show array[i] = (zero, zero)
        have harr : (initialDataArray M precision amplitude)[i]'hi =
                    (IntervalDyadic.zero, IntervalDyadic.zero) := by
          unfold initialDataArray
          simp only [Array.getElem_ofFn]
          show (if k_val = 1 ∨ k_val = -1 then
                  (IntervalDyadic.fromRat amplitude precision, IntervalDyadic.zero)
                else
                  (IntervalDyadic.zero, IntervalDyadic.zero)) =
               (IntervalDyadic.zero, IntervalDyadic.zero)
          simp [h1_val, hn1_val]
        -- Show math.a k = (0, 0)
        have hmath : (initialData_math amplitude).a k = (0, 0) := by
          simp only [initialData_math, hk_ne1, hk_ne_neg1]
          simp
        -- Now complete the proof
        simp [harr]
        have h_re : ((initialData_math amplitude).a k).1 = 0 := by rw [hmath]
        have h_im : ((initialData_math amplitude).a k).2 = 0 := by rw [hmath]
        rw [h_re, h_im]
        exact ⟨zero_contains_zero, zero_contains_zero⟩
  · -- Bounded support: modes outside the cube are zero
    intro k hk
    -- hk : k ∉ cube spatialDim M
    -- Need: (if k = 1 then (A,0) else if k = -1 then (A,0) else (0,0)) = (0,0)

    unfold ℓ2ZD.cube at hk
    simp only [Fintype.mem_piFinset, Finset.mem_Icc, not_forall] at hk
    -- hk : ∃ i, k i < -↑M ∨ M < k i

    -- For spatialDim = 1, the only coordinate is 0
    obtain ⟨i, hi⟩ := hk
    have i_eq_zero : i = 0 := by
      have : Subsingleton (Fin spatialDim) := by rw [show spatialDim = 1 from rfl]; infer_instance
      exact Subsingleton.elim i 0
    rw [i_eq_zero] at hi
    -- hi : k 0 < -↑M ∨ M < k 0

    simp only [initialData_math]
    -- Show k ≠ (fun _ => 1) and k ≠ (fun _ => -1) using hi and M ≥ 1
    by_cases h1 : k = (fun _ => 1)
    · -- k 0 = 1, but hi says k 0 < -M or k 0 > M, and M ≥ 1
      exfalso
      have : k 0 = 1 := by rw [h1]
      omega
    · by_cases h2 : k = (fun _ => -1)
      · exfalso
        have : k 0 = -1 := by rw [h2]
        omega
      · simp [h1, h2]

/-! ## Galerkin Projection -/

/-- The Galerkin projection operator: truncates a sequence to cube M.

This operator represents what happens in practice when we store only M modes
in finite memory. The full convolution u*v has support in cube 2M, but we
can only store cube M, so we implicitly project.

Making this projection explicit in the math ensures IsWitness can prove
that the finite array faithfully represents the truncated mathematical result. -/
def truncate_math (M : ℕ) (u : SeqD_Rat spatialDim) : SeqD_Rat spatialDim where
  a := fun k => if k ∈ ℓ2ZD.cube spatialDim M then u.a k else (0, 0)
  finite_support := by
    -- Support is subset of cube M, which is finite
    have h := u.finite_support
    apply Set.Finite.subset h
    intro k hk
    simp only [Set.mem_setOf_eq] at hk ⊢
    by_contra h_zero
    simp [h_zero] at hk

/-! ## Mathematical Model: Rational Evolution -/

/-- Mathematical model of Laplacian weight in rational arithmetic -/
def laplacianWeight_math (k : Lattice spatialDim) : ℚ :=
  SemilinearHeat.laplacianWeight_rat k

/-! ## Convolution Preservation -/

/-! ## Laplacian Weight Witness -/

/-- Helper: If an interval contains a larger value, it also contains any smaller value.

    This is monotonicity of interval containment: if q1 ≤ q2 and [l,u] contains q2,
    then as long as l ≤ q1, the interval also contains q1. -/
private lemma intervalContains_of_le (iv : IntervalD) (q1 q2 : ℚ)
    (h_le : q1 ≤ q2) (h_contains : intervalContains iv q2) (h_lower : DyadicCanonical.toRat iv.lower ≤ q1) :
    intervalContains iv q1 := by
  unfold intervalContains at *
  obtain ⟨h_lower_q2, h_upper⟩ := h_contains
  constructor
  · exact h_lower
  · exact le_trans h_le h_upper

/-- The interval-based laplacian weight witnesses the rational laplacian weight.

This lemma bridges the computational implementation (which uses π as an interval)
with the mathematical specification (which uses a rational upper bound for π).

**Key property**: laplacianWeight_interval computes π² · k² using interval arithmetic,
which must contain the rational approximation π_rat_ub² · k².

**Note**: Since π_rat_ub is an upper bound on π, and we use it to compute eigenvalues,
the interval [pi_lower, pi_upper] must contain both π and π_rat_ub.

**Proof strategy**:
1. Show pi_interval contains pi_rat_ub
2. Apply mul_preserves_containment for squaring
3. Apply mul_preserves_containment for multiplication by k²
-/
theorem laplacian_weight_is_witness (k : Lattice spatialDim) (p : ℕ) :
    intervalContains
      (SemilinearHeat.laplacianWeight_interval k p)
      (SemilinearHeat.laplacianWeight_rat k) := by
  unfold SemilinearHeat.laplacianWeight_interval
  unfold SemilinearHeat.laplacianWeight_rat
  unfold SemilinearHeat.pi_interval
  unfold SemilinearHeat.pi_rat_ub
  unfold SemilinearHeat.pi_lower
  unfold SemilinearHeat.pi_upper

  -- Extract k value
  let k_val := k 0

  -- Step 1: Show pi_interval contains pi_rat_ub
  -- pi_interval = [fromRat(314159/100000).lower, fromRat(31416/10000).upper]
  -- We need to show this contains 31416/10000
  have h_pi : intervalContains
      (let approx := IntervalDyadic.fromRat (314159/100000) p
       let upper_approx := IntervalDyadic.fromRat (31416/10000) p
       ⟨approx.lower, upper_approx.upper, by
         have h_rat : (314159 : ℚ) / 100000 < 31416 / 10000 := by norm_num
         have h_lower : IntervalDyadic.contains approx (314159/100000) := IntervalDyadic.fromRat_contains (314159/100000) p
         have h_upper : IntervalDyadic.contains upper_approx (31416/10000) := IntervalDyadic.fromRat_contains (31416/10000) p
         unfold IntervalDyadic.contains at h_lower h_upper
         have h1 : DyadicCanonical.toRat approx.lower ≤ 314159/100000 := h_lower.1
         have h2 : 31416/10000 ≤ DyadicCanonical.toRat upper_approx.upper := h_upper.2
         exact (DyadicCanonical.le_iff_toRat_le _ _).mpr (calc DyadicCanonical.toRat approx.lower
             ≤ 314159/100000 := h1
           _ ≤ 31416/10000 := le_of_lt h_rat
           _ ≤ DyadicCanonical.toRat upper_approx.upper := h2)⟩)
      (31416/10000) := by
    unfold intervalContains
    constructor
    · -- Lower bound: approx.lower ≤ 31416/10000
      have h_lower : IntervalDyadic.contains (IntervalDyadic.fromRat (314159/100000) p) (314159/100000) :=
        IntervalDyadic.fromRat_contains (314159/100000) p
      unfold IntervalDyadic.contains at h_lower
      have h1 : DyadicCanonical.toRat (IntervalDyadic.fromRat (314159/100000) p).lower ≤ 314159/100000 := h_lower.1
      calc DyadicCanonical.toRat (IntervalDyadic.fromRat (314159/100000) p).lower
          ≤ 314159/100000 := h1
        _ ≤ 31416/10000 := by norm_num
    · -- Upper bound: 31416/10000 ≤ upper_approx.upper
      have h_upper : IntervalDyadic.contains (IntervalDyadic.fromRat (31416/10000) p) (31416/10000) :=
        IntervalDyadic.fromRat_contains (31416/10000) p
      unfold IntervalDyadic.contains at h_upper
      exact h_upper.2

  -- Step 2: Show k_val interval contains k_val rational
  have h_k : intervalContains
      (IntervalDyadic.fromRat (k_val : ℚ) p)
      (k_val : ℚ) := fromRat_contains_rat (k_val : ℚ) p

  -- Step 3: pi² contains pi_rat_ub²
  have h_pi_sq : intervalContains
      (IntervalDyadic.mul
        (let approx := IntervalDyadic.fromRat (314159/100000) p
         let upper_approx := IntervalDyadic.fromRat (31416/10000) p
         ⟨approx.lower, upper_approx.upper, by
           have h_rat : (314159 : ℚ) / 100000 < 31416 / 10000 := by norm_num
           have h_lower : IntervalDyadic.contains approx (314159/100000) := IntervalDyadic.fromRat_contains (314159/100000) p
           have h_upper : IntervalDyadic.contains upper_approx (31416/10000) := IntervalDyadic.fromRat_contains (31416/10000) p
           unfold IntervalDyadic.contains at h_lower h_upper
           have h1 : DyadicCanonical.toRat approx.lower ≤ 314159/100000 := h_lower.1
           have h2 : 31416/10000 ≤ DyadicCanonical.toRat upper_approx.upper := h_upper.2
           exact (DyadicCanonical.le_iff_toRat_le _ _).mpr (calc DyadicCanonical.toRat approx.lower
               ≤ 314159/100000 := h1
             _ ≤ 31416/10000 := le_of_lt h_rat
             _ ≤ DyadicCanonical.toRat upper_approx.upper := h2)⟩)
        (let approx := IntervalDyadic.fromRat (314159/100000) p
         let upper_approx := IntervalDyadic.fromRat (31416/10000) p
         ⟨approx.lower, upper_approx.upper, by
           have h_rat : (314159 : ℚ) / 100000 < 31416 / 10000 := by norm_num
           have h_lower : IntervalDyadic.contains approx (314159/100000) := IntervalDyadic.fromRat_contains (314159/100000) p
           have h_upper : IntervalDyadic.contains upper_approx (31416/10000) := IntervalDyadic.fromRat_contains (31416/10000) p
           unfold IntervalDyadic.contains at h_lower h_upper
           have h1 : DyadicCanonical.toRat approx.lower ≤ 314159/100000 := h_lower.1
           have h2 : 31416/10000 ≤ DyadicCanonical.toRat upper_approx.upper := h_upper.2
           exact (DyadicCanonical.le_iff_toRat_le _ _).mpr (calc DyadicCanonical.toRat approx.lower
               ≤ 314159/100000 := h1
             _ ≤ 31416/10000 := le_of_lt h_rat
             _ ≤ DyadicCanonical.toRat upper_approx.upper := h2)⟩)
        p)
      ((31416/10000 : ℚ) * (31416/10000 : ℚ)) := by
    apply mul_preserves_containment
    exact h_pi
    exact h_pi

  -- Step 4: k² contains k_val²
  have h_k_sq : intervalContains
      (IntervalDyadic.mul
        (IntervalDyadic.fromRat (k_val : ℚ) p)
        (IntervalDyadic.fromRat (k_val : ℚ) p) p)
      ((k_val : ℚ) * (k_val : ℚ)) := by
    apply mul_preserves_containment
    exact h_k
    exact h_k

  -- Step 5: π² · k² contains pi_rat_ub² · k_val²
  apply mul_preserves_containment
  exact h_pi_sq
  exact h_k_sq

/-- Helper: cubeListLattice covers the same points as the cube Finset.

    For spatialDim = 1, lattice points are constant functions (Fin 1 → ℤ),
    so membership reduces to checking whether the single coordinate is in [-M, M]. -/
theorem cubeListLattice_covers_cube (M : ℕ) :
    ∀ k, k ∈ SemilinearHeat.cubeListLattice M ↔ k ∈ ℓ2ZD.cube spatialDim M := by
  intro k
  simp only [SemilinearHeat.cubeListLattice, ℓ2ZD.cube, List.mem_map, List.mem_range,
             Fintype.mem_piFinset, Finset.mem_Icc]
  constructor
  · -- Forward: k ∈ list → k ∈ finset
    -- Given: ∃ i < 2*M+1, k = (fun _ => (i:ℤ) - M)
    -- Goal: ∀ j, -(M:ℤ) ≤ k j ≤ M
    intro ⟨i, hi_range, hk_eq⟩ j
    rw [← hk_eq]
    simp only []
    omega
  · -- Backward: k ∈ finset → k ∈ list
    -- Given: ∀ j, -(M:ℤ) ≤ k j ≤ M
    -- Goal: ∃ i < 2*M+1, k = (fun _ => (i:ℤ) - M)
    intro h_in_cube
    -- Get the value at index 0
    let z := k ⟨0, NeZero.pos spatialDim⟩
    -- Use i = (z + M).toNat
    use (z + M).toNat
    constructor
    · -- Show (z + M).toNat < 2*M+1
      have h0 := h_in_cube ⟨0, NeZero.pos spatialDim⟩
      omega
    · -- Show k = fun _ => ((z + M).toNat : ℤ) - M
      ext i
      -- For spatialDim = 1, Fin 1 is a subsingleton, so all functions are determined by their value at 0
      have h_dim : spatialDim = 1 := rfl
      have : i = ⟨0, NeZero.pos spatialDim⟩ := by
        have : Subsingleton (Fin spatialDim) := by rw [h_dim]; infer_instance
        exact Subsingleton.elim i _
      rw [this]
      have h0 := h_in_cube ⟨0, NeZero.pos spatialDim⟩
      omega

/-- If k is in cubeListLattice M, its lattice index is in bounds. -/
lemma cubeListLattice_idx_bound (M : ℕ) (k : Lattice spatialDim)
    (hk : k ∈ SemilinearHeat.cubeListLattice M) :
    SemilinearHeat.latticeToIdx k M < 2 * M + 1 := by
  -- k ∈ cubeListLattice M means k ∈ cube M
  have hk_cube := (cubeListLattice_covers_cube M k).mp hk
  -- So -M ≤ k 0 ≤ M
  unfold ℓ2ZD.cube at hk_cube
  simp only [Fintype.mem_piFinset, Finset.mem_Icc] at hk_cube
  have hk0 := hk_cube ⟨0, NeZero.pos spatialDim⟩
  -- Therefore 0 ≤ k 0 + M ≤ 2M
  have h_nonneg : 0 ≤ k ⟨0, NeZero.pos spatialDim⟩ + (M : ℤ) := by omega
  have h_upper : k ⟨0, NeZero.pos spatialDim⟩ + (M : ℤ) ≤ 2 * M := by omega
  -- So (k 0 + M).toNat ≤ 2M < 2M+1
  unfold SemilinearHeat.latticeToIdx
  calc (k ⟨0, NeZero.pos spatialDim⟩ + (M : ℤ)).toNat
    = Int.toNat (k ⟨0, NeZero.pos spatialDim⟩ + (M : ℤ)) := rfl
    _ ≤ Int.toNat (2 * M) := by
        apply Int.toNat_le_toNat
        exact h_upper
    _ = 2 * M := Int.toNat_natCast (2 * M)
    _ < 2 * M + 1 := Nat.lt_succ_self _

/-- Helper: foldl with addition and initial value relates to foldl with shifted initial value -/
private lemma foldl_add_shift {α β : Type*} [AddCommMonoid β] (f : α → β) (xs : List α) (init : β) :
    xs.foldl (fun acc x => acc + f x) init = init + xs.foldl (fun acc x => acc + f x) 0 := by
  induction xs generalizing init with
  | nil => simp [List.foldl]
  | cons x xs ih =>
    simp only [List.foldl]
    rw [ih (init + f x)]
    have h_zero : (0 : β) + f x = f x := by simp
    rw [h_zero, ih (f x)]
    ac_rfl

/-- List fold over cube equals Finset sum over cube

**Proof Strategy**:
1. Show foldl equals List.sum over mapped list
2. Show List.sum equals Finset.sum using nodup and coverage properties
-/
lemma foldl_eq_sum_cube (M : ℕ) (f : Lattice spatialDim → ℚ) :
    (SemilinearHeat.cubeListLattice M).foldl (fun acc x => acc + f x) 0 =
    Finset.sum (ℓ2ZD.cube spatialDim M) f := by
  have h_nodup := cubeListLattice_nodup M
  have h_covers := cubeListLattice_covers_cube M

  -- Key fact: cubeListLattice.toFinset = cube
  have h_list_eq : (SemilinearHeat.cubeListLattice M).toFinset = ℓ2ZD.cube spatialDim M := by
    ext k
    simp only [List.mem_toFinset]
    exact h_covers k

  -- Prove by induction on the list structure
  -- The idea: both compute the same sum over the same set of elements
  have h_eq : ∀ (xs : List (Lattice spatialDim)) (h : xs.Nodup),
      xs.foldl (fun acc x => acc + f x) 0 = xs.toFinset.sum f := by
    intro xs h_nd
    induction xs with
    | nil =>
      simp [List.foldl, List.toFinset, Finset.sum_empty]
    | cons x xs ih =>
      have h_notin : x ∉ xs := by
        intro h_mem
        have : ¬(x :: xs).Nodup := by
          intro h_nd_cons
          have := List.nodup_cons.mp h_nd_cons |>.1
          exact this h_mem
        exact this h_nd
      have h_nd_xs : xs.Nodup := by
        cases h_nd
        assumption
      simp only [List.foldl, List.toFinset]
      have h_init : (0 : ℚ) + f x = f x := by simp
      rw [h_init]
      rw [foldl_add_shift f xs (f x)]
      rw [ih h_nd_xs]
      rw [← Finset.sum_insert (by simp [List.mem_toFinset, h_notin])]
      congr 1
      ext y
      simp only [Finset.mem_insert, List.mem_toFinset]
      constructor
      · intro h
        cases h with
        | inl h_eq => simp [h_eq]
        | inr h_mem => simp [h_mem]
      · intro h
        simp at h
        exact h

  rw [h_eq _ h_nodup, h_list_eq]

  /-- If toNat(k 0 + M) ≥ 2M+1, then k is outside cube M.

  This handles toNat non-injection: when negative, toNat gives 0,
  so the bound tells us k 0 < -M. When nonnegative, toNat preserves
  value, so k 0 > M. Either way, k ∉ cube M. -/
  private lemma toNat_ge_implies_out_of_cube (M : ℕ) (k : Lattice spatialDim)
      (h : (k ⟨0, NeZero.pos spatialDim⟩ + ↑M).toNat ≥ 2 * M + 1) :
      k ∉ ℓ2ZD.cube spatialDim M := by
    unfold ℓ2ZD.cube
    simp only [Fintype.mem_piFinset, Finset.mem_Icc, not_forall]
    use ⟨0, NeZero.pos spatialDim⟩
    -- Goal: ¬(-M ≤ k 0 ∧ k 0 ≤ M)
    intro ⟨h_lower, h_upper⟩
    -- Have: -M ≤ k 0 ≤ M, so -M ≤ k 0 + M ≤ 2M
    -- From h: (k 0 + M).toNat ≥ 2M+1
    by_cases hneg : k ⟨0, NeZero.pos spatialDim⟩ + ↑M < 0
    · -- Negative case: k 0 + M < 0
      -- But -M ≤ k 0, so 0 ≤ k 0 + M, contradiction
      omega
    · -- Nonnegative case: toNat preserves value
      push_neg at hneg
      -- From h: toNat ≥ 2M+1 and toNat = value (when nonneg), get k 0 + M ≥ 2M+1
      have h_value : k ⟨0, NeZero.pos spatialDim⟩ + ↑M ≥ 2 * ↑M + 1 := by
        have h_bound : (k ⟨0, NeZero.pos spatialDim⟩ + ↑M).toNat ≥ 2 * M + 1 := h
        have h_cast : ((k ⟨0, NeZero.pos spatialDim⟩ + ↑M).toNat : ℤ) ≥ (2 * M + 1 : ℤ) := by
          exact Int.ofNat_le.mpr h_bound
        rw [Int.toNat_of_nonneg hneg] at h_cast
        exact h_cast
      -- But k 0 ≤ M, so k 0 + M ≤ 2M, contradiction
      omega


set_option maxHeartbeats 2000000

/-- Specification lemma for convolve_Array structure.

    This lemma exposes the computational structure of convolve_Array WITHOUT
    dependent types, making it usable in proofs. It states that accessing
    element i of the convolution array gives you the result of a fold over
    the cube lattice.

    CRITICAL: Now includes geometric bounds check BEFORE toNat to prevent aliasing.

    This is the bridge between the opaque Array.ofFn definition and the
    mathematical properties we want to prove. -/
theorem convolve_Array_spec (u1 u2 : StateArray) (M p : ℕ) (i : ℕ)
    (hi : i < (SemilinearHeat.convolve_Array u1 u2 M p).size) :
    (SemilinearHeat.convolve_Array u1 u2 M p)[i]'hi =
    let k_i := SemilinearHeat.idxToLattice i M
    let result := (SemilinearHeat.cubeListLattice M).foldl (fun (acc_re, acc_im) k1 =>
      let k2 : Lattice spatialDim := fun j => k_i j - k1 j
      -- NEW: Check geometric bounds BEFORE toNat
      if -(M : ℤ) ≤ k2 ⟨0, NeZero.pos spatialDim⟩ ∧ k2 ⟨0, NeZero.pos spatialDim⟩ ≤ M then
        let i1 := SemilinearHeat.latticeToIdx k1 M
        let i2 := SemilinearHeat.latticeToIdx k2 M
        if h1 : i1 < u1.size then
          if h2 : i2 < u2.size then
            let (u1_re, u1_im) := u1[i1]
            let (u2_re, u2_im) := u2[i2]
            (IntervalDyadic.add acc_re (IntervalDyadic.sub (IntervalDyadic.mul u1_re u2_re p) (IntervalDyadic.mul u1_im u2_im p) p) p,
             IntervalDyadic.add acc_im (IntervalDyadic.add (IntervalDyadic.mul u1_re u2_im p) (IntervalDyadic.mul u1_im u2_re p) p) p)
          else (acc_re, acc_im)
        else (acc_re, acc_im)
      else (acc_re, acc_im)  -- Out-of-bounds: explicit zero
    ) (IntervalDyadic.zero, IntervalDyadic.zero)
    result := by
  unfold SemilinearHeat.convolve_Array
  simp only [Array.getElem_ofFn]

/-- Helper lemma: A single convolution fold term (real part) is witnessed.

    This lemma encapsulates the witness logic for one term in the convolution sum,
    handling all cases with the new geometric bounds check. -/
private lemma witness_fold_term_re (M : ℕ) (p : ℕ)
    (u1_impl u2_impl : StateArray) (u1_math u2_math : SeqD_Rat spatialDim)
    (h1 : IsWitness M u1_impl u1_math) (h2 : IsWitness M u2_impl u2_math)
    (k_i k1 : Lattice spatialDim) (hk1 : k1 ∈ SemilinearHeat.cubeListLattice M) :
    let k2 := fun j => k_i j - k1 j
    let f_iv_re := if -(M : ℤ) ≤ k2 ⟨0, NeZero.pos spatialDim⟩ ∧ k2 ⟨0, NeZero.pos spatialDim⟩ ≤ M then
                     let i1 := SemilinearHeat.latticeToIdx k1 M
                     let i2 := SemilinearHeat.latticeToIdx k2 M
                     if h1_idx : i1 < u1_impl.size then
                       if h2_idx : i2 < u2_impl.size then
                         let (u1_re, u1_im) := u1_impl[i1]
                         let (v2_re, v2_im) := u2_impl[i2]
                         IntervalDyadic.sub (IntervalDyadic.mul u1_re v2_re p) (IntervalDyadic.mul u1_im v2_im p) p
                       else IntervalDyadic.zero
                     else IntervalDyadic.zero
                   else IntervalDyadic.zero
    let f_rat_re := let (u1_re, u1_im) := u1_math.a k1
                    let (u2_re, u2_im) := u2_math.a k2
                    u1_re * u2_re - u1_im * u2_im
    intervalContains f_iv_re f_rat_re := by
  intro k2 f_iv_re f_rat_re
  -- Get witness sizes
  have h1_size : u1_impl.size = 2 * M + 1 := witness_size h1
  have h2_size : u2_impl.size = 2 * M + 1 := witness_size h2

  -- NEW: Case split on geometric bounds FIRST
  by_cases hk2_bounds : -(M : ℤ) ≤ k2 ⟨0, NeZero.pos spatialDim⟩ ∧ k2 ⟨0, NeZero.pos spatialDim⟩ ≤ M
  · -- k2 is in bounds geometrically
    let i1 := SemilinearHeat.latticeToIdx k1 M
    let i2 := SemilinearHeat.latticeToIdx k2 M
    by_cases h1_idx : i1 < u1_impl.size
    · by_cases h2_idx : i2 < u2_impl.size
      · -- Both in bounds: use witnesses
        have h_u1 := witness_contains h1 i1 h1_idx
        have h_u2 := witness_contains h2 i2 h2_idx
        obtain ⟨h_u1_re, h_u1_im⟩ := h_u1
        obtain ⟨h_u2_re, h_u2_im⟩ := h_u2

        -- Convert witness facts to use k1, k2 instead of fromIdx
        have h_k1_eq : GridMapping.fromIdx i1 M = k1 := fromIdx_latticeToIdx_cube M k1 hk1
        have h_k2_eq : GridMapping.fromIdx i2 M = k2 := by
          -- NOW PROVABLE! We have hk2_bounds : k2 is in [-M, M]
          unfold i2
          apply fromIdx_latticeToIdx_inbounds M k2
          · exact hk2_bounds.1  -- Lower bound from geometric bounds check
          · rw [← h2_size]      -- latticeToIdx k2 M < 2*M+1
            exact h2_idx

        -- Rewrite witness facts to use k1, k2
        have h_u1_re' : intervalContains (u1_impl[i1]'h1_idx).1 (u1_math.a k1).1 := by
          rw [←h_k1_eq]; exact h_u1_re
        have h_u1_im' : intervalContains (u1_impl[i1]'h1_idx).2 (u1_math.a k1).2 := by
          rw [←h_k1_eq]; exact h_u1_im
        have h_u2_re' : intervalContains (u2_impl[i2]'h2_idx).1 (u2_math.a k2).1 := by
          rw [←h_k2_eq]; exact h_u2_re
        have h_u2_im' : intervalContains (u2_impl[i2]'h2_idx).2 (u2_math.a k2).2 := by
          rw [←h_k2_eq]; exact h_u2_im

        -- Real part: u1_re * u2_re - u1_im * u2_im
        unfold f_iv_re f_rat_re
        rw [if_pos hk2_bounds, dif_pos h1_idx, dif_pos h2_idx]
        exact sub_preserves_containment _ _ _ _ p
          (mul_preserves_containment _ _ _ _ p h_u1_re' h_u2_re')
          (mul_preserves_containment _ _ _ _ p h_u1_im' h_u2_im')
      · -- i2 out of bounds: returns zero, witnesses 0
        unfold f_iv_re f_rat_re
        rw [if_pos hk2_bounds, dif_pos h1_idx, dif_neg h2_idx]
        have h_u2_zero : u2_math.a k2 = (0, 0) := by
          apply out_of_cube_implies_zero M u2_impl u2_math h2
          -- Need to show k2 ∉ cube
          have : ¬(latticeToIdx k2 M < u2_impl.size) := h2_idx
          rw [h2_size] at this
          unfold latticeToIdx at this
          -- this : ¬((k2 0 + ↑M).toNat < 2 * M + 1)
          -- If toNat ≥ 2M+1, then k2 is outside the cube
          have h_tonat_bound : (k2 ⟨0, NeZero.pos spatialDim⟩ + ↑M).toNat ≥ 2 * M + 1 := by
            exact Nat.le_of_not_lt this
          exact toNat_ge_implies_out_of_cube M k2 h_tonat_bound
        simp [h_u2_zero]
        exact zero_contains_zero
    · -- i1 out of bounds: impossible, since k1 ∈ cubeListLattice implies i1 in bounds
      exfalso
      -- k1 ∈ cubeListLattice M means k1 = (fun _ => (n:ℤ) - M) where n < 2*M+1
      simp only [SemilinearHeat.cubeListLattice, List.mem_map, List.mem_range] at hk1
      obtain ⟨n, hn_range, hk1_eq⟩ := hk1
      -- i1 = latticeToIdx k1 M = (k1 0 + M).toNat = n
      have h_i1_eq : i1 = n := by
        show SemilinearHeat.latticeToIdx k1 M = n
        unfold SemilinearHeat.latticeToIdx
        rw [← hk1_eq]
        simp only []
        omega
      rw [h_i1_eq, h1_size] at h1_idx
      omega
  · -- k2 out of geometric bounds
    unfold f_iv_re f_rat_re
    rw [if_neg hk2_bounds]
    have h_u2_zero : u2_math.a k2 = (0, 0) := by
      apply out_of_cube_implies_zero M u2_impl u2_math h2
      -- k2 ∉ cube because ¬(-(M : ℤ) ≤ k2 0 ∧ k2 0 ≤ M)
      unfold ℓ2ZD.cube
      simp only [Fintype.mem_piFinset, Finset.mem_Icc, not_forall]
      use ⟨0, NeZero.pos spatialDim⟩
    simp [h_u2_zero]
    exact zero_contains_zero

/-- Helper lemma: A single convolution fold term (imaginary part) is witnessed. -/
private lemma witness_fold_term_im (M : ℕ) (p : ℕ)
    (u1_impl u2_impl : StateArray) (u1_math u2_math : SeqD_Rat spatialDim)
    (h1 : IsWitness M u1_impl u1_math) (h2 : IsWitness M u2_impl u2_math)
    (k_i k1 : Lattice spatialDim) (hk1 : k1 ∈ SemilinearHeat.cubeListLattice M) :
    let k2 := fun j => k_i j - k1 j
    let f_iv_im := if -(M : ℤ) ≤ k2 ⟨0, NeZero.pos spatialDim⟩ ∧ k2 ⟨0, NeZero.pos spatialDim⟩ ≤ M then
                     let i1 := SemilinearHeat.latticeToIdx k1 M
                     let i2 := SemilinearHeat.latticeToIdx k2 M
                     if h1_idx : i1 < u1_impl.size then
                       if h2_idx : i2 < u2_impl.size then
                         let (u1_re, u1_im) := u1_impl[i1]
                         let (v2_re, v2_im) := u2_impl[i2]
                         IntervalDyadic.add (IntervalDyadic.mul u1_re v2_im p) (IntervalDyadic.mul u1_im v2_re p) p
                       else IntervalDyadic.zero
                     else IntervalDyadic.zero
                   else IntervalDyadic.zero
    let f_rat_im := let (u1_re, u1_im) := u1_math.a k1
                    let (u2_re, u2_im) := u2_math.a k2
                    u1_re * u2_im + u1_im * u2_re
    intervalContains f_iv_im f_rat_im := by
  intro k2 f_iv_im f_rat_im
  -- Get witness sizes
  have h1_size : u1_impl.size = 2 * M + 1 := witness_size h1
  have h2_size : u2_impl.size = 2 * M + 1 := witness_size h2

  -- NEW: Case split on geometric bounds FIRST
  by_cases hk2_bounds : -(M : ℤ) ≤ k2 ⟨0, NeZero.pos spatialDim⟩ ∧ k2 ⟨0, NeZero.pos spatialDim⟩ ≤ M
  · -- k2 is in bounds geometrically
    let i1 := SemilinearHeat.latticeToIdx k1 M
    let i2 := SemilinearHeat.latticeToIdx k2 M
    by_cases h1_idx : i1 < u1_impl.size
    · by_cases h2_idx : i2 < u2_impl.size
      · -- Both in bounds: use witnesses
        have h_u1 := witness_contains h1 i1 h1_idx
        have h_u2 := witness_contains h2 i2 h2_idx
        obtain ⟨h_u1_re, h_u1_im⟩ := h_u1
        obtain ⟨h_u2_re, h_u2_im⟩ := h_u2

        -- Convert witness facts to use k1, k2 instead of fromIdx
        have h_k1_eq : GridMapping.fromIdx i1 M = k1 := fromIdx_latticeToIdx_cube M k1 hk1
        have h_k2_eq : GridMapping.fromIdx i2 M = k2 := by
          -- NOW PROVABLE! We have hk2_bounds : k2 is in [-M, M]
          unfold i2
          apply fromIdx_latticeToIdx_inbounds M k2
          · exact hk2_bounds.1  -- Lower bound from geometric bounds check
          · rw [← h2_size]      -- latticeToIdx k2 M < 2*M+1
            exact h2_idx

        -- Rewrite witness facts to use k1, k2
        have h_u1_re' : intervalContains (u1_impl[i1]'h1_idx).1 (u1_math.a k1).1 := by
          rw [←h_k1_eq]; exact h_u1_re
        have h_u1_im' : intervalContains (u1_impl[i1]'h1_idx).2 (u1_math.a k1).2 := by
          rw [←h_k1_eq]; exact h_u1_im
        have h_u2_re' : intervalContains (u2_impl[i2]'h2_idx).1 (u2_math.a k2).1 := by
          rw [←h_k2_eq]; exact h_u2_re
        have h_u2_im' : intervalContains (u2_impl[i2]'h2_idx).2 (u2_math.a k2).2 := by
          rw [←h_k2_eq]; exact h_u2_im

        -- Imaginary part: u1_re * u2_im + u1_im * u2_re
        unfold f_iv_im f_rat_im
        rw [if_pos hk2_bounds, dif_pos h1_idx, dif_pos h2_idx]
        exact add_preserves_containment _ _ _ _ p
          (mul_preserves_containment _ _ _ _ p h_u1_re' h_u2_im')
          (mul_preserves_containment _ _ _ _ p h_u1_im' h_u2_re')
      · -- i2 out of bounds: returns zero, witnesses 0
        unfold f_iv_im f_rat_im
        rw [if_pos hk2_bounds, dif_pos h1_idx, dif_neg h2_idx]
        have h_u2_zero : u2_math.a k2 = (0, 0) := by
          apply out_of_cube_implies_zero M u2_impl u2_math h2
          -- Need to show k2 ∉ cube
          have : ¬(latticeToIdx k2 M < u2_impl.size) := h2_idx
          rw [h2_size] at this
          unfold latticeToIdx at this
          -- this : ¬((k2 0 + ↑M).toNat < 2 * M + 1)
          -- If toNat ≥ 2M+1, then k2 is outside the cube
          have h_tonat_bound : (k2 ⟨0, NeZero.pos spatialDim⟩ + ↑M).toNat ≥ 2 * M + 1 := by
            exact Nat.le_of_not_lt this
          exact toNat_ge_implies_out_of_cube M k2 h_tonat_bound
        simp [h_u2_zero]
        exact zero_contains_zero
    · -- i1 out of bounds: impossible, since k1 ∈ cubeListLattice implies i1 in bounds
      exfalso
      -- k1 ∈ cubeListLattice M means k1 = (fun _ => (n:ℤ) - M) where n < 2*M+1
      simp only [SemilinearHeat.cubeListLattice, List.mem_map, List.mem_range] at hk1
      obtain ⟨n, hn_range, hk1_eq⟩ := hk1
      -- i1 = latticeToIdx k1 M = (k1 0 + M).toNat = n
      have h_i1_eq : i1 = n := by
        show SemilinearHeat.latticeToIdx k1 M = n
        unfold SemilinearHeat.latticeToIdx
        rw [← hk1_eq]
        simp only []
        omega
      rw [h_i1_eq, h1_size] at h1_idx
      omega
  · -- k2 out of geometric bounds
    unfold f_iv_im f_rat_im
    rw [if_neg hk2_bounds]
    have h_u2_zero : u2_math.a k2 = (0, 0) := by
      apply out_of_cube_implies_zero M u2_impl u2_math h2
      -- k2 ∉ cube because ¬(-(M : ℤ) ≤ k2 0 ∧ k2 0 ≤ M)
      unfold ℓ2ZD.cube
      simp only [Fintype.mem_piFinset, Finset.mem_Icc, not_forall]
      use ⟨0, NeZero.pos spatialDim⟩
    simp [h_u2_zero]
    exact zero_contains_zero

/-- Theorem: convolve_Array computes intervals containing the mathematical convolution.

    This theorem states that for any index i and corresponding lattice point k,
    the convolution array at position i contains the mathematical convolution coefficient at k.

    Refactored proof using helper lemmas to eliminate massive duplication and dependent type issues. -/
theorem convolve_Array_contains_math (M : ℕ) (p : ℕ)
    (u1_impl u2_impl : StateArray) (u1_math u2_math : SeqD_Rat spatialDim)
    (h1 : IsWitness M u1_impl u1_math) (h2 : IsWitness M u2_impl u2_math)
    (i : ℕ) (hi : i < (SemilinearHeat.convolve_Array u1_impl u2_impl M p).size) :
    let k := idxToLattice i M
    let sum_re := Finset.sum (cube spatialDim M) fun k1 =>
      let k2 : Lattice spatialDim := fun j => k j - k1 j
      let (u1_re, u1_im) := u1_math.a k1
      let (u2_re, u2_im) := u2_math.a k2
      u1_re * u2_re - u1_im * u2_im
    let sum_im := Finset.sum (cube spatialDim M) fun k1 =>
      let k2 : Lattice spatialDim := fun j => k j - k1 j
      let (u1_re, u1_im) := u1_math.a k1
      let (u2_re, u2_im) := u2_math.a k2
      u1_re * u2_im + u1_im * u2_re
    intervalContains ((SemilinearHeat.convolve_Array u1_impl u2_impl M p)[i]'hi).1 sum_re ∧
    intervalContains ((SemilinearHeat.convolve_Array u1_impl u2_impl M p)[i]'hi).2 sum_im := by
  intro k sum_re sum_im

  let k_i := idxToLattice i M
  have h_k_eq : k = k_i := rfl

  -- Define interval and rational functions matching the convolution fold structure
  -- CRITICAL: Now includes geometric bounds check to prevent toNat aliasing
  let f_iv_re : (Lattice spatialDim) → IntervalD := fun k1 =>
    let k2 : Lattice spatialDim := fun j => k_i j - k1 j
    if -(M : ℤ) ≤ k2 ⟨0, NeZero.pos spatialDim⟩ ∧ k2 ⟨0, NeZero.pos spatialDim⟩ ≤ M then
      let i1 := latticeToIdx k1 M
      let i2 := latticeToIdx k2 M
      if h1_idx : i1 < u1_impl.size then
        if h2_idx : i2 < u2_impl.size then
          let (u1_re, u1_im) := u1_impl[i1]
          let (v2_re, v2_im) := u2_impl[i2]
          IntervalDyadic.sub (IntervalDyadic.mul u1_re v2_re p) (IntervalDyadic.mul u1_im v2_im p) p
        else IntervalDyadic.zero
      else IntervalDyadic.zero
    else IntervalDyadic.zero

  let f_rat_re : (Lattice spatialDim) → ℚ := fun k1 =>
    let k2 : Lattice spatialDim := fun j => k_i j - k1 j
    let (u1_re, u1_im) := u1_math.a k1
    let (u2_re, u2_im) := u2_math.a k2
    u1_re * u2_re - u1_im * u2_im

  let f_iv_im : (Lattice spatialDim) → IntervalD := fun k1 =>
    let k2 : Lattice spatialDim := fun j => k_i j - k1 j
    if -(M : ℤ) ≤ k2 ⟨0, NeZero.pos spatialDim⟩ ∧ k2 ⟨0, NeZero.pos spatialDim⟩ ≤ M then
      let i1 := latticeToIdx k1 M
      let i2 := latticeToIdx k2 M
      if h1_idx : i1 < u1_impl.size then
        if h2_idx : i2 < u2_impl.size then
          let (u1_re, u1_im) := u1_impl[i1]
          let (v2_re, v2_im) := u2_impl[i2]
          IntervalDyadic.add (IntervalDyadic.mul u1_re v2_im p) (IntervalDyadic.mul u1_im v2_re p) p
        else IntervalDyadic.zero
      else IntervalDyadic.zero
    else IntervalDyadic.zero

  let f_rat_im : (Lattice spatialDim) → ℚ := fun k1 =>
    let k2 : Lattice spatialDim := fun j => k_i j - k1 j
    let (u1_re, u1_im) := u1_math.a k1
    let (u2_re, u2_im) := u2_math.a k2
    u1_re * u2_im + u1_im * u2_re

  -- Use helper lemmas to show each fold term is witnessed (eliminates 212 lines of duplication!)
  have h_witness_re : ∀ k1 ∈ cubeListLattice M, intervalContains (f_iv_re k1) (f_rat_re k1) := fun k1 hk1 =>
    witness_fold_term_re M p u1_impl u2_impl u1_math u2_math h1 h2 k_i k1 hk1

  have h_witness_im : ∀ k1 ∈ cubeListLattice M, intervalContains (f_iv_im k1) (f_rat_im k1) := fun k1 hk1 =>
    witness_fold_term_im M p u1_impl u2_impl u1_math u2_math h1 h2 k_i k1 hk1

  -- Apply the generic paired fold lemma
  have h_fold := foldl_add_pair_contains_sum (cubeListLattice M) f_iv_re f_iv_im f_rat_re f_rat_im p
    h_witness_re h_witness_im

  -- Show the rational fold equals the Finset sum
  have h_paired_eq : (cubeListLattice M).foldl (fun (acc1, acc2) x =>
      (acc1 + f_rat_re x, acc2 + f_rat_im x)) (0, 0) = (sum_re, sum_im) := by
    unfold sum_re sum_im
    apply Prod.ext
    · -- First component (real part)
      have h_fst : ∀ (xs : List (Lattice spatialDim)) (acc1 acc2 : ℚ),
          (xs.foldl (fun (a1, a2) x => (a1 + f_rat_re x, a2 + f_rat_im x)) (acc1, acc2)).1 =
          xs.foldl (fun a x => a + f_rat_re x) acc1 := by
        intro xs; induction xs with
        | nil => intro acc1 acc2; rfl
        | cons x xs ih => intro acc1 acc2; rw [List.foldl, List.foldl]; exact ih _ _
      rw [h_fst (cubeListLattice M) 0 0]
      exact foldl_eq_sum_cube M f_rat_re
    · -- Second component (imaginary part)
      have h_snd : ∀ (xs : List (Lattice spatialDim)) (acc1 acc2 : ℚ),
          (xs.foldl (fun (a1, a2) x => (a1 + f_rat_re x, a2 + f_rat_im x)) (acc1, acc2)).2 =
          xs.foldl (fun a x => a + f_rat_im x) acc2 := by
        intro xs; induction xs with
        | nil => intro acc1 acc2; rfl
        | cons x xs ih => intro acc1 acc2; rw [List.foldl, List.foldl]; exact ih _ _
      rw [h_snd (cubeListLattice M) 0 0]
      exact foldl_eq_sum_cube M f_rat_im

  -- Complete the proof by connecting everything
  have h_spec := convolve_Array_spec u1_impl u2_impl M p i hi

  -- Use congrArg to extract component equalities from h_paired_eq
  have h_eq_re : ((cubeListLattice M).foldl (fun (acc1, acc2) x =>
      (acc1 + f_rat_re x, acc2 + f_rat_im x)) (0, 0)).1 = sum_re :=
    congrArg Prod.fst h_paired_eq
  have h_eq_im : ((cubeListLattice M).foldl (fun (acc1, acc2) x =>
      (acc1 + f_rat_re x, acc2 + f_rat_im x)) (0, 0)).2 = sum_im :=
    congrArg Prod.snd h_paired_eq

  -- NUCLEAR STRATEGY: Instead of proving fold equality, prove containment DIRECTLY
  -- using a specialized lemma that matches the convolve_Array_spec structure.
  --
  -- The issue: foldl_add_pair_contains_sum expects:
  --   foldl (fun acc x => (add acc.1 (f x) p, add acc.2 (g x) p))
  -- But convolve_Array_spec gives:
  --   foldl (fun acc x => if cond then (add acc.1 val1 p, add acc.2 val2 p) else acc)
  --
  -- These are NOT definitionally equal because "add acc zero" ≠ "acc" definitionally.
  --
  -- Solution: Prove a specialized fold_contains lemma that works with conditional updates.

  have h_fold_contains_spec :
    ∀ (xs : List (Lattice spatialDim)) acc_re_iv acc_im_iv acc_re_rat acc_im_rat,
      (∀ x ∈ xs, x ∈ SemilinearHeat.cubeListLattice M) →
      intervalContains acc_re_iv acc_re_rat →
      intervalContains acc_im_iv acc_im_rat →
      (∀ x ∈ xs, intervalContains (f_iv_re x) (f_rat_re x)) →
      (∀ x ∈ xs, intervalContains (f_iv_im x) (f_rat_im x)) →
      let result_iv := xs.foldl (fun (a_re, a_im) k1 =>
        let k2 : Lattice spatialDim := fun j => k_i j - k1 j
        if -(M : ℤ) ≤ k2 ⟨0, NeZero.pos spatialDim⟩ ∧ k2 ⟨0, NeZero.pos spatialDim⟩ ≤ M then
          let i1 := latticeToIdx k1 M
          let i2 := latticeToIdx k2 M
          if h1 : i1 < u1_impl.size then
            if h2 : i2 < u2_impl.size then
              let (u1_re, u1_im) := u1_impl[i1]
              let (u2_re, u2_im) := u2_impl[i2]
              (IntervalDyadic.add a_re (IntervalDyadic.sub (IntervalDyadic.mul u1_re u2_re p) (IntervalDyadic.mul u1_im u2_im p) p) p,
               IntervalDyadic.add a_im (IntervalDyadic.add (IntervalDyadic.mul u1_re u2_im p) (IntervalDyadic.mul u1_im u2_re p) p) p)
            else (a_re, a_im)
          else (a_re, a_im)
        else (a_re, a_im)
      ) (acc_re_iv, acc_im_iv)
      let result_rat := xs.foldl (fun (a_re, a_im) k1 =>
        (a_re + f_rat_re k1, a_im + f_rat_im k1)
      ) (acc_re_rat, acc_im_rat)
      intervalContains result_iv.1 result_rat.1 ∧ intervalContains result_iv.2 result_rat.2 := by
    intro xs
    induction xs with
    | nil =>
      intro acc_re_iv acc_im_iv acc_re_rat acc_im_rat _ h_acc_re h_acc_im _ _
      simp [List.foldl]
      exact ⟨h_acc_re, h_acc_im⟩
    | cons x xs ih =>
      intro acc_re_iv acc_im_iv acc_re_rat acc_im_rat h_xs_in_cube h_acc_re h_acc_im h_wit_re h_wit_im
      simp only [List.foldl]
      -- Split on whether the conditions hold
      by_cases hcond : -(M : ℤ) ≤ (fun j => k_i j - x j) ⟨0, NeZero.pos spatialDim⟩ ∧
                               (fun j => k_i j - x j) ⟨0, NeZero.pos spatialDim⟩ ≤ M
      · simp only [hcond]
        by_cases h1_case : latticeToIdx x M < u1_impl.size
        · by_cases h2_case : latticeToIdx (fun j => k_i j - x j) M < u2_impl.size
          · -- All conditions true: add the values
            simp only [h1_case, h2_case, ↓reduceDIte]
            apply ih
            · intro y hy; exact h_xs_in_cube y (List.mem_cons_of_mem x hy)
            · -- Show intervalContains for updated real part
              have h_re := h_wit_re x List.mem_cons_self
              unfold f_iv_re f_rat_re at h_re
              simp only [hcond, h1_case, h2_case, ↓reduceDIte] at h_re
              exact add_preserves_containment _ _ _ _ p h_acc_re h_re
            · -- Show intervalContains for updated imaginary part
              have h_im := h_wit_im x List.mem_cons_self
              unfold f_iv_im f_rat_im at h_im
              simp only [hcond, h1_case, h2_case, ↓reduceDIte] at h_im
              exact add_preserves_containment _ _ _ _ p h_acc_im h_im
            · intro y hy; exact h_wit_re y (List.mem_cons_of_mem x hy)
            · intro y hy; exact h_wit_im y (List.mem_cons_of_mem x hy)
          · -- h2 false: no update on interval side, but rational side adds (which should be zero)
            simp only [h1_case, h2_case, ↓reduceDIte]
            -- When h2 is false, k2 is out of bounds, so u2_math.a k2 = (0,0)
            -- Thus f_rat_re x = 0 and f_rat_im x = 0
            -- So acc_re_rat + f_rat_re x = acc_re_rat + 0 = acc_re_rat
            have h_k2_out : latticeToIdx (fun j => k_i j - x j) M ≥ u2_impl.size := Nat.le_of_not_lt h2_case
            have h_u2_zero : u2_math.a (fun j => k_i j - x j) = (0, 0) := by
              apply out_of_cube_implies_zero M u2_impl u2_math h2
              rw [h2.1] at h_k2_out
              exact toNat_ge_implies_out_of_cube M (fun j => k_i j - x j) h_k2_out
            have h_f_rat_re_zero : f_rat_re x = 0 := by
              unfold f_rat_re
              simp only [h_u2_zero]
              ring
            have h_f_rat_im_zero : f_rat_im x = 0 := by
              unfold f_rat_im
              simp only [h_u2_zero]
              ring
            rw [h_f_rat_re_zero, h_f_rat_im_zero]
            simp only [add_zero]
            apply ih
            · intro y hy; exact h_xs_in_cube y (List.mem_cons_of_mem x hy)
            · exact h_acc_re
            · exact h_acc_im
            · intro y hy; exact h_wit_re y (List.mem_cons_of_mem x hy)
            · intro y hy; exact h_wit_im y (List.mem_cons_of_mem x hy)
        · -- h1 false: x (i.e., k1) out of bounds
          simp only [h1_case, ↓reduceDIte]
          -- x ∈ cubeListLattice M implies latticeToIdx x M < size
          -- So h1_case (¬latticeToIdx x M < u1_impl.size) contradicts this
          exfalso
          have hx_in_cube : x ∈ SemilinearHeat.cubeListLattice M := h_xs_in_cube x List.mem_cons_self
          have : SemilinearHeat.latticeToIdx x M < 2 * M + 1 :=
            cubeListLattice_idx_bound M x hx_in_cube
          rw [h1.1] at h1_case
          omega
      · -- Condition false: geometric bounds fail
        simp only [hcond, ↓reduceIte]
        -- When geometric bounds fail, k2 is out of cube, so u2_math.a k2 = (0,0)
        have h_u2_zero : u2_math.a (fun j => k_i j - x j) = (0, 0) := by
          apply h2.2.2
          unfold ℓ2ZD.cube
          simp only [Fintype.mem_piFinset, Finset.mem_Icc, not_forall]
          use ⟨0, NeZero.pos spatialDim⟩
        have h_f_rat_re_zero : f_rat_re x = 0 := by
          unfold f_rat_re
          simp only [h_u2_zero]
          ring
        have h_f_rat_im_zero : f_rat_im x = 0 := by
          unfold f_rat_im
          simp only [h_u2_zero]
          ring
        rw [h_f_rat_re_zero, h_f_rat_im_zero]
        simp only [add_zero]
        apply ih
        · intro y hy; exact h_xs_in_cube y (List.mem_cons_of_mem x hy)
        · exact h_acc_re
        · exact h_acc_im
        · intro y hy; exact h_wit_re y (List.mem_cons_of_mem x hy)
        · intro y hy; exact h_wit_im y (List.mem_cons_of_mem x hy)

  -- Apply the specialized lemma
  have h_contains := h_fold_contains_spec (cubeListLattice M)
    IntervalDyadic.zero IntervalDyadic.zero 0 0
    (fun x hx => hx)
    zero_contains_zero zero_contains_zero h_witness_re h_witness_im

  constructor
  · -- Real part
    rw [h_spec]
    rw [← h_eq_re]
    exact h_contains.1

  · -- Imaginary part
    rw [h_spec]
    rw [← h_eq_im]
    exact h_contains.2

/-- Helper: Full convolution coefficient (before projection).
    This has support in cube 2M due to aliasing. -/
private def convolve_math_coeff_full (u1 u2 : SeqD_Rat spatialDim) (M : ℕ) (k : Lattice spatialDim) : ℚ × ℚ :=
  let cubeM := cube spatialDim M
  let sum_re := Finset.sum cubeM fun k1 =>
    let k2 : Lattice spatialDim := fun i => k i - k1 i
    let (u1_re, u1_im) := u1.a k1
    let (u2_re, u2_im) := u2.a k2
    u1_re * u2_re - u1_im * u2_im
  let sum_im := Finset.sum cubeM fun k1 =>
    let k2 : Lattice spatialDim := fun i => k i - k1 i
    let (u1_re, u1_im) := u1.a k1
    let (u2_re, u2_im) := u2.a k2
    u1_re * u2_im + u1_im * u2_re
  (sum_re, sum_im)

/-- Mathematical model of convolution with Galerkin projection.

The implementation naturally truncates to M modes (finite memory).
The math side must match this by explicitly projecting. -/
def convolve_math (u1 u2 : SeqD_Rat spatialDim) (M : ℕ) : SeqD_Rat spatialDim :=
  truncate_math M {
    a := convolve_math_coeff_full u1 u2 M
    finite_support := by
      -- The convolution coefficient is: Σ_{k1 ∈ cube M} u1(k1) * u2(k - k1)
      -- Support ⊆ Minkowski sum: {k | ∃ k1 ∈ supp(u1), k2 ∈ supp(u2), k = k1 + k2}
      -- Since supp(u1) and supp(u2) are finite, their Minkowski sum is finite.

      -- Strategy: Use classical reasoning to extract finite sets from u1, u2 supports
      classical
      -- Get finsets representing the supports of u1 and u2
      obtain ⟨S1, hS1⟩ := u1.finite_support.exists_finset_coe
      obtain ⟨S2, hS2⟩ := u2.finite_support.exists_finset_coe

      -- The support is bounded by the Minkowski sum S1 + S2
      -- For each k1 ∈ S1, k2 ∈ S2, we get k = k1 + k2 in the sum
      let minkowski_sum := (S1.product S2).image (fun (k1, k2) => fun i => k1 i + k2 i)

      apply Set.Finite.subset (Finset.finite_toSet minkowski_sum)
      intro k hk
      simp only [Set.mem_setOf_eq] at hk
      unfold convolve_math_coeff_full at hk

      -- hk says (sum_re, sum_im) ≠ (0, 0), so at least one component is nonzero
      -- This means there exists k1 ∈ cube M such that the summand is nonzero

      -- For the summand to be nonzero, we need:
      -- u1.a k1 ≠ (0,0) AND u2.a (k - k1) ≠ (0,0)

      -- We show k is in the Minkowski sum by exhibiting k1 ∈ S1, k2 ∈ S2 with k = k1 + k2
      -- If the sum is nonzero, such k1 must exist in the finite sum
      by_contra h_not_in_sum

      -- If k is not in the Minkowski sum, then for all k1 with nonzero u1.a k1,
      -- we have k2 = k - k1 not in support of u2
      have h_all_zero : ∀ k1 ∈ (ℓ2ZD.cube spatialDim M),
          let k2 := fun i => k i - k1 i
          u1.a k1 = (0, 0) ∨ u2.a k2 = (0, 0) := by
        intro k1 _
        by_cases h_u1 : u1.a k1 = (0, 0)
        · left; exact h_u1
        · right
          -- k1 ∈ S1 since u1.a k1 ≠ 0
          have hk1_in_S1 : k1 ∈ S1 := by
            have : k1 ∈ (S1 : Set (ℓ2ZD.Lattice spatialDim)) := by
              rw [hS1]
              simp only [Set.mem_setOf_eq]
              exact h_u1
            exact this
          -- If u2.a k2 ≠ 0, then k2 ∈ S2
          by_contra h_u2_ne
          push_neg at h_u2_ne
          have hk2_in_S2 : (fun i => k i - k1 i) ∈ S2 := by
            have : (fun i => k i - k1 i) ∈ (S2 : Set (ℓ2ZD.Lattice spatialDim)) := by
              rw [hS2]
              simp only [Set.mem_setOf_eq]
              exact h_u2_ne
            exact this
          -- Then k = k1 + k2 should be in Minkowski sum
          apply h_not_in_sum
          show k ∈ minkowski_sum
          simp only [minkowski_sum, Finset.mem_image]
          use (k1, fun i => k i - k1 i)
          constructor
          · show (k1, fun i => k i - k1 i) ∈ S1.product S2
            exact Finset.mem_product.mpr ⟨hk1_in_S1, hk2_in_S2⟩
          · funext i
            ring

      -- But this means every summand is zero, contradicting hk
      -- Note: hk already has convolve_math_coeff_full unfolded from earlier
      simp only [] at hk
      -- hk states the pair is nonzero, so at least one component is nonzero
      by_cases h_re : (Finset.sum (ℓ2ZD.cube spatialDim M) fun k1 =>
          let k2 := fun i => k i - k1 i
          let (u1_re, u1_im) := u1.a k1
          let (u2_re, u2_im) := u2.a k2
          u1_re * u2_re - u1_im * u2_im) ≠ 0
      · -- sum_re ≠ 0 case
        have : (Finset.sum (ℓ2ZD.cube spatialDim M) fun k1 =>
            let k2 := fun i => k i - k1 i
            let (u1_re, u1_im) := u1.a k1
            let (u2_re, u2_im) := u2.a k2
            u1_re * u2_re - u1_im * u2_im) = 0 := by
          apply Finset.sum_eq_zero
          intro k1 hk1_cube
          obtain h_u1_zero | h_u2_zero := h_all_zero k1 hk1_cube
          · simp [h_u1_zero]
          · simp [h_u2_zero]
        exact h_re this
      · -- sum_im ≠ 0 case
        push_neg at h_re
        have h_im : (Finset.sum (ℓ2ZD.cube spatialDim M) fun k1 =>
            let k2 := fun i => k i - k1 i
            let (u1_re, u1_im) := u1.a k1
            let (u2_re, u2_im) := u2.a k2
            u1_re * u2_im + u1_im * u2_re) ≠ 0 := by
          intro h_zero
          apply hk
          rw [h_re, h_zero]
        have : (Finset.sum (ℓ2ZD.cube spatialDim M) fun k1 =>
            let k2 := fun i => k i - k1 i
            let (u1_re, u1_im) := u1.a k1
            let (u2_re, u2_im) := u2.a k2
            u1_re * u2_im + u1_im * u2_re) = 0 := by
          apply Finset.sum_eq_zero
          intro k1 hk1_cube
          obtain h_u1_zero | h_u2_zero := h_all_zero k1 hk1_cube
          · simp [h_u1_zero]
          · simp [h_u2_zero]
        exact h_im this
  }

/-- Convolution preserves IsWitness.
    Given two arrays witnessing mathematical sequences, their convolution
    witnesses the mathematical convolution. -/
theorem convolve_preserves_witness (M : ℕ) (p : ℕ)
    (u1_impl u2_impl : StateArray)
    (u1_math u2_math : SeqD_Rat spatialDim)
    (h1 : IsWitness M u1_impl u1_math)
    (h2 : IsWitness M u2_impl u2_math) :
    IsWitness M
      (SemilinearHeat.convolve_Array u1_impl u2_impl M p)
      (convolve_math u1_math u2_math M) := by
  unfold IsWitness
  constructor
  · -- Size check
    unfold SemilinearHeat.convolve_Array
    simp [Array.ofFn]
  · constructor
    · -- Containment check
      intro i hi
      -- Get the lattice point k for this index
      let k := GridMapping.fromIdx (d := spatialDim) i M

      -- Extract the computational result
      have hsize : (SemilinearHeat.convolve_Array u1_impl u2_impl M p).size = 2 * M + 1 := by
        unfold SemilinearHeat.convolve_Array; simp [Array.ofFn]

      -- Apply the axiom to get containment
      have h_contains := convolve_Array_contains_math M p u1_impl u2_impl u1_math u2_math h1 h2 i hi

      -- The axiom gives us containment in terms of Finset.sum
      -- The goal expects containment for (convolve_math u1_math u2_math M).a k
      -- With Galerkin projection: (convolve_math u1 u2 M).a k = if k ∈ cube M then (full_conv).a k else (0,0)
      show (let k := GridMapping.fromIdx (d := spatialDim) i M
            let (iv_re, iv_im) := (SemilinearHeat.convolve_Array u1_impl u2_impl M p)[i]'hi
            let (q_re, q_im) := (convolve_math u1_math u2_math M).a k
            intervalContains iv_re q_re ∧ intervalContains iv_im q_im)

      -- Need to show idxToLattice = GridMapping.fromIdx for spatialDim = 1
      have hk_eq : idxToLattice i M = GridMapping.fromIdx (d := spatialDim) i M := by
        funext j
        unfold SemilinearHeat.idxToLattice GridMapping.fromIdx
        have hj : j = ⟨0, NeZero.pos spatialDim⟩ := by
          have h_dim : spatialDim = 1 := rfl
          have : j.val < 1 := by rw [← h_dim]; exact j.isLt
          omega
        simp [hj]

      -- k is in the cube because it comes from a valid index i < 2M+1
      have hk_in_cube : GridMapping.fromIdx (d := spatialDim) i M ∈ ℓ2ZD.cube spatialDim M := by
        unfold GridMapping.fromIdx ℓ2ZD.cube
        simp only [Fintype.mem_piFinset, Finset.mem_Icc]
        intro j
        -- For spatialDim = 1, j = 0
        have hj : j = ⟨0, NeZero.pos spatialDim⟩ := by
          have : Subsingleton (Fin spatialDim) := by rw [show spatialDim = 1 from rfl]; infer_instance
          exact Subsingleton.elim j ⟨0, NeZero.pos spatialDim⟩
        rw [hj]
        simp only
        -- i < 2M+1, so (i - M : ℤ) ∈ [-M, M]
        have h_size : (SemilinearHeat.convolve_Array u1_impl u2_impl M p).size = 2 * M + 1 := by
          unfold SemilinearHeat.convolve_Array; simp [Array.ofFn]
        rw [h_size] at hi
        omega

      -- Unfold convolve_math and use that k is in cube
      unfold convolve_math truncate_math
      simp only [hk_in_cube]
      rw [← hk_eq]
      exact h_contains
    · -- Bounded support: modes outside cube are zero
      intro k hk
      -- hk : k ∉ cube spatialDim M
      -- The truncate_math operator makes this trivial
      unfold convolve_math truncate_math
      simp only [if_neg hk]

/-! ## Cubic Operator Preservation -/

/-- Helper: Real part of complex product (a + bi) * (c + di) = ac - bd -/
private lemma complex_mul_re (a b c d : ℚ) :
    (a * c - b * d) = (a * c - b * d) := rfl

/-- Helper: Imaginary part of complex product (a + bi) * (c + di) = ad + bc -/
private lemma complex_mul_im (a b c d : ℚ) :
    (a * d + b * c) = (a * d + b * c) := rfl

/-- Helper: Real part of triple complex product
    ((a₁ + b₁i) * (a₂ + b₂i)) * (a₃ + b₃i) -/
private lemma complex_triple_mul_re (a₁ b₁ a₂ b₂ a₃ b₃ : ℚ) :
    let prod12_re := a₁ * a₂ - b₁ * b₂
    let prod12_im := a₁ * b₂ + b₁ * a₂
    prod12_re * a₃ - prod12_im * b₃ =
    a₁ * a₂ * a₃ - a₁ * b₂ * b₃ - b₁ * a₂ * b₃ - b₁ * b₂ * a₃ := by ring

/-- Helper: Imaginary part of triple complex product
    ((a₁ + b₁i) * (a₂ + b₂i)) * (a₃ + b₃i) -/
private lemma complex_triple_mul_im (a₁ b₁ a₂ b₂ a₃ b₃ : ℚ) :
    let prod12_re := a₁ * a₂ - b₁ * b₂
    let prod12_im := a₁ * b₂ + b₁ * a₂
    prod12_re * b₃ + prod12_im * a₃ =
    a₁ * a₂ * b₃ + a₁ * b₂ * a₃ + b₁ * a₂ * a₃ - b₁ * b₂ * b₃ := by ring

/-! ## Cubic Operator -/

/-- Mathematical model of cubic nonlinearity with Galerkin projection.

    We define this as the iterated convolution (u*u)*u, which is what
    the implementation actually computes (via two convolution calls).

    Note: This is NOT the same as the full triple convolution P(u·u·u),
    because the intermediate projection P(u·u) discards high frequencies
    that could alias back. This is the correct model for the code. -/
def applyCubic_math (u : SeqD_Rat spatialDim) (M : ℕ) : SeqD_Rat spatialDim :=
  convolve_math (convolve_math u u M) u M

/-- Mathematical model of Euler step with projection.
    Redefined to explicitly use the iterated cubic model (applyCubic_math)
    to match the verified computational path. -/
def eulerStep_math (dt : ℚ) (M : ℕ) (u : SeqD_Rat spatialDim) : SeqD_Rat spatialDim :=
  truncate_math M {
    a := fun k =>
      let (u_re, u_im) := u.a k
      let (c_re, c_im) := (applyCubic_math u M).a k
      let lambda := SemilinearHeat.laplacianWeight_rat k
      (u_re + dt * (-lambda * u_re + c_re),
        u_im + dt * (-lambda * u_im + c_im))
    finite_support := by
      -- Support is subset of union of u and cubic supports
      have hu := u.finite_support
      have hc := (applyCubic_math u M).finite_support
      apply Set.Finite.subset (Set.Finite.union hu hc)
      intro k hk
      simp only [Set.mem_union, Set.mem_setOf_eq] at hk ⊢
      contrapose! hk
      let ⟨hku, hkc⟩ := hk
      simp [hku, hkc]
  }

theorem applyCubic_rat_eq_iterated_convolve (u : SeqD_Rat spatialDim) (M : ℕ) :
    applyCubic_math u M = convolve_math (convolve_math u u M) u M := by
  rfl  -- Definitional equality by definition of applyCubic_math

/-- The cubic operator preserves witnesses.
    This uses the O(N²) optimization: u³ = (u*u)*u via two convolutions. -/
theorem applyCubic_Array_preserves_witness (M : ℕ) (p : ℕ)
    (u_impl : StateArray) (u_math : SeqD_Rat spatialDim)
    (h : IsWitness M u_impl u_math) :
    IsWitness M
      (SemilinearHeat.applyCubic_Array u_impl M p)
      (applyCubic_math u_math M) := by
  -- u³ = (u*u)*u via two convolutions
  -- First convolution: u_squared = u*u
  have h_squared : IsWitness M
      (SemilinearHeat.convolve_Array u_impl u_impl M p)
      (convolve_math u_math u_math M) := by
    exact convolve_preserves_witness M p u_impl u_impl u_math u_math h h
  -- Second convolution: (u*u)*u
  have h_cubed : IsWitness M
      (SemilinearHeat.convolve_Array (SemilinearHeat.convolve_Array u_impl u_impl M p) u_impl M p)
      (convolve_math (convolve_math u_math u_math M) u_math M) := by
    exact convolve_preserves_witness M p
      (SemilinearHeat.convolve_Array u_impl u_impl M p) u_impl
      (convolve_math u_math u_math M) u_math
      h_squared h
  -- applyCubic_Array is definitionally equal to the double convolution
  show IsWitness M (SemilinearHeat.applyCubic_Array u_impl M p) (applyCubic_math u_math M)
  -- Unfold the definition to match h_cubed
  have heq_impl : SemilinearHeat.applyCubic_Array u_impl M p =
         SemilinearHeat.convolve_Array (SemilinearHeat.convolve_Array u_impl u_impl M p) u_impl M p := by
    rfl
  -- The iterated convolution equals applyCubic_rat
  have heq_math : applyCubic_math u_math M = convolve_math (convolve_math u_math u_math M) u_math M :=
    applyCubic_rat_eq_iterated_convolve u_math M
  rw [heq_impl, heq_math]
  exact h_cubed

/-! ## Euler Step Preservation -/

/-- The eulerStep_Array produces an array of the correct size. -/
private lemma eulerStep_Array_size (dt : IntervalD) (M p : ℕ) (u : StateArray) :
    (SemilinearHeat.eulerStep_Array dt M p u).size = 2 * M + 1 := by
  unfold SemilinearHeat.eulerStep_Array
  simp [Array.ofFn]

/-- Specification lemma: exposes eulerStep_Array structure without dependent types.
    This is analogous to convolve_Array_spec and enables compositional reasoning. -/
private theorem eulerStep_Array_spec (dt : IntervalD) (M p : ℕ) (u : StateArray)
    (i : ℕ) (hi : i < (SemilinearHeat.eulerStep_Array dt M p u).size)
    (h1 : i < u.size) (h2 : i < (SemilinearHeat.applyCubic_Array u M p).size) :
    (SemilinearHeat.eulerStep_Array dt M p u)[i]'hi =
    let k := SemilinearHeat.idxToLattice i M
    let lambda := SemilinearHeat.laplacianWeight_interval k p
    let cubic := (SemilinearHeat.applyCubic_Array u M p)[i]'h2
    let u_elem := u[i]'h1
    (IntervalDyadic.add u_elem.1
      (IntervalDyadic.mul dt
        (IntervalDyadic.add
          (IntervalDyadic.mul (IntervalDyadic.neg lambda p) u_elem.1 p)
          cubic.1 p) p) p,
     IntervalDyadic.add u_elem.2
      (IntervalDyadic.mul dt
        (IntervalDyadic.add
          (IntervalDyadic.mul (IntervalDyadic.neg lambda p) u_elem.2 p)
          cubic.2 p) p) p) := by
  unfold SemilinearHeat.eulerStep_Array
  simp only [Array.getElem_ofFn]
  -- Simplify the if-then-else structure
  simp only [dif_pos h1, dif_pos h2]
  -- Now it's definitional
  rfl

/-- The Euler step preserves witnesses.
    This is the main theorem connecting computational interval evolution
    to mathematical rational evolution. -/
theorem eulerStep_Array_preserves_witness (M : ℕ) (p : ℕ) (dt : IntervalD) (dt_rat : ℚ)
    (u_impl : StateArray) (u_math : SeqD_Rat spatialDim)
    (h_witness : IsWitness M u_impl u_math)
    (h_dt : intervalContains dt dt_rat) :
    IsWitness M
      (SemilinearHeat.eulerStep_Array dt M p u_impl)
      (eulerStep_math dt_rat M u_math) := by
  unfold IsWitness
  constructor
  · -- Size check
    unfold SemilinearHeat.eulerStep_Array
    simp [Array.ofFn]
  · constructor
    · -- Containment check for each coefficient
      intro i hi

      -- Extract the cubic witness
      have h_cubic := applyCubic_Array_preserves_witness M p u_impl u_math h_witness

      -- Establish size constraints
      have h_u_size : u_impl.size = 2*M+1 := witness_size h_witness
      have hi_u : i < u_impl.size := by
        have : (SemilinearHeat.eulerStep_Array dt M p u_impl).size = 2*M+1 := by
          unfold SemilinearHeat.eulerStep_Array; simp [Array.ofFn]
        omega
      have hi_cubic : i < (SemilinearHeat.applyCubic_Array u_impl M p).size := by
        have := witness_size h_cubic
        omega

      -- Use spec lemma to get clean structure BEFORE simplification
      have h_spec := eulerStep_Array_spec dt M p u_impl i hi hi_u hi_cubic

      -- Split into components
      have h_left : (SemilinearHeat.eulerStep_Array dt M p u_impl)[i]'hi =
        let k := SemilinearHeat.idxToLattice i M
        let lambda := SemilinearHeat.laplacianWeight_interval k p
        let cubic := (SemilinearHeat.applyCubic_Array u_impl M p)[i]'hi_cubic
        let u_elem := u_impl[i]'hi_u
        (IntervalDyadic.add u_elem.1
          (IntervalDyadic.mul dt
            (IntervalDyadic.add
              (IntervalDyadic.mul (IntervalDyadic.neg lambda p) u_elem.1 p)
              cubic.1 p) p) p,
         IntervalDyadic.add u_elem.2
          (IntervalDyadic.mul dt
            (IntervalDyadic.add
              (IntervalDyadic.mul (IntervalDyadic.neg lambda p) u_elem.2 p)
              cubic.2 p) p) p) := h_spec

      -- Extract the key values from h_left
      rw [h_left]
      clear h_left

      -- Now work with the clean let-bound structure
      -- Define k to match the spec
      set k := SemilinearHeat.idxToLattice i M with hk_def
      set lambda := SemilinearHeat.laplacianWeight_interval k p
      set cubic := (SemilinearHeat.applyCubic_Array u_impl M p)[i]'hi_cubic
      set u_elem := u_impl[i]'hi_u

      -- Prove k in cube
      have hk_in_cube : k ∈ ℓ2ZD.cube spatialDim M := by
        rw [hk_def]
        unfold SemilinearHeat.idxToLattice ℓ2ZD.cube
        simp only [Fintype.mem_piFinset, Finset.mem_Icc]
        intro j
        have : j = ⟨0, NeZero.pos spatialDim⟩ := by
          have : spatialDim = 1 := rfl
          omega
        simp
        have : (SemilinearHeat.eulerStep_Array dt M p u_impl).size = 2*M+1 := by
          unfold SemilinearHeat.eulerStep_Array; simp [Array.ofFn]
        omega

      -- Match k with fromIdx for witness extraction
      have hk_eq : k = GridMapping.fromIdx (d := spatialDim) i M := by
        rw [hk_def]
        unfold SemilinearHeat.idxToLattice GridMapping.fromIdx
        funext j
        have : j = ⟨0, NeZero.pos spatialDim⟩ := by
          have : spatialDim = 1 := rfl
          omega
        simp [this]

      -- Extract component witnesses from u_impl
      have h_u_wit := witness_contains h_witness i hi_u
      have h_ure : intervalContains u_elem.1 (u_math.a k).1 := by convert h_u_wit.1
      have h_uim : intervalContains u_elem.2 (u_math.a k).2 := by convert h_u_wit.2

      -- Extract cubic witnesses
      have h_cubic_wit := witness_contains h_cubic i hi_cubic
      have h_cre : intervalContains cubic.1 ((applyCubic_math u_math M).a k).1 := by convert h_cubic_wit.1
      have h_cim : intervalContains cubic.2 ((applyCubic_math u_math M).a k).2 := by convert h_cubic_wit.2

      -- Laplacian weight witness
      have h_lambda := laplacian_weight_is_witness k p

      -- Build proof compositionally
      have h_neg_lambda := neg_preserves_containment lambda (SemilinearHeat.laplacianWeight_rat k) p h_lambda
      have h_lap_re := mul_preserves_containment _ _ _ _ p h_neg_lambda h_ure
      have h_lap_im := mul_preserves_containment _ _ _ _ p h_neg_lambda h_uim
      have h_rhs_re := add_preserves_containment _ _ _ _ p h_lap_re h_cre
      have h_rhs_im := add_preserves_containment _ _ _ _ p h_lap_im h_cim
      have h_dt_re := mul_preserves_containment _ _ _ _ p h_dt h_rhs_re
      have h_dt_im := mul_preserves_containment _ _ _ _ p h_dt h_rhs_im
      have h_final_re := add_preserves_containment _ _ _ _ p h_ure h_dt_re
      have h_final_im := add_preserves_containment _ _ _ _ p h_uim h_dt_im

      -- Final assembly
      constructor

      · -- Real Part
        convert h_final_re using 1
        -- Rewrite the index in the goal to match 'k'
        rw [← hk_eq]
        -- Unfold math definitions
        unfold eulerStep_math truncate_math
        -- Now we have `if k ∈ cube ...`
        -- Use the fact that k IS in the cube
        simp only [hk_in_cube, if_true]

      · -- Imaginary Part
        convert h_final_im using 1
        rw [← hk_eq]
        unfold eulerStep_math truncate_math
        simp only [hk_in_cube, if_true]

    · -- Case 2: Out of bounds (The second part of IsWitness)
      intro k hk
      unfold eulerStep_math truncate_math
      simp only [if_neg hk]

end Witness
