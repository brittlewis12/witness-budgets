import Budgets.Witness.Arithmetic

/-!
# Witness Summation Preservation

This module contains generic infrastructure for proving that interval-based
summations correctly witness rational summations.

## Main theorems

- `foldl_add_invariant`: Invariant lemma for folding with addition
- `foldl_add_contains_sum`: Generic summation preservation for single values
- `foldl_add_pair_invariant`: Invariant lemma for folding pairs with addition
- `foldl_add_pair_contains_sum`: Generic summation preservation for pairs

These theorems establish that folding a list with interval addition correctly
witnesses folding with rational addition, avoiding the need to prove this
property separately for each use case.
-/

namespace Witness

open IntervalDyadic

/-! ## Generic Summation Preservation -/

/-- Auxiliary lemma: At each step of the fold, the accumulator is witnessed.

This proves an invariant about folding: if the accumulator interval contains
the accumulator rational, and each new element is witnessed, then the final
folded result is witnessed.

This is the key infrastructure lemma for proving that interval-based summations
correctly witness rational summations. -/
theorem foldl_add_invariant {α : Type} [DecidableEq α]
    (xs : List α)
    (f_interval : α → IntervalD)
    (f_rational : α → ℚ)
    (p : ℕ)
    (acc_iv : IntervalD)
    (acc_rat : ℚ)
    (h_acc : intervalContains acc_iv acc_rat)
    (h_witness : ∀ x ∈ xs, intervalContains (f_interval x) (f_rational x)) :
    intervalContains
      (xs.foldl (fun acc x => IntervalDyadic.add acc (f_interval x) p) acc_iv)
      (xs.foldl (fun acc x => acc + f_rational x) acc_rat) := by
  induction xs generalizing acc_iv acc_rat with
  | nil =>
    -- Empty list: fold returns the accumulator unchanged
    simp [List.foldl]
    exact h_acc
  | cons x xs ih =>
    -- Step: fold on (x :: xs) with init acc
    simp [List.foldl]

    -- After one step, new accumulator is:
    -- acc_iv' = add acc_iv (f_interval x) p
    -- acc_rat' = acc_rat + f_rational x

    -- Need to show these are witnessed
    have h_x : intervalContains (f_interval x) (f_rational x) := by
      apply h_witness
      simp [List.mem_cons]

    have h_new_acc : intervalContains
        (IntervalDyadic.add acc_iv (f_interval x) p)
        (acc_rat + f_rational x) := by
      apply add_preserves_containment
      exact h_acc
      exact h_x

    -- Apply IH with new accumulator
    apply ih
    · exact h_new_acc
    · -- Witness property for tail
      intro y hy
      apply h_witness
      simp [List.mem_cons]
      right
      exact hy

/-- Generic summation preservation: If each term is witnessed, the fold is witnessed.

This is the workhorse lemma for proving that interval-based summation
correctly witnesses rational summation. Instead of proving this property
separately for each sum, we prove it once and for all.

Strategy: Apply the invariant lemma with initial accumulator zero. -/
theorem foldl_add_contains_sum {α : Type} [DecidableEq α]
    (xs : List α)
    (f_interval : α → IntervalD)
    (f_rational : α → ℚ)
    (p : ℕ)
    (h_witness : ∀ x ∈ xs, intervalContains (f_interval x) (f_rational x)) :
    intervalContains
      (xs.foldl (fun acc x => IntervalDyadic.add acc (f_interval x) p) IntervalDyadic.zero)
      (xs.foldl (fun acc x => acc + f_rational x) 0) := by
  apply foldl_add_invariant
  · exact zero_contains_zero
  · exact h_witness

/-! ## Paired Summation Preservation -/

/-- Paired fold invariant: Like foldl_add_invariant but for pairs.
    If the accumulator pair is witnessed and each element is witnessed,
    then the fold result is witnessed. -/
theorem foldl_add_pair_invariant {α : Type} [DecidableEq α]
    (xs : List α)
    (f_interval_1 f_interval_2 : α → IntervalD)
    (f_rational_1 f_rational_2 : α → ℚ)
    (p : ℕ)
    (acc_iv1 acc_iv2 : IntervalD)
    (acc_rat1 acc_rat2 : ℚ)
    (h_acc1 : intervalContains acc_iv1 acc_rat1)
    (h_acc2 : intervalContains acc_iv2 acc_rat2)
    (h_witness_1 : ∀ x ∈ xs, intervalContains (f_interval_1 x) (f_rational_1 x))
    (h_witness_2 : ∀ x ∈ xs, intervalContains (f_interval_2 x) (f_rational_2 x)) :
    let result_iv := xs.foldl (fun (a1, a2) x =>
      (IntervalDyadic.add a1 (f_interval_1 x) p,
       IntervalDyadic.add a2 (f_interval_2 x) p))
      (acc_iv1, acc_iv2)
    let result_rat := xs.foldl (fun (a1, a2) x =>
      (a1 + f_rational_1 x, a2 + f_rational_2 x))
      (acc_rat1, acc_rat2)
    intervalContains result_iv.1 result_rat.1 ∧
    intervalContains result_iv.2 result_rat.2 := by
  induction xs generalizing acc_iv1 acc_iv2 acc_rat1 acc_rat2 with
  | nil =>
    simp only [List.foldl]
    exact ⟨h_acc1, h_acc2⟩
  | cons x xs ih =>
    simp only [List.foldl]
    -- Get witnesses for current element
    have hx1 : intervalContains (f_interval_1 x) (f_rational_1 x) := by
      apply h_witness_1; simp [List.mem_cons]
    have hx2 : intervalContains (f_interval_2 x) (f_rational_2 x) := by
      apply h_witness_2; simp [List.mem_cons]
    -- New accumulators are witnessed
    have h_new1 : intervalContains (IntervalDyadic.add acc_iv1 (f_interval_1 x) p)
                                   (acc_rat1 + f_rational_1 x) := by
      apply add_preserves_containment acc_iv1 (f_interval_1 x) acc_rat1 (f_rational_1 x) p h_acc1 hx1
    have h_new2 : intervalContains (IntervalDyadic.add acc_iv2 (f_interval_2 x) p)
                                   (acc_rat2 + f_rational_2 x) := by
      apply add_preserves_containment acc_iv2 (f_interval_2 x) acc_rat2 (f_rational_2 x) p h_acc2 hx2
    -- Apply IH with new accumulators
    apply ih
    · exact h_new1
    · exact h_new2
    · intro y hy; apply h_witness_1; simp [List.mem_cons]; right; exact hy
    · intro y hy; apply h_witness_2; simp [List.mem_cons]; right; exact hy

/-- Paired fold lemma: If each term witnesses individually for both components,
    then the paired fold witnesses the paired sum.

    This is a generalization of foldl_add_contains_sum to product types. -/
theorem foldl_add_pair_contains_sum {α : Type} [DecidableEq α]
    (xs : List α)
    (f_interval_1 f_interval_2 : α → IntervalD)
    (f_rational_1 f_rational_2 : α → ℚ)
    (p : ℕ)
    (h_witness_1 : ∀ x ∈ xs, intervalContains (f_interval_1 x) (f_rational_1 x))
    (h_witness_2 : ∀ x ∈ xs, intervalContains (f_interval_2 x) (f_rational_2 x)) :
    let result_iv := xs.foldl (fun (acc1, acc2) x =>
      (IntervalDyadic.add acc1 (f_interval_1 x) p,
       IntervalDyadic.add acc2 (f_interval_2 x) p))
      (IntervalDyadic.zero, IntervalDyadic.zero)
    let result_rat := xs.foldl (fun (acc1, acc2) x =>
      (acc1 + f_rational_1 x, acc2 + f_rational_2 x)) (0, 0)
    intervalContains result_iv.1 result_rat.1 ∧
    intervalContains result_iv.2 result_rat.2 := by
  -- The proof is by induction on xs, using foldl_add_invariant for each component
  induction xs with
  | nil =>
    simp only [List.foldl]
    exact ⟨zero_contains_zero, zero_contains_zero⟩
  | cons x xs ih =>
    -- Use the invariant lemma directly
    apply foldl_add_pair_invariant
    · exact zero_contains_zero
    · exact zero_contains_zero
    · exact h_witness_1
    · exact h_witness_2

end Witness
