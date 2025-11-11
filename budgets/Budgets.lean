/-
Sample Module for Recipe Demonstration

This module contains intentional witness budget violations
to demonstrate the complete remediation workflow.

Each function is marked with:
- VIOLATION: What classical axiom is used incorrectly
- RECIPE: Which recipe fixes it
- FIX: What the corrected version should look like
-/

import Budgets.ConstructiveQ
import Budgets.NewtonKantorovich
import Budgets.BanachExtraction
import Budgets.QRKConstants
import Budgets.RellichKondrachov1D
import Budgets.RellichKondrachov2D

namespace SampleModule

open Classical  -- Enable classical logic for intentional violations

/-! ## Recipe 1: Require Decidable Instance (10 examples) -/

-- VIOLATION 1: Classical.propDecidable in if-then-else
-- RECIPE: Recipe 1 - Add [Decidable p] constraint
noncomputable def checkProp (p : Prop) : Nat :=
  if p then 1 else 0

-- VIOLATION 2: Classical decidability in filtering
-- RECIPE: Recipe 1 - Require DecidableEq
noncomputable def filterEqual {α : Type} (x : α) (xs : List α) : List α :=
  xs.filter (· == x)

-- VIOLATION 3: Classical decidability in counting
-- RECIPE: Recipe 1 - Add Decidable instance
noncomputable def countSatisfying {α : Type} (p : α → Prop) (xs : List α) : Nat :=
  xs.countP (fun x => if p x then true else false)

-- VIOLATION 4: Implicit classical decidability in find
-- RECIPE: Recipe 1 - Make decidability explicit
noncomputable def findSatisfying {α : Type} (p : α → Prop) (xs : List α) : Option α :=
  xs.find? (fun x => if p x then true else false)

-- VIOLATION 5: Classical decidability in partition
-- RECIPE: Recipe 1 - Add decidable constraint
noncomputable def partitionBy {α : Type} (p : α → Prop) (xs : List α) : List α × List α :=
  (xs.filter (fun x => if p x then true else false),
   xs.filter (fun x => if p x then false else true))

-- VIOLATION 6: Classical equality check
-- RECIPE: Recipe 1 - Use BEq or require DecidableEq
noncomputable def hasDuplicate {α : Type} (xs : List α) : Bool :=
  match xs with
  | [] => false
  | x :: rest => if x ∈ rest then true else hasDuplicate rest

-- VIOLATION 7: Classical membership test
-- RECIPE: Recipe 1 - Require decidable membership
noncomputable def isSubsetOf {α : Type} (xs ys : List α) : Bool :=
  xs.all (fun x => if x ∈ ys then true else false)

-- VIOLATION 8: Classical decidability in takeWhile
-- RECIPE: Recipe 1 - Add [Decidable (p x)] constraint
noncomputable def takeWhileProp {α : Type} (p : α → Prop) (xs : List α) : List α :=
  xs.takeWhile (fun x => if p x then true else false)

-- VIOLATION 9: Classical comparison
-- RECIPE: Recipe 1 - Use Ord or require decidable order
noncomputable def maxByProp {α : Type} (p : α → α → Prop) (x y : α) : α :=
  if p x y then y else x

-- VIOLATION 10: Classical decidability in any
-- RECIPE: Recipe 1 - Make predicate decidable
noncomputable def anyProp {α : Type} (p : α → Prop) (xs : List α) : Bool :=
  xs.any (fun x => if p x then true else false)


/-! ## Recipe 2: Constructive Case Analysis (5 examples) -/

-- VIOLATION 11: Using Classical.em unnecessarily
-- RECIPE: Recipe 2 - Use pattern matching
theorem natZeroOrSucc (n : Nat) : n = 0 ∨ n > 0 := by
  cases Classical.em (n = 0) with
  | inl h => left; exact h
  | inr h => right; omega

-- VIOLATION 12: Classical.em in decidable context
-- RECIPE: Recipe 2 - Use by_cases with decidable instance
theorem listEmptyOrNot {α : Type} (xs : List α) : xs = [] ∨ xs ≠ [] := by
  cases Classical.em (xs = []) with
  | inl h => left; exact h
  | inr h => right; exact h

-- VIOLATION 13: Classical.em for simple disjunction
-- RECIPE: Recipe 2 - Direct constructive proof
theorem boolTrueOrFalse (b : Bool) : b = true ∨ b = false := by
  cases Classical.em (b = true) with
  | inl h => left; exact h
  | inr h => right; cases b <;> trivial

-- VIOLATION 14: Classical.em in computational context
-- RECIPE: Recipe 2 - Use decidable instance
noncomputable def isEvenClassical (n : Nat) : Bool :=
  if n % 2 = 0 then true else false

-- VIOLATION 15: Unnecessary classical reasoning
-- RECIPE: Recipe 2 - Direct decidable proof
theorem optionSomeOrNone {α : Type} (x : Option α) : x.isSome ∨ x.isNone := by
  cases Classical.em x.isSome with
  | inl h => left; exact h
  | inr h => right; cases x <;> simp at *


/-! ## Recipe 3: Invariant-Only Witnesses (5 examples) -/

-- VIOLATION 16: Extracting arbitrary witness
-- RECIPE: Recipe 3 - Use only witness properties
noncomputable def extractPositive (h : ∃ n : Nat, n > 0) : Nat :=
  Classical.choose h

-- VIOLATION 17: Using Classical.choice to pick arbitrary element
-- RECIPE: Recipe 3 - Use Inhabited default instead
noncomputable def getArbitrary {α : Type} [Inhabited α] : α :=
  Classical.choice (⟨default⟩ : Nonempty α)

-- VIOLATION 18: Witness extraction in algorithm
-- RECIPE: Recipe 3 - Return witness with proof, or use invariant only
noncomputable def findWitness {α : Type} (p : α → Prop) (h : ∃ x, p x) : α :=
  Classical.choose h

-- VIOLATION 19: Classical.choose in data structure
-- RECIPE: Recipe 3 - Use Subtype with constructive projection
noncomputable def getMinElement (xs : List Nat) (h : xs ≠ []) : Nat :=
  Classical.choose (by
    cases xs with
    | nil => contradiction
    | cons x _ => exact ⟨x, by simp⟩ : ∃ n, n ∈ xs)

-- VIOLATION 20: Extracting witness for computation
-- RECIPE: Recipe 3 - Compute witness directly, don't extract from existence
noncomputable def findFirstSat {α : Type} (p : α → Prop) (xs : List α) (h : ∃ x ∈ xs, p x) : α :=
  Classical.choose h


/-! ## Recipe 4: Quotient Lifting (NOTE: Skipped in initial demo)

Quotient types in Lean 4 don't expose Quot.out directly.
Real-world quotient violations would involve:
- Using choice to pick representatives
- Not proving operations respect equivalence
- Breaking abstraction in other ways

For MVP demo, we focus on Recipes 1-3 which are more common.
Total violations: 20 across 3 recipe types.
-/


/-! ## Constructive Reference Implementations (for comparison) -/

-- These are CORRECT - showing what the fixes look like
def checkPropFixed (p : Prop) [Decidable p] : Nat :=
  if p then 1 else 0

def filterEqualFixed {α : Type} [DecidableEq α] (x : α) (xs : List α) : List α :=
  xs.filter (· == x)

theorem natZeroOrSuccFixed (n : Nat) : n = 0 ∨ n > 0 := by
  cases n with
  | zero => left; rfl
  | succ n => right; omega

-- Invariant-only witness usage
def useWitnessProperty (_ : ∃ n : Nat, n > 0) : Prop :=
  ∃ m, m > 0  -- Only uses existence, not the witness itself


/-! ## COMPLETE FIXED VERSION - All 20 violations remediated -/

namespace Fixed

/-! ### Recipe 1: Require Decidable Instance (10 fixes) -/

-- FIX 1: Added [Decidable p] constraint
def checkProp (p : Prop) [Decidable p] : Nat :=
  if p then 1 else 0

-- FIX 2: Added [DecidableEq α] constraint
def filterEqual {α : Type} [DecidableEq α] (x : α) (xs : List α) : List α :=
  xs.filter (· == x)

-- FIX 3: Added [Decidable (p x)] constraint
def countSatisfying {α : Type} (p : α → Prop) [DecidablePred p] (xs : List α) : Nat :=
  xs.countP (fun x => if p x then true else false)

-- FIX 4: Added decidable constraint
def findSatisfying {α : Type} (p : α → Prop) [DecidablePred p] (xs : List α) : Option α :=
  xs.find? (fun x => if p x then true else false)

-- FIX 5: Added decidable constraint
def partitionBy {α : Type} (p : α → Prop) [DecidablePred p] (xs : List α) : List α × List α :=
  (xs.filter (fun x => if p x then true else false),
   xs.filter (fun x => if p x then false else true))

-- FIX 6: Added [DecidableEq α] for membership test
def hasDuplicate {α : Type} [DecidableEq α] (xs : List α) : Bool :=
  match xs with
  | [] => false
  | x :: rest => if x ∈ rest then true else hasDuplicate rest

-- FIX 7: Added [DecidableEq α] for membership test
def isSubsetOf {α : Type} [DecidableEq α] (xs ys : List α) : Bool :=
  xs.all (fun x => if x ∈ ys then true else false)

-- FIX 8: Added decidable constraint
def takeWhileProp {α : Type} (p : α → Prop) [DecidablePred p] (xs : List α) : List α :=
  xs.takeWhile (fun x => if p x then true else false)

-- FIX 9: Added [Decidable (p x y)] constraint
def maxByProp {α : Type} (p : α → α → Prop) [DecidableRel p] (x y : α) : α :=
  if p x y then y else x

-- FIX 10: Added decidable constraint
def anyProp {α : Type} (p : α → Prop) [DecidablePred p] (xs : List α) : Bool :=
  xs.any (fun x => if p x then true else false)


/-! ### Recipe 2: Constructive Case Analysis (5 fixes) -/

-- FIX 11: Use pattern matching instead of Classical.em
theorem natZeroOrSucc (n : Nat) : n = 0 ∨ n > 0 := by
  cases n with
  | zero => left; rfl
  | succ n => right; omega

-- FIX 12: Use decidable instance instead of Classical.em
theorem listEmptyOrNot {α : Type} (xs : List α) : xs = [] ∨ xs ≠ [] := by
  cases xs with
  | nil => left; rfl
  | cons _ _ => right; intro h; contradiction

-- FIX 13: Use pattern matching on Bool
theorem boolTrueOrFalse (b : Bool) : b = true ∨ b = false := by
  cases b <;> simp

-- FIX 14: Already computable! Nat has decidable equality
def isEvenClassical (n : Nat) : Bool :=
  if n % 2 = 0 then true else false

-- FIX 15: Use pattern matching on Option
theorem optionSomeOrNone {α : Type} (x : Option α) : x.isSome ∨ x.isNone := by
  cases x <;> simp


/-! ### Recipe 3: Invariant-Only Witnesses (5 fixes) -/

-- FIX 16: Don't extract witness - use only its property
def extractPositive (_ : ∃ n : Nat, n > 0) : Prop :=
  ∃ n, n > 0  -- Only uses existence, not the specific witness

-- Alternative: If you need a concrete positive number, construct it directly
def getPositiveNumber : Nat := 1

-- FIX 17: Use default directly instead of going through Nonempty
def getArbitrary {α : Type} [Inhabited α] : α :=
  default

-- FIX 18: Use List.find? with decidable predicate
def findWitness {α : Type} (p : α → Prop) [DecidablePred p] (xs : List α) : Option α :=
  xs.find? p

-- FIX 19: Just use head (or fold to find minimum constructively)
-- The key is: no Classical.choose extraction
def getMinElement (xs : List Nat) (_ : xs ≠ []) : Option Nat :=
  xs.head?  -- Computable, no choice needed

-- FIX 20: Use decidable predicate with List.find?
def findFirstSat {α : Type} (p : α → Prop) [DecidablePred p] (xs : List α)
    (_ : ∃ x ∈ xs, p x) : Option α :=
  xs.find? p

end Fixed

end SampleModule
