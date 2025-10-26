/-
Toy test theorems for witness budget calibration.

These tests establish baseline detection for:
- C0: Fully constructive (no classical axioms)
- C3: Classical logic (excluded middle)
- C5: Full choice (choice axiom)
-/

import WBudget

-- Test 1: Direct C3 (uses Classical.em)
-- Expected: vBudget = C3, trigger = Classical.em
theorem test_direct_c3 (p : Prop) : p ∨ ¬p :=
  Classical.em p

-- Test 2: Direct C5 (uses Classical.choice)
-- Expected: vBudget = C5, trigger = Classical.choice
theorem test_direct_c5 : ∃ _f : (Nat → Nat) → Nat, True := by
  have h : Nonempty ((Nat → Nat) → Nat) := ⟨fun _ => 0⟩
  exact ⟨Classical.choice h, trivial⟩

-- Test 3: C0 (fully constructive, no classical axioms)
-- Expected: vBudget = C0, no triggers
theorem test_constructive : 2 + 2 = 4 := rfl

-- Test 4: Transitive C3 (theorem → helper → em)
-- Expected: vBudget = C5 (transitively via em→choice), path shows helper
def helper_em (p : Prop) : p ∨ ¬p := Classical.em p

theorem test_transitive (p : Prop) : p ∨ ¬p := helper_em p

-- Test 5: Implicit C3 (noncomputable definition uses Classical.propDecidable)
-- Expected: vBudget = C5 (typeclass synthesis provides classical decidability)
open Classical in
noncomputable def test_implicit (p : Prop) : Nat :=
  @ite Nat p (propDecidable p) 1 0

-- Test 6: Constructive value with classical proof (v≠x test)
-- Expected: vBudget = C3+ (classical in proof), xBudget = C0 (extractable value)
def fastAlgorithm : Nat := 42

theorem fastAlgorithm_correct : fastAlgorithm > 0 := by
  -- Use classical EM explicitly in proof
  cases Classical.em (fastAlgorithm > 0) with
  | inl h => exact h
  | inr h => exact absurd (by decide : fastAlgorithm > 0) h

-- Verification that these compile
#check test_direct_c3
#check test_direct_c5
#check test_constructive
#check test_transitive
#check test_implicit
#check fastAlgorithm
#check fastAlgorithm_correct

-- Test 7: Cache keying regression test
-- Forces the analyzer to visit Classical.em in BOTH positions within a SINGLE declaration.
-- This tests that the (Name × Position) cache allows the same constant to be analyzed
-- in different positions, rather than skipping the second visit.

noncomputable def cacheBugTest (p : Prop) : {_d : Decidable p // p ∨ ¬p} :=
  -- This is a Subtype with two components:
  -- 1. Decidable p: uses Classical.propDecidable (which depends on Classical.em) in Type position
  -- 2. Proof of p ∨ ¬p: uses Classical.em directly in Prop position
  ⟨Classical.propDecidable p, Classical.em p⟩

-- Expected behavior with (Name × Position) cache:
-- - vBudget = C5 (all classical deps found)
-- - xBudget = C5 (Classical.propDecidable in Type + its em dependency in Type)
--
-- Bug with Name-only cache:
-- When analyzing the Subtype value:
-- 1. First field (Decidable p) is analyzed in Type → visits Classical.propDecidable
--    → visits Classical.em in Type → cache contains "Classical.em"
-- 2. Second field (p ∨ ¬p proof) is analyzed in Prop → visits Classical.em
--    → BUT cache check finds "Classical.em" already visited → SKIP!
-- 3. Result: Classical.em only recorded in Type position (from propDecidable's deps)
--    Missing: Direct Classical.em usage in Prop position
--
-- The fix allows both (Classical.em, Type) and (Classical.em, Prop) to coexist.

-- Test 8: Prop→Type elimination (Classical.choose)
-- This is the classic elimination: extracting computational data from a Prop proof
noncomputable def extractWitness (h : ∃ n : Nat, n > 0) : Nat :=
  Classical.choose h

-- Expected: vBudget=C5, xBudget=C5
-- Classical.choose is analyzed in Type position (def value)
-- The argument h (exists proof) is analyzed in Prop position
-- But Classical.choose itself must be Type-flow because it produces computational data

-- Test the #wbudget command on each theorem
#wbudget test_direct_c3
#wbudget test_direct_c5
#wbudget test_constructive
#wbudget test_transitive
#wbudget test_implicit
#wbudget fastAlgorithm
#wbudget fastAlgorithm_correct
#wbudget cacheBugTest
#wbudget extractWitness

-- Test JSON export
#wbudget_json test_constructive
