/-
Core witness budget analysis module.
Defines budget levels, triggers, and analysis infrastructure.
-/

import Lean

namespace WBudget

/-- Budget levels from C0 (fully constructive) to C5 (full choice) -/
inductive BudgetLevel where
  | C0  -- Fully witnessful (intuitionistic logic only)
  | C1  -- Existence-only (propositional truncation)
  | C2  -- Countable choice (ACω, DC)
  | C3  -- Classical logic (LEM)
  | C4  -- Choice fragments (Ultrafilter Lemma)
  | C5  -- Full choice (AC, Zorn's Lemma)
deriving Repr, BEq, Ord

/-- Convert budget level to string -/
def BudgetLevel.toString : BudgetLevel → String
  | .C0 => "C0"
  | .C1 => "C1"
  | .C2 => "C2"
  | .C3 => "C3"
  | .C4 => "C4"
  | .C5 => "C5"

instance : ToString BudgetLevel where
  toString := BudgetLevel.toString

/-- Maximum of two budget levels (composition rule) -/
def BudgetLevel.max (a b : BudgetLevel) : BudgetLevel :=
  match compare a b with
  | .gt => a
  | .eq => a
  | .lt => b

/-- Trigger information: which constant triggered which budget level -/
structure Trigger where
  level : BudgetLevel
  const : String
  path : List String  -- Dependency path from declaration to trigger
deriving Repr

/-- Classical axiom triggers (C5 - Full Choice) -/
def c5Triggers : List String := [
  "Classical.choice",
  "Choice.choice",
  "Classical.epsilon",
  "Nonempty.some"
]

/-- Classical logic triggers (C3 - LEM and friends) -/
def c3Triggers : List String := [
  "Classical.em",
  "Classical.propDecidable",
  "Classical.decEq",
  "Classical.by_contra",
  "Classical.byContradiction",
  "Classical.some",
  "Classical.choose",
  "Decidable.em"
]

/-- Countable choice triggers (C2) -/
def c2Triggers : List String := [
  "Classical.axiomOfChoice",  -- When restricted to countable
  "Classical.decidableInhabited"
]

/-- Truncation/existence triggers (C1) -/
def c1Triggers : List String := [
  "Quot.out",
  "Trunc.out",
  "Nonempty.elim"
]

/-- Check if a constant name matches a trigger -/
def isTrigger (name : String) (triggers : List String) : Bool :=
  triggers.any (fun t => name.endsWith t || name == t)

/-- Classify a constant by its trigger level -/
def classifyConstant (name : String) : Option BudgetLevel :=
  if isTrigger name c5Triggers then some .C5
  else if isTrigger name c3Triggers then some .C3
  else if isTrigger name c2Triggers then some .C2
  else if isTrigger name c1Triggers then some .C1
  else none

end WBudget
