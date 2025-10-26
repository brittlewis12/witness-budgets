/-
Core analysis implementation: Expr traversal, dependency collection, budget computation.
-/

import Lean
import WBudget.WBudget

namespace WBudget

open Lean Meta Elab

/-- State for dependency analysis -/
structure AnalysisState where
  visited : Std.HashSet Name := {}
  triggers : Array Trigger := #[]
  visitedCount : Nat := 0
  fuelExhausted : Bool := false
deriving Inhabited

/-- Configuration for analysis -/
structure AnalysisConfig where
  fuelLimit : Nat := 5000
  trackPaths : Bool := true
deriving Inhabited

/-- Monad for analysis with state and config -/
abbrev AnalysisM := StateRefT AnalysisState MetaM

/-- Check if we've exceeded fuel limit -/
def checkFuel (config : AnalysisConfig) : AnalysisM Bool := do
  let state ← get
  if state.visitedCount ≥ config.fuelLimit then
    modify fun s => { s with fuelExhausted := true }
    return false
  else
    return true

/-- Record a trigger found in the dependency graph -/
def recordTrigger (level : BudgetLevel) (constName : Name) (path : List String) : AnalysisM Unit := do
  let trigger : Trigger := {
    level := level,
    const := constName.toString,
    path := path
  }
  modify fun s => { s with triggers := s.triggers.push trigger }

/-- Collect all constants from an expression -/
partial def collectConstants (e : Expr) : List Name :=
  e.foldConsts [] fun name acc =>
    if acc.contains name then acc else name :: acc

/-- Analyze a single constant and its dependencies -/
partial def analyzeConstant (config : AnalysisConfig) (name : Name) (path : List String) : AnalysisM Unit := do
  -- Check if already visited
  let state ← get
  if state.visited.contains name then
    return ()

  -- Check fuel
  let hasFuel ← checkFuel config
  if !hasFuel then
    return ()

  -- Mark as visited
  modify fun s => { s with
    visited := s.visited.insert name,
    visitedCount := s.visitedCount + 1
  }

  -- Check if this constant is a trigger (but always continue analyzing dependencies)
  let nameStr := name.toString
  match classifyConstant nameStr with
  | some level =>
      recordTrigger level name (path ++ [nameStr])
  | none => pure ()

  -- Get constant info from environment
  let env ← getEnv
  match env.find? name with
  | none => return ()  -- Not found, skip
  | some info =>
      -- Extract the expression from the constant
      -- For theorems, analyze both type and value
      let exprs := match info with
        | .axiomInfo ai => [ai.type]
        | .defnInfo di => [di.type, di.value]
        | .thmInfo ti => [ti.type, ti.value]
        | .opaqueInfo oi => [oi.type, oi.value]
        | .quotInfo _ => []
        | .inductInfo _ => []
        | .ctorInfo _ => []
        | .recInfo _ => []

      -- Collect constants from all expressions
      let allConsts := exprs.flatMap collectConstants
      let constants := allConsts.eraseDups

      -- Recursively analyze dependencies
      for depName in constants do
        analyzeConstant config depName (path ++ [nameStr])

/-- Analyze a declaration by name -/
def analyzeDeclaration (declName : Name) (config : AnalysisConfig := {}) : MetaM AnalysisState := do
  let initialState : AnalysisState := {}
  let (_, finalState) ← (analyzeConstant config declName [declName.toString]).run initialState
  return finalState

/-- Compute the overall budget level from triggers -/
def computeBudget (state : AnalysisState) : BudgetLevel :=
  if state.triggers.isEmpty then
    .C0  -- No triggers found, fully constructive
  else
    state.triggers.foldl (fun maxLevel trigger => BudgetLevel.max maxLevel trigger.level) .C0

end WBudget
