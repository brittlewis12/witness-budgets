/-
The #wbudget command implementation
-/

import Lean
import WBudget.WBudget
import WBudget.Analysis
import WBudget.PropTypeFlow
import WBudget.Lints
import WBudget.Output

namespace WBudget

open Lean Elab Command Meta

/-- Get current time in milliseconds -/
def getTimeMs : IO Nat := do
  IO.monoMsNow

/-- Run analysis and produce result -/
def runAnalysis (declName : Name) : CommandElabM AnalysisResult := do
  let startTime ← liftTermElabM <| liftM getTimeMs

  -- Run the flow analysis in MetaM context (for xBudget)
  let flowState ← liftTermElabM <| Meta.MetaM.run' do
    analyzeDeclarationFlow declName {}

  -- Run lints
  let lintWarnings ← liftTermElabM <| Meta.MetaM.run' do
    runLints declName

  let endTime ← liftTermElabM <| liftM getTimeMs
  let elapsedMs := endTime - startTime

  -- Deduplicate triggers: Type-flow takes precedence over Prop-only
  let dedupedState := deduplicateTriggers flowState

  -- Compute budgets
  let vbudget := computeVBudgetFromFlow flowState  -- Uses deduplication internally
  let xbudget := computeXBudget flowState

  -- Combine all triggers for backward compat (using deduplicated state)
  let allTriggers := dedupedState.typeFlowTriggers ++ dedupedState.propOnlyTriggers

  -- Build result with position-aware trigger lists (deduplicated)
  return {
    decl := declName.toString
    vbudget := vbudget.toString
    xbudget := xbudget.toString
    triggers := allTriggers
    typeFlowTriggers := dedupedState.typeFlowTriggers
    propOnlyTriggers := dedupedState.propOnlyTriggers
    visitedCount := flowState.visitedCount
    fuelExhausted := flowState.fuelExhausted
    elapsedMs := elapsedMs
    lintWarnings := lintWarnings
  }

/-- #wbudget command syntax -/
syntax (name := wbudget) "#wbudget " ident : command

/-- #wbudget command elaboration -/
@[command_elab wbudget]
def elabWBudget : CommandElab := fun stx => do
  match stx with
  | `(command| #wbudget $id:ident) =>
      let declName := id.getId

      -- Resolve the identifier to a full name
      let env ← getEnv
      match env.find? declName with
      | none =>
          logError s!"Declaration '{declName}' not found"
          return
      | some _ =>
          -- Run analysis
          let result ← runAnalysis declName

          -- Output results
          logInfo result.toPretty

  | _ =>
      throwUnsupportedSyntax

/-- #wbudget_json command syntax -/
syntax (name := wbudget_json) "#wbudget_json " ident : command

/-- #wbudget_json command elaboration (machine-readable output) -/
@[command_elab wbudget_json]
def elabWBudgetJson : CommandElab := fun stx => do
  match stx with
  | `(command| #wbudget_json $id:ident) =>
      let declName := id.getId

      -- Resolve the identifier to a full name
      let env ← getEnv
      match env.find? declName with
      | none =>
          logError s!"Declaration '{declName}' not found"
          return
      | some _ =>
          -- Run analysis
          let result ← runAnalysis declName

          -- Output JSON
          logInfo result.toJson

  | _ =>
      throwUnsupportedSyntax

end WBudget
