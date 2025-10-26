/-
Output formatting: JSON and CSV generation
-/

import Lean
import WBudget.WBudget
import WBudget.Analysis
import WBudget.Lints

namespace WBudget

open Lean

/-- Check if a string contains a substring -/
def hasSubstring (s : String) (substr : String) : Bool :=
  (s.splitOn substr).length > 1

/-- Map trigger names to remediation recipe hints -/
def getRecipeHint (triggerName : String) : Option String :=
  if hasSubstring triggerName "propDecidable" then
    some "Recipe 1: Require Decidable Instance (docs/constructive-playbook.md#recipe-1)"
  else if hasSubstring triggerName "Classical.em" then
    some "Recipe 2: Constructive Case Analysis (docs/constructive-playbook.md#recipe-2)"
  else if hasSubstring triggerName "Classical.choose" || hasSubstring triggerName "Classical.some" then
    some "Recipe 3: Invariant-Only Witnesses (docs/constructive-playbook.md#recipe-3)"
  else if hasSubstring triggerName "Quot.out" || hasSubstring triggerName "Trunc.out" then
    some "Recipe 4: Quotient Lifting (docs/constructive-playbook.md#recipe-4)"
  else if hasSubstring triggerName "decEq" then
    some "Recipe 5: Avoid Classical.decEq (docs/constructive-playbook.md#recipe-5)"
  else if hasSubstring triggerName "by_contra" || hasSubstring triggerName "byContradiction" then
    some "Recipe 6: Direct Proofs (docs/constructive-playbook.md#recipe-6)"
  else
    none

/-- JSON-serializable analysis result -/
structure AnalysisResult where
  decl : String
  vbudget : String
  xbudget : String := "C0"
  triggers : Array Trigger  -- All triggers (for backward compat)
  typeFlowTriggers : Array Trigger := #[]  -- Triggers in Type positions (affect xBudget)
  propOnlyTriggers : Array Trigger := #[]  -- Triggers in Prop positions only
  visitedCount : Nat
  fuelExhausted : Bool
  elapsedMs : Nat
  lintWarnings : Array LintWarning := #[]
deriving Repr

/-- Convert trigger to JSON string -/
def Trigger.toJson (t : Trigger) : String :=
  s!"\{\"level\":\"{t.level}\",\"const\":\"{t.const}\",\"path\":{toJsonArray t.path}}"
where
  toJsonArray (xs : List String) : String :=
    "[" ++ String.intercalate "," (xs.map (fun x => s!"\"{x}\"")) ++ "]"

/-- Convert analysis result to JSON -/
def AnalysisResult.toJson (r : AnalysisResult) : String :=
  let triggersJson := "[" ++ String.intercalate "," (r.triggers.toList.map Trigger.toJson) ++ "]"
  let warningsJson := "[" ++ String.intercalate "," (r.lintWarnings.toList.map LintWarning.toJson) ++ "]"
  s!"\{
  \"decl\": \"{r.decl}\",
  \"vbudget\": \"{r.vbudget}\",
  \"xbudget\": \"{r.xbudget}\",
  \"triggers\": {triggersJson},
  \"visited_count\": {r.visitedCount},
  \"fuel_exhausted\": {if r.fuelExhausted then "true" else "false"},
  \"elapsed_ms\": {r.elapsedMs},
  \"lint_warnings\": {warningsJson}
}"

/-- Convert analysis result to CSV row -/
def AnalysisResult.toCsv (r : AnalysisResult) : String :=
  s!"{r.decl},{r.vbudget},{r.xbudget},{r.visitedCount},{if r.fuelExhausted then "true" else "false"},{r.elapsedMs}"

/-- Pretty-print analysis result for terminal output -/
def AnalysisResult.toPretty (r : AnalysisResult) : String :=
  let header := s!"Declaration: {r.decl}"
  let budget := s!"  vBudget: {r.vbudget}  |  xBudget: {r.xbudget}"
  let stats := s!"  Visited: {r.visitedCount} constants{if r.fuelExhausted then " (FUEL EXHAUSTED)" else ""}"
  let perf := s!"  Time: {r.elapsedMs}ms"

  -- Format triggers with position awareness
  let formatTriggers (triggers : Array Trigger) (label : String) : String :=
    let triggerLines := triggers.toList.map fun t =>
      let pathStr := String.intercalate " → " t.path
      s!"  • [{t.level}] {t.const}\n      Path: {pathStr}"
    if triggers.isEmpty then
      s!"  {label}: none"
    else
      s!"  {label}:\n" ++ String.intercalate "\n" triggerLines

  -- Show Type-flow and Prop-only triggers separately if we have position data
  let triggersSection :=
    if !r.typeFlowTriggers.isEmpty || !r.propOnlyTriggers.isEmpty then
      -- New format: show position-aware breakdown
      let typeSection := formatTriggers r.typeFlowTriggers "Type-flow triggers (affect extraction)"
      let propSection := formatTriggers r.propOnlyTriggers "Prop-only triggers (verification only)"
      typeSection ++ "\n" ++ propSection
    else if r.triggers.isEmpty then
      "  Triggers: none (fully constructive)"
    else
      -- Fallback for backward compat: show all triggers without position
      let triggerLines := r.triggers.toList.map fun t =>
        let pathStr := String.intercalate " → " t.path
        s!"  • [{t.level}] {t.const}\n      Path: {pathStr}"
      "  Triggers:\n" ++ String.intercalate "\n" triggerLines

  -- Collect unique recipe hints from Type-flow triggers
  let recipeHints := r.typeFlowTriggers.toList.filterMap (fun t => getRecipeHint t.const)
    |> List.eraseDups
  let remediationSection :=
    if recipeHints.isEmpty then
      ""
    else
      let hintLines := recipeHints.map (fun hint => s!"  → {hint}")
      "\n  Remediation Hints (for xBudget improvement):\n" ++ String.intercalate "\n" hintLines

  let lintLines := r.lintWarnings.toList.map fun w =>
    s!"  ⚠ {w.message}\n      Hint: {w.hint}"
  let lints :=
    if r.lintWarnings.isEmpty then
      ""
    else
      "\n  Lint Warnings:\n" ++ String.intercalate "\n" lintLines

  String.intercalate "\n" [header, budget, stats, perf, triggersSection ++ remediationSection ++ lints]

end WBudget
