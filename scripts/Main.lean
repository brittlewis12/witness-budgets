/-
Batch witness budget analyzer CLI.

Usage: lake exe wbudget <Module.Name.Prefix> [--format=json|csv]

Analyzes all declarations whose names start with the given prefix.
-/

import Lean
import WBudget

open Lean Elab Command Meta IO

namespace WBudget.CLI

/-- CLI arguments -/
structure Args where
  modulePrefix : Name
  format : String := "json"  -- "json" or "csv"

/-- Parse command-line arguments -/
def parseArgs (args : List String) : Except String Args :=
  match args with
  | [] => .error "Usage: wbudget <Module.Name.Prefix> [--format=json|csv]"
  | [pfx] => .ok { modulePrefix := pfx.toName }
  | [pfx, fmt] =>
      if fmt.startsWith "--format=" then
        let formatType := fmt.drop 9
        if formatType == "json" || formatType == "csv" then
          .ok { modulePrefix := pfx.toName, format := formatType }
        else
          .error s!"Unknown format: {formatType}. Use 'json' or 'csv'"
      else
        .error s!"Unknown argument: {fmt}"
  | _ => .error "Usage: wbudget <Module.Name.Prefix> [--format=json|csv]"

/-- Get all declarations matching the prefix -/
def getDeclsWithPrefix (env : Environment) (pfx : Name) : List Name :=
  env.constants.fold (init := []) fun acc name _ =>
    if pfx.isPrefixOf name then
      name :: acc
    else
      acc

/-- Convert analysis result to CSV row -/
def resultToCSV (r : AnalysisResult) : String :=
  s!"{r.decl},{r.vbudget},{r.xbudget},{r.visitedCount},{r.elapsedMs}"

/-- Run batch analysis -/
def runBatchAnalysis (_args : Args) : IO Unit := do
  -- Initialize Lean environment (use current environment)
  -- TODO: wire this into the Lean environment so we can actually run analyses.

  -- We need to run this in a proper Lean context
  -- For now, emit error - this needs environment initialization
  IO.eprintln "Error: Batch analysis requires running in Lean environment context"
  IO.eprintln "Use the shell script wrapper: ./scripts/baseline_module.sh <Module.Name>"
  IO.Process.exit 1

/-- Main entry point -/
def main (args : List String) : IO Unit := do
  match parseArgs args with
  | .error msg =>
      IO.eprintln msg
      IO.Process.exit 1
  | .ok parsed =>
      runBatchAnalysis parsed

end WBudget.CLI

/-- Entry point -/
def main := WBudget.CLI.main
