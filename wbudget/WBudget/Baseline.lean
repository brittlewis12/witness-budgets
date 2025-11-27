/-
Baseline budget analysis for a Lean module/directory.

Usage: lake exe baseline_module <Module.Name>
Output: JSON array of analysis results
-/

import Lean
import WBudget.Command
import WBudget.Output

open Lean Elab Command Meta

namespace WBudget.Baseline

/-- Get all declarations defined in a specific module file -/
def getDeclsInModule (modPrefix : Name) (moduleFile : Option Name := none) : MetaM (List Name) := do
  let env ← getEnv
  let prefixStr := modPrefix.toString

  -- If moduleFile is provided, filter by source file; otherwise use prefix only
  let allDecls := env.constants.fold (init := []) fun acc name info =>
    -- Filter by name prefix
    if !name.toString.startsWith prefixStr then
      acc
    else
      match moduleFile with
      | none =>
          -- No file filter, include all matching prefix
          name :: acc
      | some modFile =>
          -- Filter by source module
          match env.getModuleIdxFor? name with
          | none => acc  -- Not from any module (builtin)
          | some modIdx =>
              if h : modIdx.toNat < env.allImportedModuleNames.size then
                let modName := env.allImportedModuleNames[modIdx.toNat]
                if modName == modFile then
                  name :: acc
                else
                  acc
              else
                acc
  return allDecls

/-- Run analysis on all declarations in a module -/
def baselineModule (modName : Name) (moduleFile : Option Name := none) : CommandElabM Unit := do
  -- Get all declarations
  let decls ← liftTermElabM <| Meta.MetaM.run' do
    getDeclsInModule modName moduleFile

  IO.println s!"Analyzing {decls.length} declarations in module {modName}..."
  IO.println "["  -- Start JSON array

  let mut first := true
  for decl in decls do
    try
      -- Run analysis
      let result ← WBudget.runAnalysis decl

      -- Print JSON (with comma separator for array)
      if !first then
        IO.print ","
      IO.println result.toJson
      first := false
    catch _ =>
      IO.eprintln s!"Error analyzing {decl}"

  IO.println ""
  IO.println "]"  -- End JSON array

/-- #baseline_module command syntax -/
syntax (name := baseline_module) "#baseline_module " ident (ident)? : command

/-- #baseline_module command elaboration -/
@[command_elab baseline_module]
def elabBaselineModule : CommandElab := fun stx => do
  match stx with
  | `(command| #baseline_module $id:ident $modFile:ident) =>
      let modName := id.getId
      let moduleFile := some modFile.getId
      baselineModule modName moduleFile
  | `(command| #baseline_module $id:ident) =>
      let modName := id.getId
      baselineModule modName none
  | _ =>
      throwUnsupportedSyntax

end WBudget.Baseline
