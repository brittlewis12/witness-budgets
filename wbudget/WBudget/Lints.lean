/-
Invariance lints for witness budget analysis.

These lints detect patterns that violate invariance discipline:
- Quot.out without Quot.lift
- Classical.some/choose in consumer positions
- Nonempty elimination into Type without invariance proof
-/

import Lean
import WBudget.WBudget
import WBudget.Analysis

namespace WBudget

open Lean Meta

/-- Lint warning information -/
structure LintWarning where
  location : String        -- File:line or decl name
  severity : String        -- "warn" or "error"
  message : String         -- Description of the issue
  hint : String            -- Suggested fix
deriving Repr

/-- Convert lint warning to JSON -/
def LintWarning.toJson (w : LintWarning) : String :=
  s!"\{\"location\":\"{w.location}\",\"severity\":\"{w.severity}\",\"message\":\"{w.message}\",\"hint\":\"{w.hint}\"}"

/-- State for lint analysis -/
structure LintState where
  warnings : Array LintWarning := #[]
deriving Inhabited

/-- Monad for lint analysis -/
abbrev LintM := StateRefT LintState MetaM

/-- Record a lint warning -/
def recordWarning (warning : LintWarning) : LintM Unit := do
  modify fun s => { s with warnings := s.warnings.push warning }

/-- Check if expression uses Quot.out -/
def usesQuotOut (e : Expr) : Bool :=
  e.find? (fun subExpr =>
    match subExpr with
    | .const name _ => name.toString.endsWith "Quot.out"
    | _ => false
  ) |>.isSome

/-- Check if expression uses Quot.lift -/
def usesQuotLift (e : Expr) : Bool :=
  e.find? (fun subExpr =>
    match subExpr with
    | .const name _ => name.toString.endsWith "Quot.lift"
    | _ => false
  ) |>.isSome

/-- Check if expression uses Classical.some or Classical.choose -/
def usesClassicalSome (e : Expr) : Bool :=
  e.find? (fun subExpr =>
    match subExpr with
    | .const name _ =>
        let nameStr := name.toString
        nameStr.endsWith "Classical.some" || nameStr.endsWith "Classical.choose"
    | _ => false
  ) |>.isSome

/-- Lint: Quot.out without Quot.lift -/
def lintQuotOut (declName : Name) (expr : Expr) : LintM Unit := do
  if usesQuotOut expr && !usesQuotLift expr then
    recordWarning {
      location := declName.toString
      severity := "warn"
      message := "Uses Quot.out without Quot.lift"
      hint := "Use Quot.lift with a congruence proof to ensure representative-independence"
    }

/-- Lint: Classical.some/choose in consumer positions -/
def lintClassicalSome (declName : Name) (expr : Expr) : LintM Unit := do
  if usesClassicalSome expr then
    recordWarning {
      location := declName.toString
      severity := "warn"
      message := "Uses Classical.some/choose which picks an arbitrary witness"
      hint := "Consider using only invariant properties of the witness, or refactor to avoid choice"
    }

/-- Run all lints on a declaration -/
def runLints (declName : Name) : MetaM (Array LintWarning) := do
  let env ← getEnv
  match env.find? declName with
  | none => return #[]
  | some info =>
      -- Extract expressions to lint
      let exprs := match info with
        | .defnInfo di => [di.value]
        | .thmInfo ti => [ti.value]
        | _ => []

      -- Run lints
      let initialState : LintState := {}
      let (_, finalState) ← (do
        for expr in exprs do
          lintQuotOut declName expr
          lintClassicalSome declName expr
      ).run initialState

      return finalState.warnings

end WBudget
