/-
Prop→Type flow analysis for xBudget computation.

This module tracks which parts of a theorem flow into computational (Type) positions
vs proof-only (Prop) positions. Classical axioms confined to Prop don't affect
extraction budget (xBudget), even though they affect verification budget (vBudget).
-/

import Lean
import WBudget.WBudget
import WBudget.Analysis

namespace WBudget

open Lean Meta

/-- Position in the expression tree: Prop or Type -/
inductive Position where
  | prop   -- Proof position (doesn't affect extraction)
  | type   -- Computational position (affects extraction)
deriving Repr, BEq, Hashable

/-- Extended state that tracks positions -/
structure FlowState where
  visited : Std.HashSet (Name × Position) := {}  -- Cache by (Name, Position) to avoid missing Type visits
  typeFlowTriggers : Array Trigger := #[]  -- Triggers in Type positions only
  propOnlyTriggers : Array Trigger := #[]  -- Triggers confined to Prop
  isPropCache : Std.HashMap Nat Bool := {}  -- Memoized Meta.isProp results (keyed by expr hash)
  exprDepth : Nat := 0  -- Current expression traversal depth
  visitedCount : Nat := 0
  fuelExhausted : Bool := false
deriving Inhabited

/-- Configuration with limits -/
structure FlowConfig where
  maxExprDepth : Nat := 150  -- Maximum expression nesting depth
  fuelLimit : Nat := 5000    -- Maximum constants to visit
deriving Inhabited

/-- Monad for flow analysis -/
abbrev FlowM := StateRefT FlowState MetaM

/-- Check if an expression's type eliminates into Type.
    Used to detect Prop→Type eliminations.
    Optimized version that takes the function type as input to avoid duplicate inference.
    Guards against loose bvars and uses tryCatch for resilience. -/
def resultIsType (fnType : Expr) : MetaM Bool := do
  -- Guard: don't try to infer type of expressions with loose bound variables
  if fnType.hasLooseBVars then
    return false  -- Conservative: assume Prop if term is open

  tryCatch
    (do
      let typeSort ← inferType fnType
      match typeSort with
      | .sort (.succ _) => return true   -- Type u (computational)
      | .sort .zero => return false      -- Prop (proof-only)
      | _ => return false                -- Unknown, conservatively assume Prop
    )
    (fun _ => pure false)  -- On error, conservatively assume Prop

/-- Memoized check if an expression is Prop-sorted.
    Uses cache to avoid repeated type inference. -/
def isMemoizedProp (expr : Expr) : FlowM Bool := do
  -- Fast path: literal Prop sort
  match expr with
  | .sort .zero => return true
  | _ => pure ()

  -- Guard: don't try isProp on expressions with loose bvars
  if expr.hasLooseBVars then
    return false  -- Conservative: assume not Prop if term is open

  -- Check cache using expression hash as key
  let exprHash := expr.hash.toNat
  let state ← get
  match state.isPropCache[exprHash]? with
  | some cached => return cached
  | none =>
      -- Expensive check with Meta.isProp
      try
        let result ← isProp expr
        modify fun s => { s with isPropCache := s.isPropCache.insert exprHash result }
        return result
      catch _ =>
        -- On error, conservatively assume not Prop
        return false

/-- Record a trigger with its position -/
def recordFlowTrigger (level : BudgetLevel) (constName : Name) (path : List String) (pos : Position) : FlowM Unit := do
  let trigger : Trigger := {
    level := level,
    const := constName.toString,
    path := path
  }
  match pos with
  | Position.type =>
      modify fun s => { s with typeFlowTriggers := s.typeFlowTriggers.push trigger }
  | Position.prop =>
      modify fun s => { s with propOnlyTriggers := s.propOnlyTriggers.push trigger }

mutual
  /-- Traverse an expression and analyze constants with position tracking.
      Detects Prop→Type eliminations and respects expression depth limits. -/
  partial def analyzeExprWithPosition (config : FlowConfig) (expr : Expr) (path : List String) (pos : Position) : FlowM Unit := do
    -- Check expression depth guard
    let state ← get
    if state.exprDepth ≥ config.maxExprDepth then
      return ()

    -- Increment depth - use manual cleanup to ensure decrement happens
    modify fun s => { s with exprDepth := s.exprDepth + 1 }

    -- Perform analysis (wrapped so we can decrement at the end)
    let result ← match expr with
      | .const name _ =>
          -- Direct constant reference - analyze in current position
          analyzeConstantFlow config name path pos

      | .forallE _ binderType body _ =>
          -- Pi type: check if binder type is Prop-sorted
          -- Dependencies in Prop-typed binders stay in Prop position
          do
            let binderIsProp ← isMemoizedProp binderType
            let binderPos := if binderIsProp then Position.prop else pos
            analyzeExprWithPosition config binderType path binderPos
            analyzeExprWithPosition config body path pos

      | .app fn arg =>
          -- Application: analyze function in current position
          do
            analyzeExprWithPosition config fn path pos

            -- Detect Prop→Type eliminations by checking both binder and codomain
            -- Use tryCatch to handle both inferType and whnf panics gracefully
            let argPos ← tryCatch
              (do
                -- Guard: skip type analysis if fn has loose bvars (prevents whnf panic)
                if fn.hasLooseBVars then
                  return pos  -- Conservative: inherit position if term is open

                let fnType ← inferType fn

                -- Guard against loose bvars before calling whnf
                let fnTypeWhnf ←
                  if fnType.hasLooseBVars then
                    pure fnType  -- Skip whnf if term is open
                  else
                    tryCatch
                      (whnf fnType)
                      (fun _ => pure fnType)  -- On whnf failure, use un-reduced type

                match fnTypeWhnf with
                | .forallE _ binderType body _ =>
                    do
                      -- Check if the binder expects a Prop argument
                      let binderIsProp ← isMemoizedProp binderType

                      if binderIsProp then
                        -- Check if function result is Type (Prop→Type elimination!)
                        -- resultIsType now guards against loose bvars internally
                        let appResultIsType ← resultIsType body

                        if appResultIsType && pos == Position.type then
                          -- Prop→Type elimination detected!
                          -- Example: Classical.choose : (∃ x, P x) → α
                          -- The argument (∃ x, P x) is Prop, but result α is Type
                          -- Classical axioms in the Prop witness affect extraction budget
                          -- Analyze argument in Type position so triggers credit to xBudget
                          return Position.type
                        else
                          -- Prop argument in Prop context, or Type result but not in Type position
                          return Position.prop
                      else
                        -- Type argument: inherit caller's position
                        return pos
                | _ =>
                    -- Not a forall type, conservatively inherit position
                    return pos)
              (fun _ => pure pos)  -- On any error, conservatively inherit position

            analyzeExprWithPosition config arg path argPos

      | .lam _ binderType body _ =>
          -- Lambda: structural traversal
          do
            analyzeExprWithPosition config binderType path pos
            analyzeExprWithPosition config body path pos

      | .letE _ type value body _ =>
          -- Let binding: analyze all components
          do
            analyzeExprWithPosition config type path pos
            analyzeExprWithPosition config value path pos
            analyzeExprWithPosition config body path pos

      | .mdata _ e =>
          analyzeExprWithPosition config e path pos

      | .proj _ _ e =>
          analyzeExprWithPosition config e path pos

      | _ =>
          -- Literals, bound vars, sorts, etc. - no constants to analyze
          pure ()

    -- Always decrement depth after analysis
    modify fun s => { s with exprDepth := s.exprDepth - 1 }
    return result

  /-- Analyze constant with position tracking -/
  partial def analyzeConstantFlow (config : FlowConfig) (name : Name) (path : List String) (pos : Position) : FlowM Unit := do
    -- Check if already visited in this position
    -- Using (Name × Position) key allows revisiting constants in different positions
    let state ← get
    if state.visited.contains (name, pos) then
      return ()

    -- Check fuel
    if state.visitedCount ≥ config.fuelLimit then
      modify fun s => { s with fuelExhausted := true }
      return ()

    -- Mark as visited in this position
    modify fun s => { s with
      visited := s.visited.insert (name, pos),
      visitedCount := s.visitedCount + 1
    }

    -- Check if this constant is a trigger
    let nameStr := name.toString
    match classifyConstant nameStr with
    | some level =>
        recordFlowTrigger level name (path ++ [nameStr]) pos
    | none => pure ()

    -- Get constant info from environment
    let env ← getEnv
    match env.find? name with
    | none => return ()
    | some info =>
        -- Extract expressions with proper position tracking
        let exprPositions := match info with
          | .axiomInfo ai => [(ai.type, pos)]
          | .defnInfo di => [(di.type, pos), (di.value, pos)]
          | .thmInfo ti =>
              -- When theorem is in Type position (e.g., via Prop→Type elimination),
              -- its proof dependencies affect extraction, so credit to Type.
              -- Otherwise, proof stays in Prop (standard case).
              let proofPos := if pos == Position.type then Position.type else Position.prop
              [(ti.type, pos), (ti.value, proofPos)]
          | .opaqueInfo oi => [(oi.type, pos), (oi.value, pos)]
          | _ => []

        -- Analyze dependencies with expression-level position tracking
        for (expr, exprPos) in exprPositions do
          analyzeExprWithPosition config expr (path ++ [nameStr]) exprPos
end

/-- Analyze declaration with flow tracking -/
def analyzeDeclarationFlow (declName : Name) (config : FlowConfig := {}) : MetaM FlowState := do
  let initialState : FlowState := {}

  -- Determine starting position based on declaration type
  let env ← getEnv
  let startPos ← match env.find? declName with
    | some (.thmInfo ti) =>
        -- Theorem: check if type is Prop (proof-only) or Type (computational)
        -- Only computational theorem types (e.g., proof-relevant data) start in Type
        -- Propositional theorems (standard case) start in Prop to avoid false xBudget
        if ← isProp ti.type then
          pure Position.prop  -- Proof-only theorem, doesn't affect extraction
        else
          pure Position.type  -- Computational theorem type (rare)
    | some (.defnInfo _) =>
        pure Position.type  -- Definitions are always computational
    | _ =>
        pure Position.type  -- Default to Type for axioms, etc.

  let (_, finalState) ← (analyzeConstantFlow config declName [declName.toString] startPos).run initialState
  return finalState

/-- Deduplicate triggers: remove from Prop-only list if they appear in Type-flow.
    Type position is stronger (affects extraction), so it takes precedence. -/
def deduplicateTriggers (state : FlowState) : FlowState :=
  -- Build set of trigger names that appear in Type-flow
  let typeFlowNames := state.typeFlowTriggers.foldl
    (fun acc t => acc.insert t.const)
    (Std.HashSet.emptyWithCapacity 32 : Std.HashSet String)

  -- Filter Prop-only triggers: keep only those NOT in Type-flow
  let dedupedPropOnly := state.propOnlyTriggers.filter
    (fun t => !typeFlowNames.contains t.const)

  { state with propOnlyTriggers := dedupedPropOnly }

/-- Compute xBudget from flow state (only Type-position triggers) -/
def computeXBudget (state : FlowState) : BudgetLevel :=
  if state.typeFlowTriggers.isEmpty then
    .C0  -- No Type-flow triggers, fully extractable
  else
    state.typeFlowTriggers.foldl (fun maxLevel trigger => BudgetLevel.max maxLevel trigger.level) .C0

/-- Compute vBudget from flow state (all triggers, after deduplication) -/
def computeVBudgetFromFlow (state : FlowState) : BudgetLevel :=
  let dedupedState := deduplicateTriggers state
  let allTriggers := dedupedState.typeFlowTriggers ++ dedupedState.propOnlyTriggers
  if allTriggers.isEmpty then
    .C0
  else
    allTriggers.foldl (fun maxLevel trigger => BudgetLevel.max maxLevel trigger.level) .C0

end WBudget
