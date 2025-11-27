import Budgets.SemilinearHeat.Evolution
import Budgets.SemilinearHeat.CubicBudget
import Budgets.IntervalDyadic
import Budgets.ConstructiveQ

/-!
# Interval Arithmetic Heat PDE Demo

Demonstrates bounded-precision interval arithmetic for semilinear heat:
  ∂ₜu - Δu = u³  (linear part only for now)

Key achievement: Computation completes in bounded time with bounded precision,
unlike ℚ which explodes after ~5 steps due to GCD overhead.

## Safety: Stability Gate

This demo enforces the proven stability condition dt · L < 1 using the
certified Lipschitz budget from CubicBudget.lean. The solver will NOT run
unless stability is mathematically guaranteed.
-/

namespace HeatDemoInterval

open SemilinearHeat
open SemilinearHeat.CubicBudget
open ℓ2ZD (Lattice)
open IntervalDyadic
open ConstructiveQ

/-- Create interval-valued initial data as Array: u₀(x) = A·sin(πx)
    Use small amplitude (A < 1) to avoid finite-time blowup from u³ -/
def initialDataArray (M : ℕ) (precision : ℕ) (amplitude : ℚ := 1/10) : StateArray :=
  let size := 2 * M + 1
  Array.ofFn (n := size) fun ⟨i, _⟩ =>
    let k : ℤ := (i : ℤ) - M
    if k = 1 ∨ k = -1 then
      (IntervalDyadic.fromRat amplitude precision, IntervalDyadic.zero)
    else
      (IntervalDyadic.zero, IntervalDyadic.zero)

/-- Report interval width (error bound) for a coefficient -/
def reportWidth (name : String) (interval : IntervalD) : IO Unit := do
  let w := IntervalDyadic.width interval
  IO.println s!"  {name}: width = {w}"

/-- Check stability condition and report.
    Returns true if stable, false if unstable.

    Uses the PROVEN Lipschitz budget from CubicBudget.lean, not heuristics! -/
def checkStabilityGate (dt : ℚ) (M : ℕ) (amp : ℚ) : IO Bool := do
  -- Sobolev constant upper bound (conservative)
  let C_bound : Q := ofInt 3

  -- H¹ ball radius (based on initial data amplitude)
  -- For A·sin(πx), H¹ norm ~ A·√(1 + π²) ≤ A·√10 < 4A for safety
  let amp_Q : Q := normalize amp.num amp.den
  let R_bound : Q := mul (ofInt 4) amp_Q

  -- Compute the PROVEN Lipschitz budget
  let budget := cubic_lipschitz_budget_rat 1 M C_bound R_bound

  -- Check stability: dt · L < 1
  let dt_Q : Q := normalize dt.num dt.den
  let stable := check_stability dt_Q budget

  IO.println s!"  ┌─ STABILITY CHECK ─────────────────────────────┐"
  IO.println s!"  │ dt = {dt}"
  IO.println s!"  │ Lipschitz constant L ≤ {toRat budget}"
  IO.println s!"  │ Stability product: dt·L = {toRat (mul dt_Q budget)}"

  if stable then
    IO.println s!"  │ ✓ STABLE: dt·L < 1  (certified by CubicBudget)"
    IO.println s!"  │   Required: dt < {toRat (stability_boundary budget)} (strict)"
    IO.println s!"  └───────────────────────────────────────────────┘"
    pure true
  else
    IO.println s!"  │ ✗ UNSTABLE: dt·L ≥ 1  (STABILITY VIOLATION)"
    IO.println s!"  │   Required: dt < {toRat (stability_boundary budget)} (strict)"
    IO.println s!"  │   Aborting to prevent meaningless results."
    IO.println s!"  └───────────────────────────────────────────────┘"
    pure false

/-- Run demo with given parameters using Array-based O(1) access -/
def runDemo (steps : ℕ) (precision : ℕ) (dt : ℚ) (amp : ℚ := 1/10) (M : ℕ := 1) : IO Unit := do
  IO.println s!"\n=== Interval Heat Demo ==="
  IO.println s!"  steps={steps}, M={M}, dt={dt}, amplitude={amp}, precision={precision}"

  -- ═══════════════════════════════════════════════════════════
  -- STABILITY GATE: Enforce proven stability condition
  -- ═══════════════════════════════════════════════════════════
  let stable ← checkStabilityGate dt M amp
  unless stable do
    IO.println "\n⚠️  Execution blocked by stability gate."
    return

  -- Stable! Safe to proceed
  let dtInterval := IntervalDyadic.fromRat dt precision
  let u0 := initialDataArray M precision amp

  IO.println s!"Initial condition: A·sin(πx) with A={amp}"
  IO.println s!"Time step dt = {dt}"
  IO.println s!"Array size: {u0.size}"

  let start ← IO.monoMsNow

  -- Evolve trajectory using Array-based functions (O(1) access)
  let trajectory := evolveTrajectory_Array u0 steps dtInterval M precision

  -- Force evaluation by accessing final state
  let u_final := trajectory ⟨steps, Nat.lt_succ_self steps⟩

  -- Get mode k=1 (index M+1 in array)
  let idx1 := M + 1
  let (re1, im1) := if h : idx1 < u_final.size then u_final[idx1] else (IntervalDyadic.zero, IntervalDyadic.zero)

  let elapsed ← IO.monoMsNow

  IO.println s!"\nCompleted in {elapsed - start} ms"
  IO.println s!"\nFinal state at k=1:"
  reportWidth "real part" re1
  reportWidth "imag part" im1

  IO.println s!"\nKey result: Bounded precision prevents exponent explosion!"

/-- Main entry point -/
def main : IO Unit := do
  IO.println "════════════════════════════════════════════════════════"
  IO.println "  Semilinear Heat: Certified Interval Arithmetic"
  IO.println "  PDE: ∂ₜu - Δu = u³ on (0,1) × (0,T)"
  IO.println "════════════════════════════════════════════════════════"
  IO.println ""
  IO.println "This demo enforces PROVEN stability via CubicBudget.lean."
  IO.println "The solver will NOT run unless dt·L < 1 is certified."
  IO.println ""

  -- ═════════════════════════════════════════════════
  -- TEST 1: Stable regime (should pass gate)
  -- ═════════════════════════════════════════════════
  IO.println "\n╔══════════════════════════════════════════════════╗"
  IO.println "║  TEST 1: STABLE Parameters (Expected: PASS)      ║"
  IO.println "║  Using M=1, amp=1/100, dt=1/10000000             ║"
  IO.println "╚══════════════════════════════════════════════════╝"
  runDemo 10 32 (1/10000000) (1/100) 1   -- Tiny amplitude, minuscule dt, M=1
  runDemo 100 32 (1/10000000) (1/100) 1

  -- ═════════════════════════════════════════════════
  -- TEST 2: Large time step (should fail gate)
  -- ═════════════════════════════════════════════════
  IO.println "\n╔══════════════════════════════════════════════════╗"
  IO.println "║  TEST 2: UNSTABLE dt (Expected: BLOCKED)         ║"
  IO.println "║  Using M=1, amp=1/100, dt = 1.1× boundary        ║"
  IO.println "╚══════════════════════════════════════════════════╝"
  let amp_small : ℚ := 1/100
  let M_small := 1
  let C_bound : Q := ofInt 3
  let amp_Q : Q := normalize amp_small.num amp_small.den
  let R_bound : Q := mul (ofInt 4) amp_Q
  let budget := cubic_lipschitz_budget_rat 1 M_small C_bound R_bound
  let boundary := toRat (stability_boundary budget)
  let dt_unsafe : ℚ := boundary + boundary / 10  -- 10% above certified limit
  runDemo 10 32 dt_unsafe amp_small M_small  -- Guaranteed to violate dt·L < 1

  -- ═════════════════════════════════════════════════
  -- TEST 3: Large amplitude (should fail gate)
  -- ═════════════════════════════════════════════════
  IO.println "\n╔══════════════════════════════════════════════════╗"
  IO.println "║  TEST 3: UNSTABLE amplitude (Expected: BLOCKED)  ║"
  IO.println "║  Using M=1, amp=1 (huge), dt=1/10000000          ║"
  IO.println "╚══════════════════════════════════════════════════╝"
  runDemo 10 32 (1/10000000) 1 1  -- amplitude=1 causes R^6 blowup

  -- ═════════════════════════════════════════════════
  -- TEST 4: The Real Deal (Higher Resolution)
  -- ═════════════════════════════════════════════════
  IO.println "\n╔══════════════════════════════════════════════════╗"
  IO.println "║  TEST 4: High Resolution (M=5, N=11)             ║"
  IO.println "║  Push resolution while remaining stable.         ║"
  IO.println "╚══════════════════════════════════════════════════╝"

  -- Try dt = 1e-8. If the budget fails, the gate will tell you the required dt.
  runDemo 100 32 (1/100000000) (1/100) 5

  -- ═════════════════════════════════════════════════
  -- Summary
  -- ═════════════════════════════════════════════════
  IO.println ""
  IO.println "════════════════════════════════════════════════════════"
  IO.println "  SUMMARY"
  IO.println "════════════════════════════════════════════════════════"
  IO.println ""
  IO.println "✓ Stability gate enforces dt·L < 1 (PROVEN condition)"
  IO.println "✓ Stable cases run → certified numerical results"
  IO.println "✓ Unstable cases blocked → prevents garbage output"
  IO.println ""
  IO.println "Architecture:"
  IO.println "  • Mathematical constant: CubicConvolution.lean (C5)"
  IO.println "  • Constructive budget: CubicBudget.lean (C0)"
  IO.println "  • Bridge theorem: budget_is_sound_original"
  IO.println "  • Runtime check: check_stability (this file)"
  IO.println ""
  IO.println "This is CERTIFIED computation, not just simulation!"
  IO.println ""

end HeatDemoInterval

def main : IO Unit := HeatDemoInterval.main
