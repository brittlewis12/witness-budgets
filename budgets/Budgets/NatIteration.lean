import Budgets.BanachExtraction
import WBudget.WBudget

/-!
# Nat Iteration - True C0 Budget Propagation Demo

Demonstrates budget propagation with genuinely constructive types.

Unlike LinearRecurrence.lean (which hits C5 due to mathlib's ℚ using classical proofs),
this module uses Nat arithmetic to show true C0 extraction budgets.

Pattern: Simple iterative computation over Nat using the same structure as
BanachExtraction's iterate_n_times.
-/

/-! ## Simple Nat Recurrence

Given a function f : Nat → Nat, iterate it N times from an initial value.
This mirrors solve_linear_recurrence but over a truly constructive type.
-/

/-- Iterate a Nat → Nat function N times (computable!) -/
def iterate_nat_function (f : Nat → Nat) (x₀ : Nat) (N : Nat) : Nat :=
  let rec iterate (x : Nat) : Nat → Nat
    | 0 => x
    | n + 1 => f (iterate x n)
  iterate x₀ N

/-! ## Example: Halving Recurrence

x_{n+1} = x_n / 2 + 1
Converges to small values (2 or 1 for most inputs).
-/

def halving_step (x : Nat) : Nat := x / 2 + 1

/-- Run halving recurrence for N iterations -/
def halving_recurrence (x₀ : Nat) (N : Nat) : Nat :=
  iterate_nat_function halving_step x₀ N

/-! ## Convergence Checking

Check if iteration has stabilized (reached a fixed point).
-/

def is_fixed_point (f : Nat → Nat) (x : Nat) : Bool :=
  f x == x

/-- Check if halving recurrence has converged after N iterations -/
def check_halving_converged (x₀ : Nat) (N : Nat) : Bool :=
  let x_N := halving_recurrence x₀ N
  is_fixed_point halving_step x_N

/-! ## Examples -/

#eval halving_recurrence 100 20
-- Should converge to 1 or 2

#eval check_halving_converged 100 20
-- Should be true (converged)

#eval halving_recurrence 1000 30
-- Larger input, more iterations

/-!
## Budget Verification

Expected budgets (to be verified with baseline_module.sh):
- iterate_nat_function: vBudget=C0, xBudget=C0 (pure Nat iteration)
- halving_recurrence: vBudget=C0, xBudget=C0 (calls iterate_nat_function)
- check_halving_converged: vBudget=C0, xBudget=C0 (decidable equality on Nat)
- is_fixed_point: vBudget=C0, xBudget=C0 (Nat equality)

This demonstrates TRUE budget propagation: using C0 components yields C0 downstream code.
Compare with LinearRecurrence.lean which hits C5 due to mathlib's ℚ implementation.
-/
