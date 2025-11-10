import Budgets.BanachExtraction
import WBudget.WBudget

/-!
# Linear Recurrence via Constructive Banach - Budget Propagation Demo

Demonstrates:
1. Using the computable iteration pattern from BanachExtraction
2. Budget propagation: downstream computation stays C0
3. Practical composition: build on constructive witness

Linear recurrence: x_{n+1} = a·x_n + b where |a| < 1
Fixed point: x* = b/(1-a)
-/

open Metric

/-! Linear recurrence data over ℚ -/
structure LinearRecurrenceQ where
  a : ℚ
  b : ℚ
  a_abs_lt_one : |(a : ℝ)| < 1

/-- The recurrence map f(x) = a·x + b -/
def recurrence_map_q (lr : LinearRecurrenceQ) : ℚ → ℚ :=
  fun x => lr.a * x + lr.b

/-! Lipschitz proof for verification -/
theorem recurrence_lipschitz_q (lr : LinearRecurrenceQ) :
    ∀ x y : ℚ, dist (recurrence_map_q lr x) (recurrence_map_q lr y) ≤ |(lr.a : ℝ)| * dist x y := by
  intro x y
  unfold recurrence_map_q
  simp only [Rat.dist_eq]
  push_cast
  rw [show (lr.a : ℝ) * ↑x + ↑lr.b - ((lr.a : ℝ) * ↑y + ↑lr.b) = (lr.a : ℝ) * (↑x - ↑y) by ring, abs_mul]

/-! ContractionData for verification (noncomputable) -/
noncomputable def to_contraction_q (lr : LinearRecurrenceQ) : ContractionData ℚ := {
  f := recurrence_map_q lr
  K := |(lr.a : ℝ)|
  K_nonneg := abs_nonneg _
  K_lt_one := lr.a_abs_lt_one
  lipschitz := recurrence_lipschitz_q lr
}

/-!
## Computable solver using iteration pattern from BanachExtraction

This uses the same computable iteration pattern as iterate_n_times,
but works directly with the function (not the noncomputable ContractionData).

KEY: This demonstrates the C0 extraction pattern - iterate the function N times.
-/

/-- Solve linear recurrence by iterating N times (computable!) -/
def solve_linear_recurrence (lr : LinearRecurrenceQ) (x₀ : ℚ) (N : ℕ) : ℚ :=
  let rec iterate (x : ℚ) : ℕ → ℚ
    | 0 => x
    | n + 1 => recurrence_map_q lr (iterate x n)
  iterate x₀ N

/-! Computable convergence checker -/
def abs_q (x : ℚ) : ℚ := if x < 0 then -x else x

/-- Check if iteration has converged (computable!) -/
def check_converged (lr : LinearRecurrenceQ) (x₀ : ℚ) (N : ℕ) (tol : ℚ) : Bool :=
  let x_N := solve_linear_recurrence lr x₀ N
  let residual := abs_q (x_N - recurrence_map_q lr x_N)
  residual < tol

/-! Example: x_{n+1} = (1/2)x_n + 1, fixed point x* = 2 -/
def example_recurrence : LinearRecurrenceQ where
  a := 1/2
  b := 1
  a_abs_lt_one := by norm_num

#eval solve_linear_recurrence example_recurrence 0 20
-- Should output approximately 2

#eval check_converged example_recurrence 0 20 (1/1000000)
-- Should output true

/-!
## Budget Verification

Expected budgets (run baseline_module.sh to verify):
- solve_linear_recurrence: vBudget=C0, xBudget=C0 (pure iteration, computable)
- check_converged: vBudget=C0, xBudget=C0 (decidable comparison on ℚ)
- to_contraction_q: vBudget=C5, xBudget=C5 (contains proofs)

This demonstrates budget propagation: using the C0 iteration pattern
from BanachExtraction yields C0 downstream code.
-/
