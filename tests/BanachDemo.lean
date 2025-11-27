import Budgets.BanachExtraction
import Budgets.ConstructiveQ

open Metric

/-!
## Test Cases

We define 6 concrete contraction mappings on ℚ to validate extraction:
1. Linear (K=1/2): f(x) = x/2 + 1, fixed point x* = 2
2. Slow (K=9/10): f(x) = 9x/10 + 1/10, fixed point x* = 1
3. Fast (K=1/10): f(x) = x/10 + 5, fixed point x* = 50/9
4. Piecewise (K=7/10): f(x) = 7x/10 + 3/10
5. Rational (K=3/5): f(x) = 3x/5 + 2
6. Edge (K=99/100): f(x) = 99x/100 + 1/100, fixed point x* = 1
-/

namespace BanachDemo

/-! ### Convergence tolerance for runtime validation -/
def toleranceQ : ℚ := 1 / 1000000  -- 1e-6

/-! ### Test Case 1: Linear (K=1/2) -/
def linear_f : ℚ → ℚ := fun x => x / 2 + 1

theorem linear_lipschitz : ∀ x y : ℚ, dist (linear_f x) (linear_f y) ≤ (1/2 : ℝ) * dist x y := by
  intro x y
  unfold linear_f
  simp only [Rat.dist_eq]
  push_cast
  have h : (↑x : ℝ) / 2 + 1 - (↑y / 2 + 1) = (↑x - ↑y) * (1 / 2) := by ring
  rw [h, abs_mul]
  have : (0 : ℝ) < 1 / 2 := by norm_num
  rw [abs_of_pos this]
  rw [mul_comm]

noncomputable def linear_contraction : ContractionData ℚ := {
  f := linear_f
  K := 1/2
  K_nonneg := by norm_num
  K_lt_one := by norm_num
  lipschitz := linear_lipschitz
}

/-! ### Test Case 2: Slow convergence (K=9/10) -/
def slow_f : ℚ → ℚ := fun x => 9 * x / 10 + 1 / 10

theorem slow_lipschitz : ∀ x y : ℚ, dist (slow_f x) (slow_f y) ≤ (9/10 : ℝ) * dist x y := by
  intro x y
  unfold slow_f
  simp only [Rat.dist_eq]
  push_cast
  have h : 9 * (↑x : ℝ) / 10 + 1 / 10 - (9 * ↑y / 10 + 1 / 10) = (↑x - ↑y) * (9 / 10) := by ring
  rw [h, abs_mul]
  have : (0 : ℝ) < 9 / 10 := by norm_num
  rw [abs_of_pos this]
  rw [mul_comm]

noncomputable def slow_contraction : ContractionData ℚ := {
  f := slow_f
  K := 9/10
  K_nonneg := by norm_num
  K_lt_one := by norm_num
  lipschitz := slow_lipschitz
}

/-! ### Test Case 3: Fast convergence (K=1/10) -/
def fast_f : ℚ → ℚ := fun x => x / 10 + 5

theorem fast_lipschitz : ∀ x y : ℚ, dist (fast_f x) (fast_f y) ≤ (1/10 : ℝ) * dist x y := by
  intro x y
  unfold fast_f
  simp only [Rat.dist_eq]
  push_cast
  have h : (↑x : ℝ) / 10 + 5 - (↑y / 10 + 5) = (↑x - ↑y) * (1 / 10) := by ring
  rw [h, abs_mul]
  have : (0 : ℝ) < 1 / 10 := by norm_num
  rw [abs_of_pos this]
  rw [mul_comm]

noncomputable def fast_contraction : ContractionData ℚ := {
  f := fast_f
  K := 1/10
  K_nonneg := by norm_num
  K_lt_one := by norm_num
  lipschitz := fast_lipschitz
}

/-! ### Test Case 4: Piecewise (K=7/10) -/
def piecewise_f : ℚ → ℚ := fun x => 7 * x / 10 + 3 / 10

theorem piecewise_lipschitz : ∀ x y : ℚ, dist (piecewise_f x) (piecewise_f y) ≤ (7/10 : ℝ) * dist x y := by
  intro x y
  unfold piecewise_f
  simp only [Rat.dist_eq]
  push_cast
  have h : 7 * (↑x : ℝ) / 10 + 3 / 10 - (7 * ↑y / 10 + 3 / 10) = (↑x - ↑y) * (7 / 10) := by ring
  rw [h, abs_mul]
  have : (0 : ℝ) < 7 / 10 := by norm_num
  rw [abs_of_pos this]
  rw [mul_comm]

noncomputable def piecewise_contraction : ContractionData ℚ := {
  f := piecewise_f
  K := 7/10
  K_nonneg := by norm_num
  K_lt_one := by norm_num
  lipschitz := piecewise_lipschitz
}

/-! ### Test Case 5: Rational (K=3/5) -/
def rational_f : ℚ → ℚ := fun x => 3 * x / 5 + 2

theorem rational_lipschitz : ∀ x y : ℚ, dist (rational_f x) (rational_f y) ≤ (3/5 : ℝ) * dist x y := by
  intro x y
  unfold rational_f
  simp only [Rat.dist_eq]
  push_cast
  have h : 3 * (↑x : ℝ) / 5 + 2 - (3 * ↑y / 5 + 2) = (↑x - ↑y) * (3 / 5) := by ring
  rw [h, abs_mul]
  have : (0 : ℝ) < 3 / 5 := by norm_num
  rw [abs_of_pos this]
  rw [mul_comm]

noncomputable def rational_contraction : ContractionData ℚ := {
  f := rational_f
  K := 3/5
  K_nonneg := by norm_num
  K_lt_one := by norm_num
  lipschitz := rational_lipschitz
}

/-! ### Test Case 6: Edge case (K=99/100) -/
def edge_f : ℚ → ℚ := fun x => 99 * x / 100 + 1 / 100

theorem edge_lipschitz : ∀ x y : ℚ, dist (edge_f x) (edge_f y) ≤ (99/100 : ℝ) * dist x y := by
  intro x y
  unfold edge_f
  simp only [Rat.dist_eq]
  push_cast
  have h : 99 * (↑x : ℝ) / 100 + 1 / 100 - (99 * ↑y / 100 + 1 / 100) = (↑x - ↑y) * (99 / 100) := by ring
  rw [h, abs_mul]
  have : (0 : ℝ) < 99 / 100 := by norm_num
  rw [abs_of_pos this]
  rw [mul_comm]

noncomputable def edge_contraction : ContractionData ℚ := {
  f := edge_f
  K := 99/100
  K_nonneg := by norm_num
  K_lt_one := by norm_num
  lipschitz := edge_lipschitz
}

/-! ### Executable runner with convergence validation -/

/-- Computable rational absolute value for convergence checking -/
def abs_rat (x : ℚ) : ℚ := if x < 0 then -x else x

/-- Computable test runner that works with just the function (not the full ContractionData) -/
def run_test (name : String) (f : ℚ → ℚ) (x₀ : ℚ) (n_iters : ℕ) : IO Unit := do
  -- Helper: iterate the function n times (computable!)
  let rec iterate (x : ℚ) : ℕ → ℚ
    | 0 => x
    | n + 1 => f (iterate x n)

  let x_n := iterate x₀ n_iters
  let f_x_n := f x_n

  -- Compute residual directly in ℚ (computable!)
  let residual := abs_rat (x_n - f_x_n)

  -- Check convergence constructively (ℚ has decidable <)
  if residual < toleranceQ then
    IO.println s!"✓ Test: {name}"
    IO.println s!"  Iterations: {n_iters}"
    IO.println s!"  Residual: {residual} (< {toleranceQ})"
    IO.println s!"  Status: CONVERGED (xBudget = C0)"
  else
    IO.println s!"✗ Test: {name}"
    IO.println s!"  Iterations: {n_iters}"
    IO.println s!"  Residual: {residual} (≥ {toleranceQ})"
    IO.println s!"  STATUS: NOT CONVERGED - need more iterations!"
    IO.println s!"  ERROR: Convergence check failed!"

  IO.println ""

end BanachDemo

namespace ConstructiveDemo

open ConstructiveQ

def tolerance : Q := (1 : Q) / (1000000 : Q)

def linear_f : Q → Q := fun x => x / 2 + 1
def slow_f : Q → Q := fun x => (9 : Q) * x / 10 + 1 / 10
def fast_f : Q → Q := fun x => x / 10 + 5
def piecewise_f : Q → Q := fun x => (7 : Q) * x / 10 + 3 / 10
def rational_f : Q → Q := fun x => (3 : Q) * x / 5 + 2
def edge_f : Q → Q := fun x => (99 : Q) * x / 100 + 1 / 100

def abs_q (x : Q) : Q :=
  if x.num ≥ 0 then x else normalize (-x.num) x.den

def run_test (name : String) (f : Q → Q) (x₀ : Q)
    (n_iters : ℕ) : IO Unit := do
  let rec iterate (x : Q) : ℕ → Q
    | 0 => x
    | n + 1 => f (iterate x n)
  let x_n := iterate x₀ n_iters
  let residual := abs_q (x_n - f x_n)
  if residual < tolerance then
    IO.println s!"✓ Test: {name}"
    IO.println s!"  Iterations: {n_iters}"
    IO.println s!"  Residual: {residual} (< {tolerance})"
    IO.println s!"  Status: CONVERGED (ConstructiveQ)"
  else
    IO.println s!"✗ Test: {name}"
    IO.println s!"  Iterations: {n_iters}"
    IO.println s!"  Residual: {residual} (≥ {tolerance})"
    IO.println s!"  STATUS: NOT CONVERGED - need more iterations!"
    IO.println s!"  ERROR: Convergence check failed!"
  IO.println ""

end ConstructiveDemo

/-! ### Main executable -/

def main : IO Unit := do
  IO.println "=== Banach Fixed-Point Extraction Demo ==="
  IO.println "Constructive fixed-point theorem with xBudget = C0"
  IO.println "Running over ConstructiveQ with runtime convergence validation"
  IO.println s!"Convergence tolerance: {ConstructiveDemo.tolerance}"
  IO.println ""
  ConstructiveDemo.run_test "Linear (K=1/2)" ConstructiveDemo.linear_f 0 20
  ConstructiveDemo.run_test "Slow (K=9/10)" ConstructiveDemo.slow_f 0 150
  ConstructiveDemo.run_test "Fast (K=1/10)" ConstructiveDemo.fast_f 0 20
  ConstructiveDemo.run_test "Piecewise (K=7/10)" ConstructiveDemo.piecewise_f 0 50
  ConstructiveDemo.run_test "Rational (K=3/5)" ConstructiveDemo.rational_f 0 35
  ConstructiveDemo.run_test "Edge (K=99/100)" ConstructiveDemo.edge_f 0 1400
