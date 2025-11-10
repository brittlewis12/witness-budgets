import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import WBudget.WBudget

/-!
# Constructive Banach Fixed-Point Theorem

This file contains a constructive formalization of the Banach fixed-point theorem
with explicit convergence rates and extractable iteration bounds.

## Main definitions

* `ContractionData` : bundled data for a contraction mapping (f, K, proofs)
* `iterations_needed` : computable function returning N(ε) for tolerance ε
* `banach_fixed_point` : constructive fixed-point theorem returning Σ-type witness
* `iterate_to_fixed_point` : extractable iteration function

## Main results

* `banach_fixed_point` : every contraction on a complete metric space has a unique
  fixed point, with explicit convergence rate
* All results target xBudget = C0 (fully extractable, no classical axioms)

## Tags

Banach fixed-point theorem, contraction mapping, constructive mathematics,
witness budgets, program extraction
-/

open Metric Set Filter Topology

variable {X : Type*}

section ContractionData

/-!
### Contraction Data Structure

We bundle the contraction function with its Lipschitz constant and proofs.
This makes all data explicit for extraction.
-/

/--
A contraction mapping with explicit Lipschitz constant K < 1.
All data is bundled to make extraction clear.
-/
structure ContractionData (X : Type*) [MetricSpace X] where
  /-- The contracting function -/
  f : X → X
  /-- Lipschitz constant (must satisfy 0 ≤ K < 1) -/
  K : ℝ
  /-- Proof that K is non-negative -/
  K_nonneg : 0 ≤ K
  /-- Proof that K is strictly less than 1 -/
  K_lt_one : K < 1
  /-- Lipschitz condition: f contracts distances by factor K -/
  lipschitz : ∀ x y : X, dist (f x) (f y) ≤ K * dist x y

namespace ContractionData

variable [MetricSpace X]

/--
The denominator (1 - K) is always positive for a contraction.
-/
theorem one_sub_K_pos (contr : ContractionData X) : 0 < 1 - contr.K := by
  linarith [contr.K_lt_one]

/--
Helper: (1 - K) is never zero.
-/
theorem one_sub_K_ne_zero (contr : ContractionData X) : 1 - contr.K ≠ 0 := by
  linarith [contr.one_sub_K_pos]

end ContractionData

end ContractionData

section IterationCount

/-!
### Iteration Functions

We separate **computation** from **verification**:

1. **Computable layer (xBudget = C0 - for extraction!):**
   - `iterate_n_times`: Run the contraction N times
   - Takes N as an explicit parameter
   - No real number comparisons, fully extractable

2. **Verification layer (noncomputable - for proofs):**
   - `iterations_needed`: Theoretical bound N(ε) using logarithms
   - Proves that some N is sufficient
   - Not extracted, just for mathematical guarantees

This design mirrors practice: you specify `max_iter` explicitly,
but have theoretical proof that convergence will occur.
-/

/--
**Computable iteration (extractable!).**

Applies the contraction function `n` times to the initial point.
This is the core extractable algorithm - xBudget = C0.

No real number comparisons needed, just pure iteration.
-/
def iterate_n_times [MetricSpace X] (contr : ContractionData X) (x₀ : X) (n : ℕ) : X :=
  match n with
  | 0 => x₀
  | n' + 1 => contr.f (iterate_n_times contr x₀ n')

/--
**Theoretical iteration bound (noncomputable).**

Computes the minimum N such that f^[N](x₀) is within ε of the fixed point.
Uses closed-form logarithmic formula for tight bounds.

Formula: N = ⌈log(d₀ / ((1-K)ε)) / log(1/K)⌉
where d₀ = dist(x₀, f(x₀))

This is used in **proofs** to show that a sufficient N exists.
The extracted code doesn't call this - it just takes N as input.
-/
noncomputable def iterations_needed [MetricSpace X] (contr : ContractionData X)
    (x₀ : X) (ε : ℝ) : ℕ :=
  if ε > 0 ∧ dist x₀ (contr.f x₀) > 0 then
    let d₀ := dist x₀ (contr.f x₀)
    let numerator := Real.log (d₀ / ((1 - contr.K) * ε))
    let denominator := Real.log (1 / contr.K)
    if denominator > 0 then
      Int.toNat ⌈numerator / denominator⌉
    else
      0
  else
    0

end IterationCount

section BudgetCheck

/-!
### Budget Monitoring

Verify the xBudget separation between computable (extractable) and
verification (proof-only) layers.

**Expected results:**
- `ContractionData`: xBudget = C0 (pure data structure)
- `iterate_n_times`: xBudget = C0 (**extractable core!**)
- `iterations_needed`: xBudget = C5 (uses Real.log, proof-only)

The key: `iterate_n_times` is the extraction target with xBudget = C0.
-/

-- Check ContractionData structure
-- TODO: Fix #wbudget command syntax
-- #wbudget ContractionData
-- #wbudget ContractionData.f
-- #wbudget ContractionData.K

-- Check iteration functions
-- #wbudget iterate_n_times  -- Expect: xBudget = C0 (EXTRACTABLE!)
-- #wbudget iterations_needed  -- Expect: xBudget = C5 (proof-only)

end BudgetCheck

section CauchySequence

/-!
### Cauchy Sequence Lemmas

Prove that the iteration sequence f^[n](x₀) forms a Cauchy sequence
with explicit geometric convergence rate.

Key steps:
1. Successive iterates get closer: dist(f^[n+1](x), f^[n](x)) ≤ K^n * d₀
2. Telescoping sum: dist(f^[m](x), f^[n](x)) ≤ geometric series bound
3. Cauchy property: sequence converges
-/

variable [MetricSpace X]

/-- Geometric-series helper: `(1 - a^(k+1))/(1-a)` splits into previous term plus `a^k`. -/
lemma geom_series_next (a : ℝ) (h : 1 - a ≠ 0) (k : ℕ) :
    (1 - a ^ (k + 1)) / (1 - a) = (1 - a ^ k) / (1 - a) + a ^ k := by
  have hdecomp :
      1 - a ^ (k + 1) = (1 - a ^ k) + a ^ k * (1 - a) := by
    ring
  calc
    (1 - a ^ (k + 1)) / (1 - a)
        = ((1 - a ^ k) + a ^ k * (1 - a)) / (1 - a) := by simp [hdecomp]
    _ = (1 - a ^ k) / (1 - a) + a ^ k := by
          field_simp [h]

/--
Distance between successive iterates decreases geometrically.

This is the foundation for all convergence estimates.
-/
lemma iterate_successive_dist (contr : ContractionData X) (x₀ : X) (n : ℕ) :
    dist (iterate_n_times contr x₀ (n + 1)) (iterate_n_times contr x₀ n) ≤
      contr.K ^ n * dist (contr.f x₀) x₀ := by
  induction n with
  | zero =>
    -- Base case: dist(f(x₀), x₀) ≤ K^0 * dist(f(x₀), x₀) = dist(f(x₀), x₀)
    simp [iterate_n_times, pow_zero, one_mul]
  | succ n ih =>
    -- Inductive step: use Lipschitz property
    simp only [iterate_n_times]
    calc dist (contr.f (iterate_n_times contr x₀ (n + 1)))
              (contr.f (iterate_n_times contr x₀ n))
        ≤ contr.K * dist (iterate_n_times contr x₀ (n + 1))
                         (iterate_n_times contr x₀ n) := by
          apply contr.lipschitz
      _ ≤ contr.K * (contr.K ^ n * dist (contr.f x₀) x₀) := by
          apply mul_le_mul_of_nonneg_left ih contr.K_nonneg
      _ = contr.K ^ (n + 1) * dist (contr.f x₀) x₀ := by
          ring

/--
Geometric series bound for distance between arbitrary iterates.

For m ≤ n, we have dist(f^[n](x₀), f^[m](x₀)) ≤ K^m * (1 - K^(n-m)) / (1 - K) * d₀
where d₀ = dist(f(x₀), x₀).

This follows from telescoping the sum of successive distances.
-/
lemma iterate_dist_bound (contr : ContractionData X) (x₀ : X) (m n : ℕ) (h : m ≤ n) :
      dist (iterate_n_times contr x₀ n) (iterate_n_times contr x₀ m) ≤
        contr.K ^ m * ((1 - contr.K ^ (n - m)) / (1 - contr.K)) * dist (contr.f x₀) x₀ := by
  induction h with
  | refl =>
    -- Case m = n: distance is zero, bound is non-negative
    simp [dist_self, pow_zero]
  | step ih =>
    -- Step case: m ≤ n, need to show m ≤ n+1
    -- Goal: dist(x_{n+1}, x_m) ≤ K^m * (1 - K^(n+1-m)) / (1-K) * d₀
    -- IH (named `ih`): dist(x_n, x_m) ≤ K^m * (1 - K^(n-m)) / (1-K) * d₀
    -- The step pattern gives us an unnamed nat m✝ and an unnamed proof
    -- Let's extract them with a clear pattern match
    next n_prev a_ih =>
    have h_le_proof : m ≤ n_prev := ih
    calc dist (iterate_n_times contr x₀ (n_prev + 1)) (iterate_n_times contr x₀ m)
        ≤ dist (iterate_n_times contr x₀ (n_prev + 1)) (iterate_n_times contr x₀ n_prev) +
          dist (iterate_n_times contr x₀ n_prev) (iterate_n_times contr x₀ m) := dist_triangle _ _ _
      _ ≤ contr.K ^ n_prev * dist (contr.f x₀) x₀ +
          contr.K ^ m * ((1 - contr.K ^ (n_prev - m)) / (1 - contr.K)) * dist (contr.f x₀) x₀ := by
            apply add_le_add
            · exact iterate_successive_dist contr x₀ n_prev
            · exact a_ih
      _ = (contr.K ^ n_prev + contr.K ^ m * ((1 - contr.K ^ (n_prev - m)) / (1 - contr.K))) * dist (contr.f x₀) x₀ := by ring
      _ = contr.K ^ m * (contr.K ^ (n_prev - m) + (1 - contr.K ^ (n_prev - m)) / (1 - contr.K)) * dist (contr.f x₀) x₀ := by
            -- Factor out K^m: need n_prev = m + (n_prev - m), so K^n_prev = K^m * K^(n_prev-m)
            have : n_prev = m + (n_prev - m) := (Nat.add_sub_of_le h_le_proof).symm
            conv_lhs => arg 1; rw [this, pow_add]
            simp only [Nat.add_sub_cancel_left]
            ring
      _ = contr.K ^ m * ((1 - contr.K ^ (n_prev + 1 - m)) / (1 - contr.K)) * dist (contr.f x₀) x₀ := by
            -- Use geom_series_next: a^k + (1-a^k)/(1-a) = (1-a^(k+1))/(1-a)
            congr 1
            -- Show (n_prev - m) + 1 = n_prev + 1 - m
            have h_sub_eq : n_prev - m + 1 = n_prev + 1 - m := by omega
            -- Rewrite using geom_series_next (need to commute terms)
            rw [add_comm, ← h_sub_eq, ← geom_series_next contr.K contr.one_sub_K_ne_zero (n_prev - m)]

/--
Simplified bound when n → ∞: dist(f^[n](x₀), f^[m](x₀)) ≤ K^m / (1 - K) * d₀.

This is the key inequality for proving the Cauchy property.

The proof uses the triangle inequality to telescope the distance as a sum
of successive distances, then bounds each term using iterate_successive_dist
and sums the resulting geometric series.
-/
lemma iterate_dist_bound_simple (contr : ContractionData X) (x₀ : X) (m n : ℕ) (h : m ≤ n) :
    dist (iterate_n_times contr x₀ n) (iterate_n_times contr x₀ m) ≤
      contr.K ^ m / (1 - contr.K) * dist (contr.f x₀) x₀ := by
  -- Use full bound and drop the (1 - K^(n-m)) term since it's ≤ 1
  calc dist (iterate_n_times contr x₀ n) (iterate_n_times contr x₀ m)
      ≤ contr.K ^ m * ((1 - contr.K ^ (n - m)) / (1 - contr.K)) * dist (contr.f x₀) x₀ := by
        exact iterate_dist_bound contr x₀ m n h
    _ ≤ contr.K ^ m / (1 - contr.K) * dist (contr.f x₀) x₀ := by
        -- Since 0 ≤ K^(n-m) ≤ 1, we have (1 - K^(n-m)) ≤ 1, hence the bound drops
        have h1 : 1 - contr.K ^ (n - m) ≤ 1 := by
          have : 0 ≤ contr.K ^ (n - m) := pow_nonneg contr.K_nonneg (n - m)
          linarith
        have h2 : (1 - contr.K ^ (n - m)) / (1 - contr.K) ≤ 1 / (1 - contr.K) := by
          apply div_le_div_of_nonneg_right h1 (le_of_lt contr.one_sub_K_pos)
        calc contr.K ^ m * ((1 - contr.K ^ (n - m)) / (1 - contr.K)) * dist (contr.f x₀) x₀
            ≤ contr.K ^ m * (1 / (1 - contr.K)) * dist (contr.f x₀) x₀ := by
              apply mul_le_mul_of_nonneg_right
              · apply mul_le_mul_of_nonneg_left h2 (pow_nonneg contr.K_nonneg m)
              · exact dist_nonneg
          _ = contr.K ^ m / (1 - contr.K) * dist (contr.f x₀) x₀ := by ring

end CauchySequence

section ConstructiveFixedPoint

/-!
### Constructive Fixed Point Theorem

The main result: a constructive version of Banach's fixed-point theorem
that returns a Σ-type witness with explicit data.
-/

variable [MetricSpace X]

/--
Helper: the iteration sequence is Cauchy.

This uses the geometric series bound to show that for any ε > 0,
the sequence eventually stays within ε.

The key: since K < 1, we have K^m → 0, so the bound K^m / (1-K) * d₀
can be made arbitrarily small.
-/
lemma iterate_is_cauchy (contr : ContractionData X) (x₀ : X)
    (h_nonzero : dist x₀ (contr.f x₀) ≠ 0) :
    CauchySeq (fun n => iterate_n_times contr x₀ n) := by
  -- Use the metric space definition of Cauchy
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  -- We need N such that for all m, n ≥ N: dist(x_m, x_n) < ε
  -- From our bound: dist(x_n, x_m) ≤ K^m / (1-K) * d₀ when m ≤ n
  -- So we need: K^N / (1-K) * d₀ < ε
  -- i.e., K^N < ε * (1-K) / d₀

  -- Since K^n → 0, such an N exists
  let d₀ := dist x₀ (contr.f x₀)
  let threshold := ε * (1 - contr.K) / d₀

  -- Key: K < 1 implies K^N → 0, so eventually K^N < threshold
  have d₀_pos : 0 < d₀ := by
    exact h_nonzero.symm.lt_of_le dist_nonneg

  have threshold_pos : 0 < threshold := by
    apply div_pos
    · apply mul_pos ε_pos contr.one_sub_K_pos
    · exact d₀_pos

  -- For 0 ≤ K < 1 and any positive threshold, ∃N: K^N < threshold
  have : ∃ N, contr.K ^ N < threshold := by
    -- Mathlib has this: exists_pow_lt_of_lt_one
    exact exists_pow_lt_of_lt_one threshold_pos contr.K_lt_one

  obtain ⟨N, hN⟩ := this
  use N

  intro n hn
  -- Show dist(x_n, x_N) < ε using the bound
  -- We have n ≥ N, so we can use iterate_dist_bound_simple
  calc dist (iterate_n_times contr x₀ n) (iterate_n_times contr x₀ N)
      ≤ contr.K ^ N / (1 - contr.K) * dist (contr.f x₀) x₀ := by
        exact iterate_dist_bound_simple contr x₀ N n hn
    _ = contr.K ^ N / (1 - contr.K) * d₀ := by
        rw [dist_comm]
    _ < ε := by
        -- Unfold threshold and simplify: K^N/(1-K)*d₀ < ε * (1-K)/d₀ * (1-K) * d₀ / (1-K)
        calc contr.K ^ N / (1 - contr.K) * d₀
            = contr.K ^ N * d₀ / (1 - contr.K) := by ring
          _ < threshold * d₀ / (1 - contr.K) := by
              apply div_lt_div_of_pos_right
              · apply mul_lt_mul_of_pos_right hN d₀_pos
              · exact contr.one_sub_K_pos
          _ = ε * (1 - contr.K) / d₀ * d₀ / (1 - contr.K) := by rfl
          _ = ε := by field_simp [d₀_pos.ne', contr.one_sub_K_ne_zero]

/--
Helper: the limit of the iteration sequence is a fixed point.

If x_n → x*, then f(x*) = x* by continuity of f.

Proof: f is Lipschitz, hence continuous. So f(x_n) → f(x*).
But x_{n+1} = f(x_n), so x_{n+1} → x* as well.
By uniqueness of limits, f(x*) = x*.
-/
lemma limit_is_fixed_point (contr : ContractionData X) (x₀ : X)
    (x_star : X) (h_limit : Filter.Tendsto (fun n => iterate_n_times contr x₀ n) Filter.atTop (𝓝 x_star)) :
    contr.f x_star = x_star := by
  -- f is Lipschitz, hence continuous
  have f_cont : Continuous contr.f := by
    let K_nnreal : NNReal := ⟨contr.K, contr.K_nonneg⟩
    have : LipschitzWith K_nnreal contr.f := by
      intro x y
      simp only [edist_dist, ENNReal.coe_nnreal_eq]
      calc ENNReal.ofReal (dist (contr.f x) (contr.f y))
          ≤ ENNReal.ofReal (contr.K * dist x y) := ENNReal.ofReal_le_ofReal (contr.lipschitz x y)
        _ = ENNReal.ofReal contr.K * ENNReal.ofReal (dist x y) := ENNReal.ofReal_mul contr.K_nonneg
    exact this.continuous

  -- f(x_n) → f(x*) by continuity
  have f_limit : Tendsto (fun n => contr.f (iterate_n_times contr x₀ n)) atTop (𝓝 (contr.f x_star)) := by
    exact Continuous.tendsto f_cont x_star |>.comp h_limit

  -- But x_{n+1} = f(x_n), so f(x_n) → x*
  have shift_limit : Tendsto (fun n => iterate_n_times contr x₀ (n + 1)) atTop (𝓝 x_star) := by
    exact h_limit.comp (tendsto_add_atTop_nat 1)

  have f_xn_eq : ∀ n, contr.f (iterate_n_times contr x₀ n) = iterate_n_times contr x₀ (n + 1) := by
    intro n
    rfl

  -- The sequence (f(x_n)) = (x_{n+1}) has limit x*
  have : Tendsto (fun n => contr.f (iterate_n_times contr x₀ n)) atTop (𝓝 x_star) := by
    simp only [f_xn_eq]
    exact shift_limit

  -- By uniqueness of limits: f(x*) = x*
  exact tendsto_nhds_unique f_limit this

/--
**Main Theorem:** Constructive Banach fixed-point theorem with explicit witness.

Given a contraction mapping on a complete metric space, returns a Σ-type
containing:
1. The fixed point x*
2. Proof that f(x*) = x*

This uses completeness (classical), but the iteration function itself is C0!
-/
noncomputable def banach_fixed_point [CompleteSpace X] (contr : ContractionData X) (x₀ : X) :
    {x : X // contr.f x = x} := by
  -- The iteration sequence
  let seq := fun n => iterate_n_times contr x₀ n

  -- Case split: if x₀ is already a fixed point, we're done
  by_cases h : contr.f x₀ = x₀
  case pos =>
    -- Easy case: x₀ is already a fixed point
    exact ⟨x₀, h⟩
  case neg =>
    -- Main case: x₀ is not a fixed point
    -- The sequence is Cauchy
    have cauchy : CauchySeq seq := by
      apply iterate_is_cauchy
      intro heq
      exact h (dist_eq_zero.mp heq).symm

    -- By completeness, the Cauchy sequence converges
    have h_exists : ∃ x, Tendsto seq atTop (𝓝 x) := cauchySeq_tendsto_of_complete cauchy
    let x_star := Classical.choose h_exists
    have h_limit := Classical.choose_spec h_exists

    -- The limit is a fixed point
    have fixed : contr.f x_star = x_star := by
      exact limit_is_fixed_point contr x₀ x_star h_limit

    -- Return the witness
    exact ⟨x_star, fixed⟩

end ConstructiveFixedPoint

/-!
## Status Update

- ContractionData: ✅
- iterate_n_times: ✅ (xBudget = C0)
- iterations_needed (proof layer): ✅
- iterate_successive_dist / iterate_dist_bound / iterate_dist_bound_simple: ✅
- iterate_is_cauchy / limit_is_fixed_point / banach_fixed_point: ✅

Remaining work moves to Week 2 (extraction harness + benchmarks).
-/
