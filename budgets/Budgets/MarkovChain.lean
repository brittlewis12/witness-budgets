import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Budgets.BanachExtraction

/-!
# Markov Chain Convergence Demo

Demonstrates contraction mapping for a concrete 3-state Markov chain.
This is Demo 2 in the "Banach → Newton → Markov" sequence.

## The Chain

Symmetric random walk on triangle:
- State space: {0, 1, 2}
- From each state: stay with prob 1/4, move to each neighbor with prob 3/8

Transition matrix P:
```
     0     1     2
0  [1/4   3/8   3/8]
1  [3/8   1/4   3/8]
2  [3/8   3/8   1/4]
```

## Key Results

- Stationary distribution: π = (1/3, 1/3, 1/3) (uniform)
- Eigenvalues: λ₁ = 1, λ₂ = λ₃ = -1/8
- Contraction constant: K = 1/8
- Convergence: ‖Pⁿμ - π‖ ≤ (1/8)ⁿ ‖μ - π‖

## Architecture

This file provides the formal verification layer (noncomputable ℝ proofs).
Runtime extraction uses ConstructiveQ in tests/MarkovDemo.lean.
-/

namespace MarkovChain

noncomputable section

open Matrix Finset
open scoped Matrix

-- State space: vertices of triangle
abbrev S : Type := Fin 3

instance : Fintype S := inferInstance
instance : DecidableEq S := inferInstance

-- Transition matrix (symmetric random walk on triangle)
def P : Matrix (Fin 3) (Fin 3) ℝ := !![
  1/4, 3/8, 3/8;
  3/8, 1/4, 3/8;
  3/8, 3/8, 1/4
]

-- Probability distribution type (non-negative, sums to 1)
-- Simplified to use ℝ directly with non-negativity constraints
def Distribution :=
  { μ : Fin 3 → ℝ // (∀ i, 0 ≤ μ i) ∧ (univ.sum μ = 1) }

-- L1 distance (total variation distance, scaled by 1/2)
def l1_dist {n : ℕ} (μ ν : Fin n → ℝ) : ℝ :=
  univ.sum (fun i => |μ i - ν i|)

-- Stationary distribution (uniform for symmetric chain)
def π : Distribution :=
  ⟨fun _ => 1/3,
   by
     constructor
     · intro i; norm_num
     · simp only [sum_const, card_univ, Fintype.card_fin]; norm_num⟩

-- Action of transition matrix on distributions
def apply_P (μ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j => univ.sum (fun i => P j i * μ i)

/-! ## Basic Properties -/

-- Each row of P sums to 1 (stochastic property)
lemma P_stochastic (i : Fin 3) : univ.sum (fun j => P i j) = 1 := by
  fin_cases i
  · -- i = 0
    simp [P, Fin.sum_univ_three]
    norm_num
  · -- i = 1
    simp [P, Fin.sum_univ_three]
    norm_num
  · -- i = 2
    simp [P, Fin.sum_univ_three]
    norm_num

-- All entries of P are non-negative
lemma P_nonneg (i j : Fin 3) : 0 ≤ P i j := by
  fin_cases i <;> fin_cases j <;> { simp [P]; try norm_num }

-- P is symmetric
lemma P_symmetric (i j : Fin 3) : P i j = P j i := by
  fin_cases i <;> fin_cases j <;> rfl

-- π is stationary: P π = π
lemma stationary_distribution : apply_P π.val = π.val := by
  ext j
  simp only [apply_P, π]
  fin_cases j
  · -- j = 0
    simp [P, Fin.sum_univ_three]
    norm_num
  · -- j = 1
    simp [P, Fin.sum_univ_three]
    norm_num
  · -- j = 2
    simp [P, Fin.sum_univ_three]
    norm_num

/-! ## Eigenvector Analysis -/

-- Eigenvector for eigenvalue 1 (stationary)
def v₁ : Fin 3 → ℝ := ![1, 1, 1]

-- Eigenvector for eigenvalue -1/8
def v₂ : Fin 3 → ℝ := ![1, -1, 0]

-- Another eigenvector for eigenvalue -1/8
def v₃ : Fin 3 → ℝ := ![1, 1, -2]

-- Matrix-vector multiplication
def mulVec (A : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => univ.sum (fun j => A i j * v j)

-- Verify v₁ is eigenvector with eigenvalue 1
lemma eigen_v₁ : mulVec P v₁ = v₁ := by
  ext i
  simp only [mulVec, v₁, P]
  fin_cases i
  · -- i = 0
    simp [Fin.sum_univ_three]
    norm_num
  · -- i = 1
    simp [Fin.sum_univ_three]
    norm_num
  · -- i = 2
    simp [Fin.sum_univ_three]
    norm_num

-- Verify v₂ is eigenvector with eigenvalue -1/8
lemma eigen_v₂ : mulVec P v₂ = fun i => (-1/8 : ℝ) * v₂ i := by
  ext i
  simp only [mulVec, v₂, P]
  fin_cases i
  · -- i = 0
    simp [Fin.sum_univ_three]; norm_num
  · -- i = 1
    simp [Fin.sum_univ_three]; norm_num
  · -- i = 2
    simp [Fin.sum_univ_three]

-- Verify v₃ is eigenvector with eigenvalue -1/8
lemma eigen_v₃ : mulVec P v₃ = fun i => (-1/8 : ℝ) * v₃ i := by
  ext i
  simp only [mulVec, v₃, P]
  fin_cases i
  · -- i = 0
    simp [Fin.sum_univ_three]; norm_num
  · -- i = 1
    simp [Fin.sum_univ_three]; norm_num
  · -- i = 2
    simp [Fin.sum_univ_three]; norm_num

/-! ## Orthogonality -/

-- Inner product for Fin 3 → ℝ
def inner (u v : Fin 3 → ℝ) : ℝ :=
  univ.sum (fun i => u i * v i)

-- v₁, v₂, v₃ are pairwise orthogonal
lemma orthogonal_v₁_v₂ : inner v₁ v₂ = 0 := by
  simp only [inner, v₁, v₂, Fin.sum_univ_three, cons_val_zero, cons_val_one, cons_val_two]
  norm_num

lemma orthogonal_v₁_v₃ : inner v₁ v₃ = 0 := by
  simp only [inner, v₁, v₃, Fin.sum_univ_three, cons_val_zero, cons_val_one, cons_val_two]
  norm_num

lemma orthogonal_v₂_v₃ : inner v₂ v₃ = 0 := by
  simp only [inner, v₂, v₃, Fin.sum_univ_three, cons_val_zero, cons_val_one, cons_val_two]
  norm_num

/-! ## Contraction Proof -/

-- Key insight: P acts as P w = 3/8 (sum w) v₁ - 1/8 w
-- For vectors with sum 0, this gives P w = -1/8 w, yielding exact 1/8 contraction

-- Formula for P action on any vector
lemma apply_P_formula (w : Fin 3 → ℝ) (j : Fin 3) :
    apply_P w j = 3/8 * univ.sum w - 1/8 * w j := by
  simp only [apply_P, P]
  fin_cases j
  · -- j = 0
    simp [Fin.sum_univ_three]
    ring
  · -- j = 1
    simp [Fin.sum_univ_three]
    ring
  · -- j = 2
    simp [Fin.sum_univ_three]
    ring

-- For vectors with sum 0, P scales by -1/8
lemma apply_P_sum_zero (w : Fin 3 → ℝ) (h : univ.sum w = 0) :
    apply_P w = fun j => -1/8 * w j := by
  ext j
  rw [apply_P_formula, h]
  ring

-- L1 norm of scaled vector
lemma l1_dist_scale_self (w : Fin 3 → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    l1_dist (fun i => c * w i) (fun _ => 0) = c * l1_dist w (fun _ => 0) := by
  simp only [l1_dist, sub_zero]
  have : ∑ i : Fin 3, |c * w i| = c * ∑ i : Fin 3, |w i| := by
    simp_rw [abs_mul, abs_of_nonneg hc, Finset.mul_sum]
  exact this

lemma l1_dist_self_zero (w : Fin 3 → ℝ) :
    l1_dist w (fun _ => 0) = univ.sum (fun i => |w i|) := by
  simp only [l1_dist, sub_zero]

-- Main helper: L1 norm contracts by exactly 1/8 for sum-0 vectors
lemma sum_zero_contraction (w : Fin 3 → ℝ) (h : univ.sum w = 0) :
    l1_dist (apply_P w) (fun _ => 0) = 1/8 * l1_dist w (fun _ => 0) := by
  rw [apply_P_sum_zero w h]
  rw [l1_dist_self_zero, l1_dist_self_zero]
  have : ∑ i : Fin 3, |-1/8 * w i| = 1/8 * ∑ i : Fin 3, |w i| := by
    simp_rw [abs_mul]
    norm_num
    simp_rw [Finset.mul_sum]
  exact this

-- Linearity of apply_P
lemma apply_P_sub (μ ν : Fin 3 → ℝ) :
    apply_P (fun i => μ i - ν i) = fun j => apply_P μ j - apply_P ν j := by
  ext j
  simp only [apply_P]
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext i
  ring

-- L1 distance is translation invariant and equals L1 norm of difference
lemma l1_dist_eq_l1_norm_sub (μ ν : Fin 3 → ℝ) :
    l1_dist μ ν = l1_dist (fun i => μ i - ν i) (fun _ => 0) := by
  simp only [l1_dist, sub_zero]

-- Sum is linear
lemma sum_sub (μ ν : Fin 3 → ℝ) :
    univ.sum (fun i => μ i - ν i) = univ.sum μ - univ.sum ν := by
  rw [← Finset.sum_sub_distrib]

-- Main contraction theorem: holds when μ and ν have equal sums
-- This covers probability distributions (sum = 1) and more generally
-- any vectors in the same affine subspace
lemma contraction :
    ∀ μ ν : S → ℝ,
      univ.sum μ = univ.sum ν →
      l1_dist (apply_P μ) (apply_P ν) ≤ (1/8 : ℝ) * l1_dist μ ν := by
  intro μ ν h_sum
  let w := fun i => μ i - ν i

  -- Key: w has sum 0
  have hw_sum : univ.sum w = 0 := by
    simp only [w]
    rw [sum_sub, h_sum]
    ring

  -- Rewrite using linearity
  calc l1_dist (apply_P μ) (apply_P ν)
      = l1_dist (fun j => apply_P μ j - apply_P ν j) (fun _ => 0) := by
          exact l1_dist_eq_l1_norm_sub (apply_P μ) (apply_P ν)
    _ = l1_dist (apply_P w) (fun _ => 0) := by
          congr 1
          exact (apply_P_sub μ ν).symm
    _ = 1/8 * l1_dist w (fun _ => 0) := sum_zero_contraction w hw_sum
    _ = 1/8 * l1_dist μ ν := by
          rw [l1_dist_eq_l1_norm_sub μ ν]
    _ ≤ 1/8 * l1_dist μ ν := le_refl _

-- Corollary for probability distributions
lemma contraction_distributions (μ ν : Distribution) :
    l1_dist (apply_P μ.val) (apply_P ν.val) ≤ (1/8 : ℝ) * l1_dist μ.val ν.val := by
  apply contraction
  have hμ := μ.property.2
  have hν := ν.property.2
  rw [hμ, hν]

/-! ## ContractionData Package -/

-- MetricSpace instance on Distribution using L1 distance
instance : MetricSpace Distribution where
  dist μ ν := l1_dist μ.val ν.val
  dist_self μ := by
    simp only [l1_dist]
    rw [Finset.sum_eq_zero]
    intro i _
    simp
  dist_comm μ ν := by
    simp only [l1_dist]
    congr 1
    ext i
    rw [abs_sub_comm]
  dist_triangle μ ν ρ := by
    simp only [l1_dist]
    calc ∑ i, |μ.val i - ρ.val i|
        = ∑ i, |(μ.val i - ν.val i) + (ν.val i - ρ.val i)| := by
            congr 1; ext i; abel_nf
      _ ≤ ∑ i, (|μ.val i - ν.val i| + |ν.val i - ρ.val i|) := by
            apply Finset.sum_le_sum
            intro i _
            exact abs_add_le (μ.val i - ν.val i) (ν.val i - ρ.val i)
      _ = (∑ i, |μ.val i - ν.val i|) + (∑ i, |ν.val i - ρ.val i|) := by
            rw [Finset.sum_add_distrib]
  eq_of_dist_eq_zero {μ ν} h := by
    -- Use Subtype extensionality
    apply Subtype.ext
    ext i
    -- From l1_dist = 0, we get |μ i - ν i| = 0 for all i
    have h_sum : ∑ j : Fin 3, |μ.val j - ν.val j| = 0 := h
    have h_each : ∀ j, |μ.val j - ν.val j| = 0 := by
      intro j
      -- All terms non-negative, sum is 0, so all terms are 0
      by_contra h_ne
      have h_pos : 0 < |μ.val j - ν.val j| := by
        rw [abs_pos]
        intro h_eq
        apply h_ne
        rw [h_eq, abs_zero]
      -- Since all terms are non-negative and the sum is 0, each term must be 0
      -- But we have h_pos : 0 < |μ j - ν j|, so the sum must be positive
      have : 0 < ∑ k : Fin 3, |μ.val k - ν.val k| := by
        apply Finset.sum_pos'
        · intro k _; exact abs_nonneg _
        · exact ⟨j, Finset.mem_univ j, h_pos⟩
      linarith [h_sum]
    have : μ.val i - ν.val i = 0 := abs_eq_zero.mp (h_each i)
    linarith

-- Transition map on distributions: applies P and proves result is still a distribution
def applyP_dist (μ : Distribution) : Distribution :=
  ⟨apply_P μ.val, by
    constructor
    · -- Non-negativity: need to show ∀ i, 0 ≤ (P μ) i
      intro i
      simp only [apply_P]
      apply Finset.sum_nonneg
      intro j _
      apply mul_nonneg (P_nonneg i j)
      exact μ.property.1 j
    · -- Sum = 1: need to show Σⱼ (P μ) j = 1
      unfold apply_P
      rw [Finset.sum_comm]
      -- Now we have ∑ j, ∑ i, P i j * μ j
      -- Need to get to ∑ j, μ j * ∑ i, P i j
      conv_lhs =>
        arg 2; ext j
        rw [show univ.sum (fun i => P i j * μ.val j) = univ.sum (fun i => P i j) * μ.val j by
          rw [Finset.sum_mul]]
        rw [mul_comm]
      have : ∑ j : Fin 3, μ.val j * ∑ i : Fin 3, P i j = ∑ j : Fin 3, μ.val j * 1 := by
        congr 1
        ext j
        congr 1
        -- For each j, Σᵢ P i j = 1 (column sum, but P is symmetric so same as row sum)
        calc ∑ i : Fin 3, P i j
            = ∑ i : Fin 3, P j i := by congr 1; ext i; exact P_symmetric i j
          _ = 1 := P_stochastic j
      simp only [this, mul_one]
      exact μ.property.2
  ⟩

-- applyP_dist is a contraction with constant 1/8
def contractionData : ContractionData Distribution where
  f := applyP_dist
  K := 1/8
  K_nonneg := by norm_num
  K_lt_one := by norm_num
  lipschitz := fun μ ν => by
    simp only [dist, applyP_dist]
    exact contraction_distributions μ ν

end -- noncomputable section

end MarkovChain
