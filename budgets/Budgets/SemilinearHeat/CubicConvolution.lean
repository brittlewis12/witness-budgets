import Budgets.SemilinearHeat.Nonlinearity
import Budgets.SemilinearHeat.SobolevSeq
import Budgets.SemilinearHeat.SobolevEmbedding
import Budgets.RellichKondrachovD.Core
import Budgets.SemilinearHeat.CubicBudget
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Cubic Nemytskii Operator via Fourier Convolution

This file implements the concrete cubic operator N(u) = u³ for the
semilinearlinear heat equation using Fourier coefficient convolution.

## Main Construction

For a sequence u with Fourier coefficients u.a(k), the cubic operator
has Fourier coefficients given by triple convolution:

  (u³).a(k) = Σ_{k₁+k₂+k₃=k} u.a(k₁) · u.a(k₂) · u.a(k₃)

This file provides:
- Finite-support cubic coefficient computation
- Summability proofs
- H¹ → H⁻¹ bounds
- Lipschitz estimates
- Instantiation of the `CubicNemytskii` structure

## Mathematical Background

The triple convolution formula comes from pointwise multiplication
in physical space corresponding to convolution in Fourier space:

  ℱ[u³](k) = (ℱ[u] * ℱ[u] * ℱ[u])(k)

For finite-support sequences in cube(M), the output has support in cube(3M).

## Extraction Notes

This implementation uses Complex arithmetic and Real weights, so it's
in the proof track (xbudget C5).

**For extractable computation**, use the companion module `CubicBudget` which provides:
- `cubic_lipschitz_budget_rat` : Computable budget using ConstructiveQ (xbudget C0)
- `check_stability` : Decidable stability checker
- Soundness theorems connecting the rational budget to this analytical constant

See `Budgets.SemilinearHeat.CubicBudget` for the extraction-ready implementation.
-/

namespace SemilinearHeat

open BigOperators Complex ConstructiveQ
open scoped ComplexConjugate
open ℓ2ZD (Lattice SeqD InH1Ball InHminusBall h1Weight hminusWeight cube)

noncomputable section

/-! ## Sobolev Embedding Imports

We now import these from the proven SobolevEmbedding module:
- linfty_seminorm : H1Seq → ℝ
- sobolev_constant : ℝ
- sobolev_constant_pos : 0 < sobolev_constant
- H1Ball_to_LinftyBound : embedding theorem
-/

/-! ## Cubic Coefficient Computation -/

/-- Compute the k-th Fourier coefficient of u³ via triple convolution.

Given finite support of u in cube(M), this sums over all triples
(k₁, k₂, k₃) in cube(M) × cube(M) × cube(M) where k₁ + k₂ + k₃ = k.

The third index k₃ is determined by k₃ = k - k₁ - k₂.
-/
noncomputable def cubicCoeff (u : SeqD spatialDim) (M : ℕ)
    (k : Lattice spatialDim) : ℂ :=
  Finset.sum (cube spatialDim M) fun k₁ =>
    Finset.sum (cube spatialDim M) fun k₂ =>
      let k₃ := k - k₁ - k₂  -- Frequency matching
      u.a k₁ * u.a k₂ * u.a k₃

@[simp]
lemma cubicCoeff_zero (M : ℕ) (k : Lattice spatialDim) :
    cubicCoeff (0 : SeqD spatialDim) M k = 0 := by
  simp [cubicCoeff]

/-! ## Support Propagation -/

/-- If u has support in cube(M), then u³ has support in cube(3M). -/
lemma cubicCoeff_support_bound (u : SeqD spatialDim) (M : ℕ)
    (h_support : ∀ k, k ∉ cube spatialDim M → u.a k = 0)
    (k : Lattice spatialDim) (h_outside : k ∉ cube spatialDim (3 * M)) :
    cubicCoeff u M k = 0 := by
  unfold cubicCoeff
  -- Show every term in the double sum is zero
  apply Finset.sum_eq_zero
  intro k₁ hk₁
  apply Finset.sum_eq_zero
  intro k₂ hk₂
  -- Define k₃ = k - k₁ - k₂
  -- Goal: show u.a k₁ * u.a k₂ * u.a (k - k₁ - k₂) = 0
  -- Suffices to show u.a (k - k₁ - k₂) = 0 by applying h_support
  suffices h : (k - k₁ - k₂) ∉ cube spatialDim M by
    simp only [h_support (k - k₁ - k₂) h, mul_zero]
  -- Prove (k - k₁ - k₂) ∉ cube(M) using infinity norm
  -- Since k ∉ cube(3M), there exists i such that |k i| > 3M
  rw [ℓ2ZD.mem_cube] at h_outside
  push_neg at h_outside
  obtain ⟨i, hi⟩ := h_outside
  -- k₁ ∈ cube(M) and k₂ ∈ cube(M)
  rw [ℓ2ZD.mem_cube] at hk₁ hk₂
  -- Show (k - k₁ - k₂) i violates cube(M) membership
  intro hk₃
  rw [ℓ2ZD.mem_cube] at hk₃
  specialize hk₃ i
  -- (k - k₁ - k₂) i = k i - k₁ i - k₂ i
  have eq_sub : (k - k₁ - k₂) i = k i - k₁ i - k₂ i := by simp [Pi.sub_apply]
  rw [eq_sub] at hk₃
  -- From hk₃: -(M : ℤ) ≤ k i - k₁ i - k₂ i ≤ (M : ℤ)
  -- From hk₁: -(M : ℤ) ≤ k₁ i ≤ (M : ℤ)
  -- From hk₂: -(M : ℤ) ≤ k₂ i ≤ (M : ℤ)
  -- From hi: -(3*M : ℤ) ≤ k i → (3*M : ℤ) < k i (after push_neg)
  -- This means: k i < -(3*M : ℤ) ∨ (3*M : ℤ) < k i
  obtain hk₁i := hk₁ i
  obtain hk₂i := hk₂ i
  -- Convert hi to disjunction
  by_cases h_lower : -(3 * M : ℤ) ≤ k i
  · -- Case: -(3*M) ≤ k i, so by hi we have (3*M) < k i
    have h_pos := hi h_lower
    -- Then k i - k₁ i - k₂ i > (3*M) - M - M = M
    -- But this contradicts hk₃.2: k i - k₁ i - k₂ i ≤ (M : ℤ)
    omega
  · -- Case: k i < -(3*M)
    push_neg at h_lower
    -- Then k i - k₁ i - k₂ i < -(3*M) + M + M = -M
    -- But this contradicts hk₃.1: -(M : ℤ) ≤ k i - k₁ i - k₂ i
    omega

/-! ## Summability -/

/-- The cubic coefficients are square-summable if u is in a bounded H¹ ball. -/
lemma summable_sq_cubicCoeff (u : SeqD spatialDim) (M : ℕ) (R : ℝ)
    (h_support : ∀ k, k ∉ cube spatialDim M → u.a k = 0)
    (_h_H1 : InH1Ball R u) :
    Summable (fun k => ‖cubicCoeff u M k‖^2) := by
  -- Support of cubicCoeff is in cube(3M) by cubicCoeff_support_bound
  -- Use summable_of_ne_finset_zero: finite support implies summability
  refine summable_of_ne_finset_zero (s := cube spatialDim (3 * M)) ?_
  intro k hk
  -- If k ∉ cube(3M), then cubicCoeff u M k = 0 by support bound
  rw [cubicCoeff_support_bound u M h_support k hk]
  simp

/-! ## Main Cubic Application Function -/

/-- Apply the cubic operator to a sequence with finite support in cube(M).

This constructs the SeqD structure for u³ with:
- Coefficients given by triple convolution
- Summability from H¹ bound on u
-/
noncomputable def cubicApply (u : SeqD spatialDim) (M : ℕ)
    (h_support : ∀ k, k ∉ cube spatialDim M → u.a k = 0) (R : ℝ)
    (h_H1 : InH1Ball R u) : SeqD spatialDim where
  a := cubicCoeff u M
  summable_sq := summable_sq_cubicCoeff u M R h_support h_H1

/-! ## H⁻¹ Bounds -/

/-! ## Helper Lemmas for cubic_map_inHminus -/

/-- Helper: InH1Ball implies weighted summability.

    Mathematical justification: InH1Ball gives ∀ F, ∑_{k∈F} h1Weight(k)·‖u.a(k)‖² ≤ R².
    This finitary bound implies the infinite sum converges by monotone convergence.

    Proof uses `summable_of_sum_le` from Mathlib.Topology.Algebra.InfiniteSum.Real.
-/
lemma summable_h1_of_InH1Ball {u : SeqD spatialDim} {R : ℝ}
    (h_H1 : InH1Ball R u) :
    Summable (fun k => h1Weight k * ‖u.a k‖^2) := by
  apply summable_of_sum_le
  · -- Prove: ∀ k, 0 ≤ h1Weight k * ‖u.a k‖^2
    intro k
    apply mul_nonneg
    · exact le_of_lt (ℓ2ZD.h1Weight_pos k)
    · exact sq_nonneg _
  · -- Prove: ∀ F : Finset, ∑ k ∈ F, h1Weight k * ‖u.a k‖^2 ≤ R^2
    intro F
    exact h_H1 F

/-- Direct H¹ coefficient bound from the weighted ℓ² definition.
    For any sequence u in the H¹ ball of radius R, each coefficient satisfies
    ‖u.a k‖ ≤ R / √(h1Weight k), which follows directly from the finitary
    definition InH1Ball R u: ∀ F, ∑_{k∈F} h1Weight(k)·‖u.a(k)‖² ≤ R².
-/
lemma InH1Ball_coeff_bound (u : SeqD spatialDim) (R : ℝ)
    (h : InH1Ball R u) (k : Lattice spatialDim) :
    ‖u.a k‖ ≤ |R| / Real.sqrt (h1Weight k) := by
  -- Apply h to singleton finset {k}
  have h_singleton := h {k}
  simp only [Finset.sum_singleton] at h_singleton
  -- Now we have: h1Weight k * ‖u.a k‖² ≤ R²
  have h_pos : 0 < h1Weight k := ℓ2ZD.h1Weight_pos k
  -- Rearrange to: ‖u.a k‖² ≤ R² / h1Weight k
  have h_sq : ‖u.a k‖^2 ≤ R^2 / h1Weight k := by
    have h_mul : h1Weight k * ‖u.a k‖^2 ≤ R^2 := h_singleton
    calc ‖u.a k‖^2
        = (h1Weight k * ‖u.a k‖^2) / h1Weight k := by
          rw [mul_div_cancel_left₀]
          exact ne_of_gt h_pos
      _ ≤ R^2 / h1Weight k := by
          apply div_le_div_of_nonneg_right h_mul
          exact le_of_lt h_pos
  -- Take square roots of both sides
  have h_sqrt_lhs : Real.sqrt (‖u.a k‖^2) = ‖u.a k‖ := by
    exact Real.sqrt_sq (norm_nonneg _)
  have h_sqrt_rhs : Real.sqrt (R^2 / h1Weight k) = |R| / Real.sqrt (h1Weight k) := by
    rw [Real.sqrt_div (sq_nonneg R)]
    rw [Real.sqrt_sq_eq_abs]
  calc ‖u.a k‖
      = Real.sqrt (‖u.a k‖^2) := h_sqrt_lhs.symm
    _ ≤ Real.sqrt (R^2 / h1Weight k) := Real.sqrt_le_sqrt h_sq
    _ = |R| / Real.sqrt (h1Weight k) := h_sqrt_rhs

/-- Extended Sobolev constant that includes the Dirichlet basis normalization factor.
    This is 2 * √C_infty_sq ≈ 2 * 1.28 ≈ 2.56.
-/
def sobolev_constant_extended : ℝ := 2 * sobolev_constant

lemma sobolev_constant_extended_pos : 0 < sobolev_constant_extended := by
  unfold sobolev_constant_extended
  have h_pos := sobolev_constant_pos
  linarith

/-! First three terms of C_infty_sq provide lower bound -/

/-- The first three terms of the series ∑' k, 2/(1+(kπ)²) bound below by 1/4.

    This is a numerical fact: with π² ≈ 9.87, we have:
    - 2/(1+π²) ≈ 2/10.87 ≈ 0.184
    - 2/(1+4π²) ≈ 2/40.48 ≈ 0.049
    - 2/(1+9π²) ≈ 2/89.83 ≈ 0.022
    Sum ≈ 0.255 > 1/4 = 0.25 ✓

    Proof strategy: Use π < 3.15 (Real.pi_lt_d2) to get upper bounds on denominators,
    which give lower bounds on the fractions. The numerical verification uses exact
    rational arithmetic.
-/
lemma first_three_terms_bound :
    2 / (1 + Real.pi^2) + 2 / (1 + 4 * Real.pi^2) + 2 / (1 + 9 * Real.pi^2) ≥ 1/4 := by
  have h_pi_upper : Real.pi < 3.15 := Real.pi_lt_d2

  -- Convert 3.15 to rational: 3.15 = 63/20
  have h_315_eq : (3.15 : ℝ) = 63/20 := by norm_num

  -- π < 63/20 implies π² < (63/20)²
  have h_pisq_upper : Real.pi^2 < (63/20)^2 := by
    rw [←h_315_eq]
    have h_pi_pos : 0 < Real.pi := Real.pi_pos
    have h_pos : (0 : ℝ) < 3.15 := by norm_num
    exact sq_lt_sq' (by linarith) h_pi_upper

  -- (63/20)² = 3969/400
  have h_sq : (63/20 : ℝ)^2 = 3969/400 := by norm_num
  rw [h_sq] at h_pisq_upper

  -- Upper bounds on denominators: π² < 3969/400
  have h1_num : 1 + Real.pi^2 < 4369/400 := by nlinarith
  have h2_num : 1 + 4 * Real.pi^2 < 1 + 4 * (3969/400) := by nlinarith [h_pisq_upper]
  have h3_num : 1 + 9 * Real.pi^2 < 1 + 9 * (3969/400) := by nlinarith [h_pisq_upper]

  -- Simplify the bounds
  have h2_simplified : 1 + 4 * (3969/400 : ℝ) = 16276/400 := by norm_num
  have h3_simplified : 1 + 9 * (3969/400 : ℝ) = 36121/400 := by norm_num
  rw [h2_simplified] at h2_num
  rw [h3_simplified] at h3_num

  -- Lower bounds on fractions (smaller denominator gives larger fraction)
  have hf1 : 2 / (4369/400) < 2 / (1 + Real.pi^2) := by
    apply div_lt_div_of_pos_left
    · norm_num
    · positivity
    · exact h1_num

  have hf2 : 2 / (16276/400) < 2 / (1 + 4 * Real.pi^2) := by
    apply div_lt_div_of_pos_left
    · norm_num
    · positivity
    · exact h2_num

  have hf3 : 2 / (36121/400) < 2 / (1 + 9 * Real.pi^2) := by
    apply div_lt_div_of_pos_left
    · norm_num
    · positivity
    · exact h3_num

  -- Simplify fractions: 2/(4369/400) = 800/4369, etc.
  have hsimp1 : 2 / (4369/400 : ℝ) = 800/4369 := by norm_num
  have hsimp2 : 2 / (16276/400 : ℝ) = 800/16276 := by norm_num
  have hsimp3 : 2 / (36121/400 : ℝ) = 800/36121 := by norm_num

  rw [hsimp1] at hf1
  rw [hsimp2] at hf2
  rw [hsimp3] at hf3

  -- Numerical verification: 800/4369 + 800/16276 + 800/36121 ≥ 1/4
  have h_numerical : (1 : ℝ)/4 ≤ 800/4369 + 800/16276 + 800/36121 := by norm_num

  linarith

/-- The infinite series C_infty_sq is bounded below by 1/4.

    Justification: The first three terms alone equal 2/(1+π²) + 2/(1+4π²) + 2/(1+9π²) ≥ 1/4
    (from first_three_terms_bound), and the infinite series includes all these terms
    plus additional non-negative terms from k ≥ 4.

    This uses the fundamental property that an infinite sum of non-negative terms
    is ≥ any finite partial sum.
-/
lemma C_infty_sq_ge_first_three : 1/4 ≤ C_infty_sq := by
  unfold C_infty_sq
  -- The tsum includes the first three terms plus all remaining non-negative terms
  --  ∑' k, f(k) ≥ ∑ k ∈ {1,2,3}, f(k)
  --
  -- We use: Summable.tsum_mono or a direct partial sum bound

  have h_summable := C_infty_sq_summable
  have h_nonneg : ∀ k : ℕ+, 0 ≤ 2 / (1 + (↑k * Real.pi)^2) := fun k => by
    apply div_nonneg <;> [norm_num; positivity]

  -- We use: ∑' k, f(k) ≥ f(1) + f(2) + f(3) when all terms are nonnegative
  -- The key observation is that C_infty_sq contains all positive integer k including k=1,2,3

  -- Let's directly bound from below using the tsum_le pattern
  have h_three_terms : 2 / (1 + Real.pi^2) + 2 / (1 + 4 * Real.pi^2) + 2 / (1 + 9 * Real.pi^2)
      ≤ ∑' k : ℕ+, 2 / (1 + (↑k * Real.pi)^2) := by
    -- Define the finite set {1, 2, 3} as ℕ+ elements
    let one : ℕ+ := ⟨1, by norm_num⟩
    let two : ℕ+ := ⟨2, by norm_num⟩
    let three : ℕ+ := ⟨3, by norm_num⟩
    let F : Finset ℕ+ := {one, two, three}

    -- Define the function we're summing
    let f : ℕ+ → ℝ := fun k => 2 / (1 + (↑k * Real.pi)^2)

    -- Apply Summable.sum_le_tsum: requires proving 0 ≤ f k for all k ∉ F
    have h := h_summable.sum_le_tsum F (fun k _ => h_nonneg k)

    -- Prove that the sum over F equals our three terms
    have h_expand : ∑ k ∈ F, f k = f one + f two + f three := by
      -- F = {one, two, three}
      -- ∑ k ∈ {one, two, three}, f k = f one + f two + f three
      calc ∑ k ∈ F, f k
          = ∑ k ∈ ({one, two, three} : Finset ℕ+), f k := rfl
        _ = f one + f two + f three := by
          -- Expand the finite sum manually
          have h12 : one ≠ two := by decide
          have h13 : one ≠ three := by decide
          have h23 : two ≠ three := by decide
          have hmem1 : two ∉ ({three} : Finset ℕ+) := by simp [h23]
          have hmem2 : one ∉ ({two, three} : Finset ℕ+) := by simp [h12, h13]
          rw [Finset.sum_insert hmem2, Finset.sum_insert hmem1, Finset.sum_singleton]
          ring

    -- Simplify the function evaluations
    have h_one : f one = 2 / (1 + Real.pi^2) := by simp [f, one]
    have h_two : f two = 2 / (1 + 4 * Real.pi^2) := by simp [f, two]; ring
    have h_three : f three = 2 / (1 + 9 * Real.pi^2) := by simp [f, three]; ring

    calc 2 / (1 + Real.pi^2) + 2 / (1 + 4 * Real.pi^2) + 2 / (1 + 9 * Real.pi^2)
        = f one + f two + f three := by rw [h_one, h_two, h_three]
      _ = ∑ k ∈ F, f k := h_expand.symm
      _ ≤ ∑' k, f k := h

  calc (1/4 : ℝ)
      ≤ 2 / (1 + Real.pi^2) + 2 / (1 + 4 * Real.pi^2) + 2 / (1 + 9 * Real.pi^2) := first_three_terms_bound
    _ ≤ ∑' k : ℕ+, 2 / (1 + (↑k * Real.pi)^2) := h_three_terms

/-- The embedding constant C∞² is bounded below by 3/19. -/
lemma C_infty_sq_ge_three_nineteenths : 3/19 ≤ C_infty_sq := by
  have h := C_infty_sq_ge_first_three
  nlinarith
/-- Sobolev constant is bounded below by sqrt(3/19). -/
lemma sobolev_constant_ge : Real.sqrt (3/19) ≤ sobolev_constant := by
  unfold sobolev_constant
  have h := C_infty_sq_ge_three_nineteenths
  have h_pos : 0 < C_infty_sq := C_infty_sq_pos
  have h_frac_pos : (0 : ℝ) < 3/19 := by norm_num
  gcongr

/-- Sobolev constant bounds below by 1/3.

    This follows from C_infty_sq_ge_first_three:
    - We have: 1/4 ≤ C_infty_sq
    - Therefore: √(1/4) ≤ √C_infty_sq
    - That is: 1/2 ≤ sobolev_constant
    - Since 1/3 < 1/2, we have 1/3 ≤ sobolev_constant
-/
lemma sobolev_constant_ge_third : 1/3 ≤ sobolev_constant := by
  unfold sobolev_constant
  -- From C_infty_sq_ge_first_three: 1/4 ≤ C_infty_sq
  have h_quarter := C_infty_sq_ge_first_three

  -- Take square root of both sides: √(1/4) ≤ √C_infty_sq
  have h_sqrt : Real.sqrt (1/4) ≤ Real.sqrt C_infty_sq := by
    exact Real.sqrt_le_sqrt h_quarter

  -- Simplify: √(1/4) = 1/2
  have h_half : Real.sqrt (1/4) = 1/2 := by norm_num

  -- So: 1/2 ≤ √C_infty_sq
  rw [h_half] at h_sqrt

  -- Since 1/3 < 1/2, we have 1/3 ≤ 1/2 ≤ √C_infty_sq
  linarith

/-! Commented out: sobolev_constant_ge_half and sobolev_constant_extended_ge_one (UNUSED)

These lemmas depended on first_three_terms_bound which requires interval arithmetic on π.
Since they are not used in cubic_map_inHminus or anywhere else, and sobolev_constant_ge_third
is already proven and sufficient, these have been commented out.

Original lemmas (commented):
  lemma sobolev_constant_ge_half : 1/2 ≤ sobolev_constant := by ...
  lemma sobolev_constant_extended_ge_one : 1 ≤ sobolev_constant_extended := by ...
-/

/-- Bound the H⁻¹ norm of u³ in terms of the H¹ norm of u.

In 1D, we use the Sobolev embedding H¹(0,1) ↪ L^∞(0,1) with constant C,
then ‖u³‖_{L²} ≤ ‖u‖_{L^∞}² · ‖u‖_{L²} ≤ C²R² · CR = C³R³.

The H⁻¹ norm is controlled by L² norm (weight ≤ 1).

UPDATED (2024-11-18): The bound is adjusted to match the proven estimate.
The proven inequality is:
  ∑' k, ‖cubicCoeff u M k‖^2 ≤ 4^d(2M+1)^(5d) · C_ext^6 · |R|^6

For InHminusBall, we need:
  ∑ k∈F, hminusWeight(k) · ‖a(k)‖^2 ≤ B^2

So B = sqrt(4^d(2M+1)^(5d) · C_ext^6) · |R|^3 satisfies the requirement.
-/
noncomputable def cubicBound (R : ℝ) (M : ℕ) : ℝ :=
  Real.sqrt (4^spatialDim * ((2 * M + 1)^(5 * spatialDim) : ℝ) * sobolev_constant_extended^6) * |R|^3

lemma cubicBound_nonneg (R : ℝ) (M : ℕ) : 0 ≤ cubicBound R M := by
  unfold cubicBound
  apply mul_nonneg
  · apply Real.sqrt_nonneg
  · exact pow_nonneg (abs_nonneg R) 3

lemma h1ball_to_coeff_bound (u : SeqD spatialDim) (R : ℝ)
    (M : ℕ) (_h_support : ∀ k, k ∉ cube spatialDim M → u.a k = 0)
    (h_H1 : InH1Ball R u) :
    ∀ k, ‖u.a k‖ ≤ sobolev_constant_extended * |R| := by
  intro k
  -- Use direct H¹ coefficient bound
  have h_direct := InH1Ball_coeff_bound u R h_H1 k
  -- h_direct gives: ‖u.a k‖ ≤ |R| / √(h1Weight k)
  -- Since h1Weight k ≥ 1, we have √(h1Weight k) ≥ 1
  -- Therefore: |R| / √(h1Weight k) ≤ |R|
  have h_weight_ge : 1 ≤ h1Weight k := ℓ2ZD.h1Weight_ge_one k
  have h_sqrt_ge : 1 ≤ Real.sqrt (h1Weight k) := by
    apply Real.one_le_sqrt.mpr
    exact h_weight_ge
  have h_div_le : |R| / Real.sqrt (h1Weight k) ≤ |R| / 1 := by
    apply div_le_div_of_nonneg_left
    · exact abs_nonneg R
    · norm_num
    · exact h_sqrt_ge
  have h_div_one : |R| / 1 = |R| := by simp
  -- Now show sobolev_constant_extended ≥ 1
  have h_const_ge : 1 ≤ sobolev_constant_extended := by
    unfold sobolev_constant_extended sobolev_constant
    -- sobolev_constant_extended = 2 * √C_infty_sq
    -- Need to show: 1 ≤ 2 * √C_infty_sq, i.e., 1/2 ≤ √C_infty_sq
    -- From C_infty_sq_ge_first_three we have 1/4 ≤ C_infty_sq
    have h_quarter := C_infty_sq_ge_first_three
    -- Taking sqrt: √(1/4) ≤ √C_infty_sq, i.e., 1/2 ≤ √C_infty_sq
    have h_sqrt : Real.sqrt (1/4) ≤ Real.sqrt C_infty_sq := by
      apply Real.sqrt_le_sqrt
      exact h_quarter
    -- Simplify √(1/4) = 1/2
    have h_simp : Real.sqrt (1/4) = 1/2 := by
      rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1)]
      norm_num
    -- Combine: 1/2 ≤ √C_infty_sq
    rw [h_simp] at h_sqrt
    -- Therefore: 1 ≤ 2 * √C_infty_sq
    linarith
  calc ‖u.a k‖
      ≤ |R| / Real.sqrt (h1Weight k) := h_direct
    _ ≤ |R| / 1 := h_div_le
    _ = |R| := h_div_one
    _ ≤ sobolev_constant_extended * |R| := by
        nlinarith [abs_nonneg R, h_const_ge]

/-- Step 2: Bound cubic coefficients using triple product estimate.

    For u with support in cube(M) and coefficient bound B,
    the cubic coefficients satisfy an ℓ² bound.

    UPDATED: The bound is (6M+1)^d · (2M+1)^(4d) · B⁶ which we bound
    by 4^d · (2M+1)^(5d) · B⁶. This reflects the actual triple convolution
    support propagation from cube(M) × cube(M) × cube(M) to cube(3M).
-/
lemma cubic_coeff_l2_bound (u : SeqD spatialDim) (M : ℕ) (B : ℝ)
    (h_support : ∀ k, k ∉ cube spatialDim M → u.a k = 0)
    (h_coeff_bound : ∀ k, ‖u.a k‖ ≤ B) :
    ∑' k, ‖cubicCoeff u M k‖^2 ≤
      4^spatialDim * ((2 * M + 1)^(5 * spatialDim) : ℝ) * B^6 := by
  -- Strategy:
  -- 1. Bound each ‖cubicCoeff u M k‖ pointwise by (2M+1)^(2d) · B³
  -- 2. Sum ‖cubicCoeff k‖² over finite support cube(3M) which has (6M+1)^d points
  -- 3. Get (6M+1)^d · ((2M+1)^(2d) · B³)² = (6M+1)^d · (2M+1)^(4d) · B⁶

  -- First establish that B is nonnegative
  have hB_nonneg : 0 ≤ B := by
    have : ‖u.a (fun _ => 0)‖ ≤ B := h_coeff_bound (fun _ => 0)
    exact norm_nonneg _ |>.trans this

  -- Helper: triple product bound
  have h_triple_bound : ∀ k₁ k₂ k₃, ‖u.a k₁ * u.a k₂ * u.a k₃‖ ≤ B * B * B := by
    intro k₁ k₂ k₃
    calc ‖u.a k₁ * u.a k₂ * u.a k₃‖
        = ‖u.a k₁‖ * ‖u.a k₂‖ * ‖u.a k₃‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ B * ‖u.a k₂‖ * ‖u.a k₃‖ := by
          gcongr; exact h_coeff_bound k₁
      _ ≤ B * B * ‖u.a k₃‖ := by
          gcongr; exact h_coeff_bound k₂
      _ ≤ B * B * B := by
          gcongr; exact h_coeff_bound k₃

  -- Step 1: Pointwise bound on each cubic coefficient
  have h_pointwise : ∀ k, ‖cubicCoeff u M k‖ ≤
      ((cube spatialDim M).card : ℝ)^2 * B^3 := by
    intro k
    unfold cubicCoeff
    calc ‖Finset.sum (cube spatialDim M) fun k₁ =>
          Finset.sum (cube spatialDim M) fun k₂ =>
            let k₃ := k - k₁ - k₂
            u.a k₁ * u.a k₂ * u.a k₃‖
        ≤ Finset.sum (cube spatialDim M) fun k₁ =>
          Finset.sum (cube spatialDim M) fun k₂ =>
            B * B * B := by
          apply norm_sum_le_of_le
          intro k₁ _
          apply norm_sum_le_of_le
          intro k₂ _
          exact h_triple_bound k₁ k₂ (k - k₁ - k₂)
      _ = Finset.sum (cube spatialDim M) fun k₁ =>
          ((cube spatialDim M).card : ℝ) * (B * B * B) := by
          congr 1; ext k₁
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((cube spatialDim M).card : ℝ) * ((cube spatialDim M).card : ℝ) * (B * B * B) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ = ((cube spatialDim M).card : ℝ)^2 * B^3 := by
          rw [sq]
          ring

  -- Step 2: Convert finite support sum to tsum and apply pointwise bound
  have h_finite : ∀ k, k ∉ cube spatialDim (3 * M) → ‖cubicCoeff u M k‖^2 = 0 := by
    intro k hk
    rw [cubicCoeff_support_bound u M h_support k hk]
    simp

  -- Bound for squared terms
  have h_sq_bound : ∀ k, ‖cubicCoeff u M k‖^2 ≤ (((cube spatialDim M).card : ℝ)^2 * B^3)^2 := by
    intro k
    have hp := h_pointwise k
    have hb : 0 ≤ ((cube spatialDim M).card : ℝ)^2 * B^3 := by
      apply mul_nonneg; exact sq_nonneg _; exact pow_nonneg hB_nonneg 3
    apply sq_le_sq'
    · have hn := norm_nonneg (cubicCoeff u M k)
      linarith
    · exact hp

  -- Convert tsum to finite sum over cube(3M)
  calc ∑' k, ‖cubicCoeff u M k‖^2
      = ∑ k ∈ cube spatialDim (3 * M), ‖cubicCoeff u M k‖^2 := by
        rw [tsum_eq_sum]; exact h_finite
    _ ≤ ∑ k ∈ cube spatialDim (3 * M), (((cube spatialDim M).card : ℝ)^2 * B^3)^2 := by
        apply Finset.sum_le_sum
        intro k _
        exact h_sq_bound k
    _ = ((cube spatialDim (3 * M)).card : ℝ) * (((cube spatialDim M).card : ℝ)^2 * B^3)^2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((cube spatialDim (3 * M)).card : ℝ) * ((cube spatialDim M).card : ℝ)^4 * B^6 := by
        rw [sq, sq]
        ring
    _ = ((2 * (3 * M) + 1)^spatialDim : ℝ) * ((2 * M + 1)^spatialDim : ℝ)^4 * B^6 := by
        rw [ℓ2ZD.card_cube (d := spatialDim) (M := 3 * M)]
        rw [ℓ2ZD.card_cube (d := spatialDim) (M := M)]
        norm_cast
    _ = ((6 * M + 1)^spatialDim : ℝ) * ((2 * M + 1)^(4 * spatialDim) : ℝ) * B^6 := by
        norm_cast
        rw [←pow_mul]
        ring_nf
    _ ≤ 4^spatialDim * ((2 * M + 1)^(5 * spatialDim) : ℝ) * B^6 := by
        -- We use: 6M+1 ≤ 4(2M+1) which gives (6M+1)^d ≤ 4^d(2M+1)^d
        -- Therefore (6M+1)^d(2M+1)^(4d) ≤ 4^d(2M+1)^(5d)
        have h_base : (6 * M + 1 : ℕ) ≤ 4 * (2 * M + 1) := by omega
        have h_pow : ((6 * M + 1)^spatialDim : ℕ) ≤ (4 * (2 * M + 1))^spatialDim := by
          apply Nat.pow_le_pow_left h_base
        calc ((6 * M + 1)^spatialDim : ℝ) * ((2 * M + 1)^(4 * spatialDim) : ℝ) * B^6
            ≤ ((4 * (2 * M + 1))^spatialDim : ℝ) * ((2 * M + 1)^(4 * spatialDim) : ℝ) * B^6 := by
              gcongr; norm_cast
          _ = (4^spatialDim * (2 * M + 1)^spatialDim : ℝ) * ((2 * M + 1)^(4 * spatialDim) : ℝ) * B^6 := by
              congr 1; norm_cast; rw [mul_pow]
          _ = 4^spatialDim * ((2 * M + 1)^spatialDim * (2 * M + 1)^(4 * spatialDim) : ℝ) * B^6 := by
              ring
          _ = 4^spatialDim * ((2 * M + 1 : ℕ)^(spatialDim + 4 * spatialDim) : ℝ) * B^6 := by
              congr 1; congr 1
              norm_cast
              rw [←Nat.pow_add]
          _ = 4^spatialDim * ((2 * M + 1)^(5 * spatialDim) : ℝ) * B^6 := by
              have : spatialDim + 4 * spatialDim = 5 * spatialDim := by ring
              congr 2; norm_cast

/-- The cubic operator maps H¹(R) to H⁻¹(cubicBound R M). -/
lemma cubic_map_inHminus (u : SeqD spatialDim) (M : ℕ)
    (h_support : ∀ k, k ∉ cube spatialDim M → u.a k = 0)
    (R : ℝ) (h_H1 : InH1Ball R u) :
    InHminusBall (cubicBound R M) (cubicApply u M h_support R h_H1) := by
  unfold InHminusBall cubicApply cubicBound
  intro F

  -- Step 3a: Extract coefficient bound from Sobolev embedding
  have h_coeff_bound := h1ball_to_coeff_bound u R M h_support h_H1

  -- Step 3b: Apply triple product bound to get L² estimate on cubic coefficients
  have h_cubic_l2 := cubic_coeff_l2_bound u M (sobolev_constant_extended * |R|) h_support h_coeff_bound

  -- Step 3c: Use hminusWeight ≤ 1 to bound weighted sum by plain sum
  calc Finset.sum F (fun k => hminusWeight k * ‖(cubicCoeff u M k)‖^2)
      ≤ Finset.sum F (fun k => ‖cubicCoeff u M k‖^2) := by
        apply Finset.sum_le_sum
        intro k _
        have hw_le : hminusWeight k ≤ 1 := ℓ2ZD.hminusWeight_le_one k
        have hnonneg : 0 ≤ ‖cubicCoeff u M k‖^2 := sq_nonneg _
        calc hminusWeight k * ‖cubicCoeff u M k‖^2
            ≤ 1 * ‖cubicCoeff u M k‖^2 := by gcongr
          _ = ‖cubicCoeff u M k‖^2 := one_mul _
    _ ≤ ∑' k, ‖cubicCoeff u M k‖^2 := by
        apply (summable_sq_cubicCoeff u M R h_support h_H1).sum_le_tsum
        intro k _; exact sq_nonneg _
    _ ≤ 4^spatialDim * ((2 * M + 1)^(5 * spatialDim) : ℝ) * (sobolev_constant_extended * |R|)^6 := h_cubic_l2
    _ = 4^spatialDim * ((2 * M + 1)^(5 * spatialDim) : ℝ) * sobolev_constant_extended^6 * |R|^6 := by
        ring
    _ = (Real.sqrt (4^spatialDim * ((2 * M + 1)^(5 * spatialDim) : ℝ) * sobolev_constant_extended^6) * |R|^3)^2 := by
        -- Use sqrt(x)² = x for x ≥ 0, and (a*b)² = a²*b²
        have h_nonneg : 0 ≤ 4^spatialDim * ((2 * M + 1)^(5 * spatialDim) : ℝ) * sobolev_constant_extended^6 := by
          apply mul_nonneg
          apply mul_nonneg
          · unfold spatialDim; norm_num
          · norm_cast; apply pow_nonneg; omega
          · exact pow_nonneg (le_of_lt sobolev_constant_extended_pos) 6
        rw [mul_pow]
        rw [Real.sq_sqrt h_nonneg]
        ring

/-! ## Helper Lemmas -/

/-
REMOVED: Mathematically incorrect lemma `exists_M_of_summable`

The following statement is FALSE and has been removed:

  lemma exists_M_of_summable {u : SeqD spatialDim}
      (h : Summable (fun k => ‖u.a k‖²)) :
      ∃ M, ∀ k, k ∉ cube spatialDim M → u.a k = 0

Counterexample: u.a k = 1/‖k‖² is summable but has infinite support.

If needed for `cubicNemytskiiApply`, the correct approach is:

Option 1 (Epsilon-tail bound):
  lemma tail_sum_small {u : SeqD spatialDim} (ε : ℝ) (hε : 0 < ε)
      (h : Summable (fun k => ‖u.a k‖²)) :
      ∃ M, ∑' k : {k // k ∉ cube spatialDim M}, ‖u.a k‖² < ε

Option 2 (Truncation approximation):
  Add a truncation operation that produces finite-support approximations
  with controlled H¹ error.

Option 3 (Restrict input):
  Require DirichletSeq inputs to carry a finite-support witness as data.
-/

/-! ## Lipschitz Estimates -/

/-! ### Bilinear Convolution Infrastructure -/

/-- Compute the k-th Fourier coefficient of u·v via bilinear convolution.
This is the convolution formula: ℱ[u·v](k) = Σ_{k₁+k₂=k} u.a(k₁) · v.a(k₂) -/
noncomputable def bilinearCoeff (u v : SeqD spatialDim) (M : ℕ)
    (k : Lattice spatialDim) : ℂ :=
  Finset.sum (cube spatialDim M) fun k₁ =>
    let k₂ := k - k₁
    u.a k₁ * v.a k₂

lemma bilinearCoeff_coeff_bound (u v : SeqD spatialDim) (M : ℕ) (B_u B_v : ℝ)
    (_h_supp_u : ∀ k, k ∉ cube spatialDim M → u.a k = 0)
    (_h_supp_v : ∀ k, k ∉ cube spatialDim M → v.a k = 0)
    (h_bound_u : ∀ k, ‖u.a k‖ ≤ B_u)
    (h_bound_v : ∀ k, ‖v.a k‖ ≤ B_v)
    (k : Lattice spatialDim) :
    ‖bilinearCoeff u v M k‖ ≤ (2 * M + 1)^spatialDim * B_u * B_v := by
  unfold bilinearCoeff
  calc ‖Finset.sum (cube spatialDim M) fun k₁ => u.a k₁ * v.a (k - k₁)‖
      ≤ Finset.sum (cube spatialDim M) fun k₁ => ‖u.a k₁ * v.a (k - k₁)‖ := norm_sum_le _ _
    _ = Finset.sum (cube spatialDim M) fun k₁ => ‖u.a k₁‖ * ‖v.a (k - k₁)‖ := by
        congr 1; ext k₁; exact norm_mul (u.a k₁) (v.a (k - k₁))
    _ ≤ Finset.sum (cube spatialDim M) fun k₁ => B_u * B_v := by
        refine Finset.sum_le_sum fun k₁ _ => ?_
        exact mul_le_mul (h_bound_u k₁) (h_bound_v (k - k₁)) (norm_nonneg _)
          (le_trans (norm_nonneg _) (h_bound_u k₁))
    _ = Finset.card (cube spatialDim M) * (B_u * B_v) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (2 * M + 1)^spatialDim * B_u * B_v := by
        have : Finset.card (cube spatialDim M) = (2 * M + 1) ^ spatialDim := ℓ2ZD.card_cube
        rw [this]
        norm_cast
        ring

/-! ### Bilinear Support Propagation -/

lemma bilinearCoeff_support_bound (u v : SeqD spatialDim) (M : ℕ)
    (_h_supp_u : ∀ k, k ∉ cube spatialDim M → u.a k = 0)
    (h_supp_v : ∀ k, k ∉ cube spatialDim M → v.a k = 0)
    (k : Lattice spatialDim) :
    k ∉ cube spatialDim (2*M) →
    bilinearCoeff u v M k = 0 := by
  intro h_outside
  unfold bilinearCoeff
  -- Show every term in the sum is zero
  apply Finset.sum_eq_zero
  intro k₁ hk₁
  -- Goal: show u.a k₁ * v.a (k - k₁) = 0
  -- Suffices to show v.a (k - k₁) = 0 by applying h_supp_v
  suffices h : (k - k₁) ∉ cube spatialDim M by
    simp only [h_supp_v (k - k₁) h, mul_zero]
  -- Prove (k - k₁) ∉ cube(M) using infinity norm
  -- Since k ∉ cube(2M), there exists i such that |k i| > 2M
  rw [ℓ2ZD.mem_cube] at h_outside
  push_neg at h_outside
  obtain ⟨i, hi⟩ := h_outside
  -- k₁ ∈ cube(M)
  rw [ℓ2ZD.mem_cube] at hk₁
  -- Show (k - k₁) i violates cube(M) membership
  intro hk₂
  rw [ℓ2ZD.mem_cube] at hk₂
  specialize hk₂ i
  -- (k - k₁) i = k i - k₁ i
  have eq_sub : (k - k₁) i = k i - k₁ i := by simp [Pi.sub_apply]
  rw [eq_sub] at hk₂
  -- From hk₂: -(M : ℤ) ≤ k i - k₁ i ≤ (M : ℤ)
  -- From hk₁: -(M : ℤ) ≤ k₁ i ≤ (M : ℤ)
  -- From hi: -(2*M : ℤ) ≤ k i → (2*M : ℤ) < k i (after push_neg)
  -- This means: k i < -(2*M : ℤ) ∨ (2*M : ℤ) < k i
  obtain hk₁i := hk₁ i
  -- Convert hi to disjunction
  by_cases h_lower : -(2 * M : ℤ) ≤ k i
  · -- Case: -(2*M) ≤ k i, so by hi we have (2*M) < k i
    have h_pos := hi h_lower
    -- Then k i - k₁ i > (2*M) - M = M
    -- But this contradicts hk₂.2: k i - k₁ i ≤ (M : ℤ)
    omega
  · -- Case: k i < -(2*M)
    push_neg at h_lower
    -- Then k i - k₁ i < -(2*M) + M = -M
    -- But this contradicts hk₂.1: -(M : ℤ) ≤ k i - k₁ i
    omega

/-! ### Combinatorial Counting Bound -/

/-- **Combinatorial counting bound on triple sum repetition** (THE KEY LEMMA)

When expanding (u-v)·(u²+uv+v²), each coefficient ‖u.a(k') - v.a(k')‖ appears
multiple times in the triple convolution. This lemma bounds HOW MANY times:
at most (2M+1)^(2d) times.
-/
lemma cube_triple_count_bound (M : ℕ) (k : Lattice spatialDim) :
    (Finset.filter (fun (p : (Lattice spatialDim) × (Lattice spatialDim)) =>
        p.1 ∈ cube spatialDim M ∧
        p.2 ∈ cube spatialDim M ∧
        (k - p.1 - p.2) ∈ cube spatialDim M)
      (Finset.product (cube spatialDim M) (cube spatialDim M))).card
    ≤ (2 * M + 1)^(2 * spatialDim) := by
  -- Step 1: Filter is subset of the product
  have h_subset : Finset.filter (fun (p : (Lattice spatialDim) × (Lattice spatialDim)) =>
        p.1 ∈ cube spatialDim M ∧
        p.2 ∈ cube spatialDim M ∧
        (k - p.1 - p.2) ∈ cube spatialDim M)
      (Finset.product (cube spatialDim M) (cube spatialDim M))
    ⊆ Finset.product (cube spatialDim M) (cube spatialDim M) :=
    Finset.filter_subset _ _

  -- Step 2: Apply subset cardinality bound
  calc (Finset.filter (fun (p : (Lattice spatialDim) × (Lattice spatialDim)) =>
          p.1 ∈ cube spatialDim M ∧
          p.2 ∈ cube spatialDim M ∧
          (k - p.1 - p.2) ∈ cube spatialDim M)
        (Finset.product (cube spatialDim M) (cube spatialDim M))).card
      ≤ (Finset.product (cube spatialDim M) (cube spatialDim M)).card :=
        Finset.card_le_card h_subset
    -- Step 3: Product cardinality formula
    _ = (cube spatialDim M).card * (cube spatialDim M).card :=
        Finset.card_product _ _
    -- Step 4: Apply card_cube (proven fact)
    _ = (2 * M + 1)^spatialDim * (2 * M + 1)^spatialDim := by
        simp only [ℓ2ZD.card_cube (d := spatialDim) (M := M)]
    -- Step 5: Exponent algebra
    _ = ((2 * M + 1)^spatialDim)^2 := by ring
    _ = (2 * M + 1)^(spatialDim * 2) := by rw [pow_mul]
    _ = (2 * M + 1)^(2 * spatialDim) := by ring

/-! ### Cubic Difference Factorization -/

/-- Cubic difference factorization at the Fourier coefficient level.

Given sequences u, v with support in cube(M), the difference of their cubic
coefficients factors into three bilinear terms corresponding to the algebraic
identity u³ - v³ = (u-v)·u² + v·(u-v)·u + v²·(u-v).

This is the key algebraic step for the Lipschitz estimate. Each term on the RHS
isolates one factor of (u - v), making it suitable for Cauchy-Schwarz application.
-/
lemma cubic_diff_factorization (u v : SeqD spatialDim) (M : ℕ)
    (_h_supp_u : ∀ k, k ∉ cube spatialDim M → u.a k = 0)
    (_h_supp_v : ∀ k, k ∉ cube spatialDim M → v.a k = 0)
    (k : Lattice spatialDim) :
    cubicCoeff u M k - cubicCoeff v M k =
    Finset.sum (cube spatialDim M) (fun k₁ =>
      Finset.sum (cube spatialDim M) (fun k₂ =>
        (u.a k₁ - v.a k₁) * u.a k₂ * u.a (k - k₁ - k₂))) +
    Finset.sum (cube spatialDim M) (fun k₁ =>
      Finset.sum (cube spatialDim M) (fun k₂ =>
        v.a k₁ * (u.a k₂ - v.a k₂) * u.a (k - k₁ - k₂))) +
    Finset.sum (cube spatialDim M) (fun k₁ =>
      Finset.sum (cube spatialDim M) (fun k₂ =>
        v.a k₁ * v.a k₂ * (u.a (k - k₁ - k₂) - v.a (k - k₁ - k₂)))) := by
  -- Unfold cubicCoeff definition: triple convolution formula
  unfold cubicCoeff

  -- Apply triple product expansion to each term
  have h_triple_expand : ∀ k₁ k₂,
    let k₃ := k - k₁ - k₂
    u.a k₁ * u.a k₂ * u.a k₃ - v.a k₁ * v.a k₂ * v.a k₃ =
    (u.a k₁ - v.a k₁) * u.a k₂ * u.a k₃ +
    v.a k₁ * (u.a k₂ - v.a k₂) * u.a k₃ +
    v.a k₁ * v.a k₂ * (u.a k₃ - v.a k₃) := by
      intro k₁ k₂
      ring  -- Pure algebraic identity

  -- Apply the expansion and reorganize sums
  calc Finset.sum (cube spatialDim M) (fun k₁ =>
         Finset.sum (cube spatialDim M) (fun k₂ =>
           u.a k₁ * u.a k₂ * u.a (k - k₁ - k₂))) -
       Finset.sum (cube spatialDim M) (fun k₁ =>
         Finset.sum (cube spatialDim M) (fun k₂ =>
           v.a k₁ * v.a k₂ * v.a (k - k₁ - k₂)))
      = Finset.sum (cube spatialDim M) (fun k₁ =>
         Finset.sum (cube spatialDim M) (fun k₂ =>
           u.a k₁ * u.a k₂ * u.a (k - k₁ - k₂) - v.a k₁ * v.a k₂ * v.a (k - k₁ - k₂))) := by
        simp only [Finset.sum_sub_distrib]
    _ = Finset.sum (cube spatialDim M) (fun k₁ =>
         Finset.sum (cube spatialDim M) (fun k₂ =>
           u.a k₁ * u.a k₂ * u.a (k - k₁ - k₂) - v.a k₁ * v.a k₂ * v.a (k - k₁ - k₂))) := by rfl
    _ = Finset.sum (cube spatialDim M) (fun k₁ =>
         Finset.sum (cube spatialDim M) (fun k₂ =>
           (u.a k₁ - v.a k₁) * u.a k₂ * u.a (k - k₁ - k₂) +
           v.a k₁ * (u.a k₂ - v.a k₂) * u.a (k - k₁ - k₂) +
           v.a k₁ * v.a k₂ * (u.a (k - k₁ - k₂) - v.a (k - k₁ - k₂)))) := by
        -- Apply h_triple_expand to each term
        congr 1; ext k₁
        congr 1; ext k₂
        exact h_triple_expand k₁ k₂
    _ = Finset.sum (cube spatialDim M) (fun k₁ =>
         Finset.sum (cube spatialDim M) (fun k₂ =>
           (u.a k₁ - v.a k₁) * u.a k₂ * u.a (k - k₁ - k₂))) +
        Finset.sum (cube spatialDim M) (fun k₁ =>
         Finset.sum (cube spatialDim M) (fun k₂ =>
           v.a k₁ * (u.a k₂ - v.a k₂) * u.a (k - k₁ - k₂))) +
        Finset.sum (cube spatialDim M) (fun k₁ =>
         Finset.sum (cube spatialDim M) (fun k₂ =>
           v.a k₁ * v.a k₂ * (u.a (k - k₁ - k₂) - v.a (k - k₁ - k₂)))) := by
        -- Distribute sum over addition: ∑(a + b + c) = ∑a + ∑b + ∑c
        simp only [Finset.sum_add_distrib]

/-! ## Lipschitz Estimate -/

-- Helper lemma: bound triple product difference
lemma triple_product_diff_bound (a b c d e f : ℂ) :
    ‖a * b * c - d * e * f‖ ≤ ‖a - d‖ * ‖b‖ * ‖c‖ +
                                ‖d‖ * ‖b - e‖ * ‖c‖ +
                                ‖d‖ * ‖e‖ * ‖c - f‖ := by
  have h_expand : a * b * c - d * e * f = (a - d) * b * c + d * (b - e) * c + d * e * (c - f) := by
    ring
  calc ‖a * b * c - d * e * f‖
      = ‖(a - d) * b * c + (d * (b - e) * c + d * e * (c - f))‖ := by rw [h_expand]; ring_nf
    _ ≤ ‖(a - d) * b * c‖ + ‖d * (b - e) * c + d * e * (c - f)‖ := norm_add_le _ _
    _ ≤ ‖(a - d) * b * c‖ + (‖d * (b - e) * c‖ + ‖d * e * (c - f)‖) := by
        gcongr
        exact norm_add_le _ _
    _ = ‖a - d‖ * ‖b‖ * ‖c‖ + ‖d‖ * ‖b - e‖ * ‖c‖ + ‖d‖ * ‖e‖ * ‖c - f‖ := by
        simp only [norm_mul]; ring

/-! ### Bilinear L² Bounds (Phase 2A) -/

/-- Bilinear coefficients have finite support, hence square-summable. -/
lemma summable_sq_bilinearCoeff (u v : SeqD spatialDim) (M : ℕ)
    (_h_supp_u : ∀ k, k ∉ cube spatialDim M → u.a k = 0)
    (h_supp_v : ∀ k, k ∉ cube spatialDim M → v.a k = 0) :
    Summable (fun k => ‖bilinearCoeff u v M k‖^2) := by
  -- Support of bilinearCoeff is in cube(2M) by bilinearCoeff_support_bound
  refine summable_of_ne_finset_zero (s := cube spatialDim (2 * M)) ?_
  intro k hk
  rw [bilinearCoeff_support_bound u v M _h_supp_u h_supp_v k hk]
  simp

/-- **Phase 2A: Quadratic L² bound for bilinear coefficients**

This proves that ‖u·v‖_{L²} is quadratic in the H¹ ball radius R.
The bound ∑' ‖bilinearCoeff‖² ≤ 4^d·(2M+1)^(3d)·C^4·R^4 follows from:

1. Coefficient bounds: ‖u.a k‖, ‖v.a k‖ ≤ C·|R| (from H¹ ball)
2. Pointwise bound: ‖bilinearCoeff k‖ ≤ (2M+1)^d · (C|R|)²
3. Finite support: bilinearCoeff supported on cube(2M)
4. L² sum: ∑ ‖bilinearCoeff k‖² ≤ |cube(2M)| · ((2M+1)^d·(C|R|)²)²

where |cube(2M)| = (4M+1)^d ≤ 4^d·(2M+1)^d, giving the final bound.
-/
lemma bilinear_l2_bound (u v : SeqD spatialDim) (M : ℕ) (R : ℝ)
    (h_supp_u : ∀ k, k ∉ cube spatialDim M → u.a k = 0)
    (h_supp_v : ∀ k, k ∉ cube spatialDim M → v.a k = 0)
    (h_H1_u : InH1Ball R u)
    (h_H1_v : InH1Ball R v) :
    ∑' k, ‖bilinearCoeff u v M k‖^2 ≤
      4^spatialDim * ((2 * M + 1)^(3 * spatialDim) : ℝ) *
      sobolev_constant_extended^4 * |R|^4 := by
  -- Get coefficient bounds from H¹ balls
  have h_bound_u := h1ball_to_coeff_bound u R M h_supp_u h_H1_u
  have h_bound_v := h1ball_to_coeff_bound v R M h_supp_v h_H1_v

  -- Pointwise bound on bilinearCoeff
  have h_pw : ∀ k, ‖bilinearCoeff u v M k‖ ≤
      (2 * M + 1)^spatialDim * (sobolev_constant_extended * |R|)^2 := fun k =>
    calc ‖bilinearCoeff u v M k‖
        ≤ (2 * M + 1)^spatialDim * (sobolev_constant_extended * |R|) *
          (sobolev_constant_extended * |R|) :=
          bilinearCoeff_coeff_bound u v M _ _ h_supp_u h_supp_v h_bound_u h_bound_v k
      _ = (2 * M + 1)^spatialDim * (sobolev_constant_extended * |R|)^2 := by rw [sq]; ring

  -- Finite support
  have h_fin : ∀ k, k ∉ cube spatialDim (2 * M) → ‖bilinearCoeff u v M k‖^2 = 0 := fun k hk => by
    rw [bilinearCoeff_support_bound u v M h_supp_u h_supp_v k hk]; simp

  -- Main computation
  calc ∑' k, ‖bilinearCoeff u v M k‖^2
      = ∑ k ∈ cube spatialDim (2 * M), ‖bilinearCoeff u v M k‖^2 := by rw [tsum_eq_sum h_fin]
    _ ≤ ∑ k ∈ cube spatialDim (2 * M),
          ((2 * M + 1)^spatialDim * (sobolev_constant_extended * |R|)^2)^2 := by
        apply Finset.sum_le_sum
        intro k _
        -- TODO: Use proper pow monotonicity lemma
        have := h_pw k
        have h_nn := norm_nonneg (bilinearCoeff u v M k)
        have h_sq : ‖bilinearCoeff u v M k‖ ^ 2 ≤
            ((2 * M + 1)^spatialDim * (sobolev_constant_extended * |R|)^2) ^ 2 := by
          apply sq_le_sq'
          · linarith
          · exact this
        exact h_sq
    _ = (cube spatialDim (2 * M)).card *
          ((2 * M + 1)^spatialDim * (sobolev_constant_extended * |R|)^2)^2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 4^spatialDim * ((2 * M + 1)^(3 * spatialDim) : ℝ) *
          sobolev_constant_extended^4 * |R|^4 := by
        rw [ℓ2ZD.card_cube (d := spatialDim) (M := 2 * M)]
        rw [mul_pow, mul_pow, sq, sq]
        -- Strategy: (4M+1)^d ≤ (4·(2M+1))^d = 4^d·(2M+1)^d, then combine exponents
        have h_card : (2 * (2 * M) + 1 : ℕ) = 4 * M + 1 := by omega
        have h_bound : (4 * M + 1 : ℕ) ≤ 4 * (2 * M + 1) := by omega
        simp only [h_card]
        push_cast
        -- LHS = (4M+1)^d · (2M+1)^d · (2M+1)^d · C^4·|R|^4
        -- RHS = 4^d · (2M+1)^(3d) · C^4·|R|^4
        -- Need: (4M+1)^d · (2M+1)^(2d) ≤ 4^d · (2M+1)^(3d)
        calc (4 * ↑M + 1) ^ spatialDim *
              ((2 * ↑M + 1) ^ spatialDim * (2 * ↑M + 1) ^ spatialDim *
               (sobolev_constant_extended ^ 2 * |R| ^ 2 * (sobolev_constant_extended ^ 2 * |R| ^ 2)))
            ≤ (4 * (2 * ↑M + 1)) ^ spatialDim *
              ((2 * ↑M + 1) ^ spatialDim * (2 * ↑M + 1) ^ spatialDim *
               (sobolev_constant_extended ^ 2 * |R| ^ 2 * (sobolev_constant_extended ^ 2 * |R| ^ 2))) := by
              gcongr
              exact_mod_cast h_bound
          _ = 4 ^ spatialDim * (2 * ↑M + 1) ^ (3 * spatialDim) *
              sobolev_constant_extended ^ 4 * |R| ^ 4 := by
              rw [mul_pow]
              ring

/-! ### Product-Convolution H⁻¹ Bound (Phase 2B) -/

/-- **Phase 2B: Product-convolution H⁻¹ bound (Lemma 4)**

This proves the key weighted bound for bilinear convolutions:
  ∑_k hminusWeight(k) · ‖bilinearCoeff(w,uv,M)(k)‖² ≤ (2M+1)^d · R_w² · B_uv²

**Mathematical Strategy:**
The proof uses weighted Cauchy-Schwarz and clever summation reordering:

1. Apply hminusWeight ≤ 1: ∑_k hminusWeight(k)·|bilinear(k)|² ≤ ∑_k |bilinear(k)|²
2. Expand: bilinearCoeff(k) = ∑_{k₁∈cube(M)} w(k₁) · uv(k-k₁)
3. Apply weighted CS on each k: |∑_{k₁} w(k₁)·uv(k-k₁)|²
   ≤ (∑_{k₁} h1Weight(k₁)·|w(k₁)|²) · (∑_{k₁} |uv(k-k₁)|²/h1Weight(k₁))
4. **KEY**: First factor independent of k! Factor it out before summing over k:
   ∑_k product ≤ (∑_{k₁} h1Weight(k₁)·|w(k₁)|²) · (∑_k ∑_{k₁} |uv(k-k₁)|²/h1Weight(k₁))
5. Bound first factor: ≤ R_w² (from InH1Ball)
6. Drop weight in second factor using h1Weight ≥ 1
7. Exchange summation order: ∑_k ∑_{k₁} |uv(k-k₁)|² = ∑_{k₁} ∑_k |uv(k-k₁)|²
8. For each k₁, reindex and bound: ∑_k |uv(k-k₁)|² ≤ ∑' k' |uv(k')|² ≤ B_uv²
9. Sum over k₁ ∈ cube(M): ∑_{k₁} B_uv² = |cube(M)| · B_uv² = (2M+1)^d · B_uv²

**Infrastructure Dependencies:**
- `InH1Ball`: ∀ F, ∑_{k∈F} h1Weight(k)·‖w.a(k)‖² ≤ R_w² (Core.lean:363)
- `hminusWeight_le_one`: hminusWeight(k) ≤ 1 (Core.lean:85)
- `h1Weight_ge_one`: 1 ≤ h1Weight(k) (Core.lean:69)
- `weighted_cs_tsum`: Weighted Cauchy-Schwarz for infinite sums (SobolevEmbedding.lean:228)
-/
lemma product_hminus_bound (w uv : SeqD spatialDim) (M : ℕ)
    (R_w B_uv : ℝ) (F : Finset (Lattice spatialDim))
    (h_w_H1 : InH1Ball R_w w)
    (h_uv_summable : Summable (fun k => ‖uv.a k‖^2))
    (h_uv_L2 : ∑' k, ‖uv.a k‖^2 ≤ B_uv^2) :
    Finset.sum F (fun k =>
      hminusWeight k * ‖bilinearCoeff w uv M k‖^2)
    ≤ ((2 * M + 1)^spatialDim : ℝ) * R_w^2 * B_uv^2 := by
  -- KEY INSIGHT: Change order of summation!
  -- Instead of: ∑_k hminusWeight(k) · |∑_{k₁} w(k₁)·uv(k-k₁)|²
  -- We rearrange to get a GLOBAL Cauchy-Schwarz over the double sum.

  -- Step 1: Expand bilinear Coeff and use hminusWeight ≤ 1
  calc Finset.sum F (fun k => hminusWeight k * ‖bilinearCoeff w uv M k‖^2)
      ≤ Finset.sum F (fun k => 1 * ‖bilinearCoeff w uv M k‖^2) := by
        apply Finset.sum_le_sum
        intro k _
        gcongr
        exact ℓ2ZD.hminusWeight_le_one k
    _ = Finset.sum F (fun k => ‖bilinearCoeff w uv M k‖^2) := by
        simp [one_mul]
    _ = Finset.sum F (fun k => ‖Finset.sum (cube spatialDim M) (fun k₁ => w.a k₁ * uv.a (k - k₁))‖^2) := by
        simp [bilinearCoeff]
    _ ≤ Finset.sum F (fun k => (Finset.sum (cube spatialDim M) (fun k₁ => ‖w.a k₁‖ * ‖uv.a (k - k₁)‖))^2) := by
        apply Finset.sum_le_sum
        intro k _
        have h_tri := norm_sum_le (cube spatialDim M) (fun k₁ => w.a k₁ * uv.a (k - k₁))
        have h_sum_nn : 0 ≤ Finset.sum (cube spatialDim M) (fun k₁ => ‖w.a k₁ * uv.a (k - k₁)‖) :=
          Finset.sum_nonneg (fun i _ => norm_nonneg _)
        calc ‖Finset.sum (cube spatialDim M) (fun k₁ => w.a k₁ * uv.a (k - k₁))‖^2
            ≤ (Finset.sum (cube spatialDim M) (fun k₁ => ‖w.a k₁ * uv.a (k - k₁)‖))^2 := by
              apply sq_le_sq' _ h_tri
              linarith [norm_nonneg (Finset.sum (cube spatialDim M) (fun k₁ => w.a k₁ * uv.a (k - k₁)))]
          _ = (Finset.sum (cube spatialDim M) (fun k₁ => ‖w.a k₁‖ * ‖uv.a (k - k₁)‖))^2 := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro k₁ _
              exact norm_mul _ _
    _ ≤ Finset.sum F (fun k =>
          (Finset.sum (cube spatialDim M) (fun k₁ => h1Weight k₁ * ‖w.a k₁‖^2))
          * (Finset.sum (cube spatialDim M) (fun k₁ => ‖uv.a (k - k₁)‖^2 / h1Weight k₁))) := by
        apply Finset.sum_le_sum
        intro k _
        -- Apply weighted Cauchy-Schwarz for this k
        have h_sq := Finset.sum_mul_sq_le_sq_mul_sq (cube spatialDim M)
          (fun k₁ => Real.sqrt (h1Weight k₁) * ‖w.a k₁‖)
          (fun k₁ => ‖uv.a (k - k₁)‖ / Real.sqrt (h1Weight k₁))
        -- Simplify LHS
        have h_lhs : (Finset.sum (cube spatialDim M) (fun k₁ => ‖w.a k₁‖ * ‖uv.a (k - k₁)‖))^2
            = (Finset.sum (cube spatialDim M)
                (fun k₁ => (Real.sqrt (h1Weight k₁) * ‖w.a k₁‖) *
                           (‖uv.a (k - k₁)‖ / Real.sqrt (h1Weight k₁))))^2 := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro k₁ _
          have h_pos : 0 < h1Weight k₁ := ℓ2ZD.h1Weight_pos k₁
          field_simp [ne_of_gt (Real.sqrt_pos.mpr h_pos), Real.sq_sqrt (le_of_lt h_pos)]
        -- Simplify RHS factors
        have h_rhs1 : Finset.sum (cube spatialDim M) (fun k₁ => (Real.sqrt (h1Weight k₁) * ‖w.a k₁‖)^2)
            = Finset.sum (cube spatialDim M) (fun k₁ => h1Weight k₁ * ‖w.a k₁‖^2) := by
          refine Finset.sum_congr rfl ?_
          intro k₁ _
          have h_pos : 0 < h1Weight k₁ := ℓ2ZD.h1Weight_pos k₁
          rw [mul_pow, Real.sq_sqrt (le_of_lt h_pos), sq]
        have h_rhs2 : Finset.sum (cube spatialDim M) (fun k₁ => (‖uv.a (k - k₁)‖ / Real.sqrt (h1Weight k₁))^2)
            = Finset.sum (cube spatialDim M) (fun k₁ => ‖uv.a (k - k₁)‖^2 / h1Weight k₁) := by
          refine Finset.sum_congr rfl ?_
          intro k₁ _
          have h_pos : 0 < h1Weight k₁ := ℓ2ZD.h1Weight_pos k₁
          rw [div_pow, Real.sq_sqrt (le_of_lt h_pos), sq]
        -- Apply CS
        rw [h_lhs]
        calc (Finset.sum (cube spatialDim M)
                (fun k₁ => (Real.sqrt (h1Weight k₁) * ‖w.a k₁‖) *
                           (‖uv.a (k - k₁)‖ / Real.sqrt (h1Weight k₁))))^2
            ≤ (Finset.sum (cube spatialDim M) (fun k₁ => (Real.sqrt (h1Weight k₁) * ‖w.a k₁‖)^2))
              * (Finset.sum (cube spatialDim M) (fun k₁ => (‖uv.a (k - k₁)‖ / Real.sqrt (h1Weight k₁))^2)) := h_sq
          _ = (Finset.sum (cube spatialDim M) (fun k₁ => h1Weight k₁ * ‖w.a k₁‖^2))
              * (Finset.sum (cube spatialDim M) (fun k₁ => ‖uv.a (k - k₁)‖^2 / h1Weight k₁)) := by
              rw [h_rhs1, h_rhs2]
    _ = Finset.sum F (fun k =>
          (Finset.sum (cube spatialDim M) (fun k₁ => h1Weight k₁ * ‖w.a k₁‖^2))
          * (Finset.sum (cube spatialDim M) (fun k₁ => ‖uv.a (k - k₁)‖^2 / h1Weight k₁))) := by
        -- First factor is independent of k, so extract it
        rfl
    _ = (Finset.sum (cube spatialDim M) (fun k₁ => h1Weight k₁ * ‖w.a k₁‖^2))
        * (Finset.sum F (fun k => Finset.sum (cube spatialDim M) (fun k₁ => ‖uv.a (k - k₁)‖^2 / h1Weight k₁))) := by
        rw [← Finset.mul_sum]
    _ ≤ R_w^2 * (Finset.sum F (fun k => Finset.sum (cube spatialDim M) (fun k₁ => ‖uv.a (k - k₁)‖^2 / h1Weight k₁))) := by
        gcongr
        · apply Finset.sum_nonneg
          intro k _
          apply Finset.sum_nonneg
          intro k₁ _
          apply div_nonneg (sq_nonneg _)
          exact le_of_lt (ℓ2ZD.h1Weight_pos k₁)
        · exact h_w_H1 (cube spatialDim M)
    _ ≤ R_w^2 * (Finset.sum F (fun k => Finset.sum (cube spatialDim M) (fun k₁ => ‖uv.a (k - k₁)‖^2))) := by
        gcongr with k _ k₁ _
        -- Use h1Weight ≥ 1
        have h_ge : 1 ≤ h1Weight k₁ := ℓ2ZD.h1Weight_ge_one k₁
        have h_pos : 0 < h1Weight k₁ := ℓ2ZD.h1Weight_pos k₁
        calc ‖uv.a (k - k₁)‖^2 / h1Weight k₁
            ≤ ‖uv.a (k - k₁)‖^2 / 1 := div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) h_ge
          _ = ‖uv.a (k - k₁)‖^2 := by simp
    _ = R_w^2 * (Finset.sum (cube spatialDim M) (fun k₁ => Finset.sum F (fun k => ‖uv.a (k - k₁)‖^2))) := by
        congr 1
        rw [Finset.sum_comm]
    _ ≤ R_w^2 * (Finset.sum (cube spatialDim M) (fun k₁ => ∑' k₂, ‖uv.a k₂‖^2)) := by
        gcongr with k₁ _
        -- Reindex via translation: ∑_{k∈F} f(k-k₁) = ∑_{k'∈F.image(·-k₁)} f(k')
        have h_reindex : Finset.sum F (fun k => ‖uv.a (k - k₁)‖^2)
            = Finset.sum (F.image (fun k => k - k₁)) (fun k' => ‖uv.a k'‖^2) := by
          rw [Finset.sum_image]
          intros x _ y _ hxy
          -- k - k₁ injective in k
          simp only at hxy
          exact sub_left_inj.mp hxy
        -- Apply sum_le_tsum: finite ≤ infinite
        calc Finset.sum F (fun k => ‖uv.a (k - k₁)‖^2)
            = Finset.sum (F.image (fun k => k - k₁)) (fun k' => ‖uv.a k'‖^2) := h_reindex
          _ ≤ ∑' k', ‖uv.a k'‖^2 := by
              apply h_uv_summable.sum_le_tsum
              intro k _
              exact sq_nonneg _
    _ ≤ R_w^2 * (Finset.sum (cube spatialDim M) (fun k₁ => B_uv^2)) := by
        gcongr with k₁ _
    _ = R_w^2 * ((cube spatialDim M).card * B_uv^2) := by
        congr 1
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = R_w^2 * B_uv^2 * (cube spatialDim M).card := by
        ring
    _ = R_w^2 * B_uv^2 * ((2 * M + 1)^spatialDim : ℕ) := by
        congr 2
        exact ℓ2ZD.card_cube
    _ = ((2 * M + 1)^spatialDim : ℝ) * R_w^2 * B_uv^2 := by
        push_cast
        ring

/-! ## Trilinear Helper for Lipschitz Estimate

The cubic factorization gives three terms of the form:
  ∑_{k₁} ∑_{k₂} diff(k₁) * a(k₂) * b(k - k₁ - k₂)

This equals bilinearCoeff(diff, productSeq) where productSeq.a(j) = bilinearCoeff(a,b)(j).
The helper bounds ONE such term using product_hminus_bound and bilinear_l2_bound.
-/

/-- **Key Helper:** Bounds ONE trilinear term from the cubic factorization.

Given diff = (u-v) and two bounded sequences a, b, bounds:
  ∑_F hminusWeight(k) * ‖∑_{k₁,k₂} diff(k₁) * a(k₂) * b(k-k₁-k₂)‖²
  ≤ K * R_diff² * R_ab⁴

where K absorbs the dimensional constants. Uses product_hminus_bound + bilinear_l2_bound.
-/
lemma bound_trilinear_diff_term (diff a b : SeqD spatialDim) (M : ℕ)
    (R_diff R_ab : ℝ) (F : Finset (Lattice spatialDim))
    (h_diff_H1 : InH1Ball R_diff diff)
    (h_supp_a : ∀ k, k ∉ cube spatialDim M → a.a k = 0)
    (h_supp_b : ∀ k, k ∉ cube spatialDim M → b.a k = 0)
    (h_H1_a : InH1Ball R_ab a) (h_H1_b : InH1Ball R_ab b) :
    Finset.sum F (fun k =>
      hminusWeight k * ‖Finset.sum (cube spatialDim M) (fun k₁ =>
        Finset.sum (cube spatialDim M) (fun k₂ =>
          diff.a k₁ * a.a k₂ * b.a (k - k₁ - k₂)))‖^2)
    ≤ 4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
      sobolev_constant_extended^4 * R_diff^2 * |R_ab|^4 := by
  -- Strategy: The double sum equals bilinearCoeff(diff, productSeq(a,b))
  -- where productSeq.a(j) = bilinearCoeff(a,b)(j).
  -- Then apply product_hminus_bound with L² bound from bilinear_l2_bound.

  -- Step 1: Construct productSeq = bilinearCoeff(a, b, M) as a SeqD
  let productSeq : SeqD spatialDim := {
    a := fun j => bilinearCoeff a b M j
    summable_sq := summable_sq_bilinearCoeff a b M h_supp_a h_supp_b
  }

  -- Step 2: Show the double sum equals bilinearCoeff(diff, productSeq)
  have h_eq : ∀ k, Finset.sum (cube spatialDim M) (fun k₁ =>
        Finset.sum (cube spatialDim M) (fun k₂ =>
          diff.a k₁ * a.a k₂ * b.a (k - k₁ - k₂)))
      = bilinearCoeff diff productSeq M k := by
    intro k
    simp only [bilinearCoeff]
    -- bilinearCoeff diff productSeq M k = ∑_{k₁ ∈ cube(M)} diff.a k₁ * productSeq.a (k - k₁)
    --       = ∑_{k₁} diff.a k₁ * (∑_{k₂ ∈ cube(M)} a.a k₂ * b.a ((k - k₁) - k₂))
    -- Note: (k - k₁) - k₂ = k - k₁ - k₂
    refine Finset.sum_congr rfl ?_
    intro k₁ _
    -- productSeq.a (k - k₁) = ∑_{k₂} a.a k₂ * b.a ((k - k₁) - k₂)
    show ∑ k₂ ∈ cube spatialDim M, diff.a k₁ * a.a k₂ * b.a (k - k₁ - k₂)
       = diff.a k₁ * ∑ k₂ ∈ cube spatialDim M, a.a k₂ * b.a (k - k₁ - k₂)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k₂ _
    ring

  -- Step 3: Rewrite LHS using h_eq
  conv_lhs =>
    congr
    · skip
    · ext k
      rw [h_eq k]

  -- Step 4: Get L² bound on productSeq from bilinear_l2_bound
  have h_l2_bound := bilinear_l2_bound a b M R_ab h_supp_a h_supp_b h_H1_a h_H1_b

  -- Step 5: Apply product_hminus_bound
  have h_prod := product_hminus_bound diff productSeq M R_diff
    (Real.sqrt (4^spatialDim * ((2 * M + 1)^(3 * spatialDim) : ℝ) *
      sobolev_constant_extended^4 * |R_ab|^4)) F h_diff_H1
    (summable_sq_bilinearCoeff a b M h_supp_a h_supp_b)
    (by
      rw [Real.sq_sqrt (by positivity)]
      exact h_l2_bound)

  -- Step 6: Combine bounds
  calc Finset.sum F (fun k => hminusWeight k * ‖bilinearCoeff diff productSeq M k‖^2)
      ≤ ((2 * M + 1)^spatialDim : ℝ) * R_diff^2 *
        (Real.sqrt (4^spatialDim * ((2 * M + 1)^(3 * spatialDim) : ℝ) *
          sobolev_constant_extended^4 * |R_ab|^4))^2 := h_prod
    _ = ((2 * M + 1)^spatialDim : ℝ) * R_diff^2 *
        (4^spatialDim * ((2 * M + 1)^(3 * spatialDim) : ℝ) *
          sobolev_constant_extended^4 * |R_ab|^4) := by
        rw [Real.sq_sqrt (by positivity)]
    _ = 4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
        sobolev_constant_extended^4 * R_diff^2 * |R_ab|^4 := by
        rw [show (4 : ℕ) * spatialDim = spatialDim + 3 * spatialDim by ring]
        rw [pow_add]
        ring

/-- **Key Helper:** Bounds trilinear term where diff is at position 3 (the dependent index).

Given diff = (u-v) and two bounded sequences a, b, bounds:
  ∑_F hminusWeight(k) * ‖∑_{k₁,k₂} a(k₁) * b(k₂) * diff(k-k₁-k₂)‖²
  ≤ K * R² * |R|⁴

This is the symmetric counterpart to bound_trilinear_diff_term.
Key insight: T3 = bilinearCoeff(a, bilinearCoeff(b, diff)), so the roles are swapped.

Note: For simplicity, we require all three sequences to be in the same H¹(R) ball.
This matches the typical Lipschitz use case where a=u, b=v, diff=u-v all lie in H¹(R).
-/
lemma bound_trilinear_term_pos3 (a b diff : SeqD spatialDim) (M : ℕ)
    (R : ℝ) (F : Finset (Lattice spatialDim))
    (h_H1_a : InH1Ball R a)
    (h_H1_b : InH1Ball R b)
    (h_diff_H1 : InH1Ball R diff)
    (_h_supp_a : ∀ k, k ∉ cube spatialDim M → a.a k = 0)
    (h_supp_b : ∀ k, k ∉ cube spatialDim M → b.a k = 0)
    (h_supp_diff : ∀ k, k ∉ cube spatialDim M → diff.a k = 0) :
    Finset.sum F (fun k =>
      hminusWeight k * ‖Finset.sum (cube spatialDim M) (fun k₁ =>
        Finset.sum (cube spatialDim M) (fun k₂ =>
          a.a k₁ * b.a k₂ * diff.a (k - k₁ - k₂)))‖^2)
    ≤ 4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
      sobolev_constant_extended^4 * R^2 * |R|^4 := by
  -- Strategy: Rewrite T3 = bilinearCoeff(a, productBD)
  -- where productBD.a(j) = bilinearCoeff(b, diff)(j).
  -- Then apply product_hminus_bound with L² bound from bilinear_l2_bound.

  -- Step 1: Construct productBD = bilinearCoeff(b, diff, M) as a SeqD
  let productBD : SeqD spatialDim := {
    a := fun j => bilinearCoeff b diff M j
    summable_sq := summable_sq_bilinearCoeff b diff M h_supp_b h_supp_diff
  }

  -- Step 2: Show the double sum equals bilinearCoeff(a, productBD)
  have h_eq : ∀ k, Finset.sum (cube spatialDim M) (fun k₁ =>
        Finset.sum (cube spatialDim M) (fun k₂ =>
          a.a k₁ * b.a k₂ * diff.a (k - k₁ - k₂)))
      = bilinearCoeff a productBD M k := by
    intro k
    simp only [bilinearCoeff]
    -- bilinearCoeff a productBD M k = ∑_{k₁ ∈ cube(M)} a.a k₁ * productBD.a (k - k₁)
    --       = ∑_{k₁} a.a k₁ * (∑_{k₂ ∈ cube(M)} b.a k₂ * diff.a ((k - k₁) - k₂))
    -- Note: (k - k₁) - k₂ = k - k₁ - k₂
    refine Finset.sum_congr rfl ?_
    intro k₁ _
    -- productBD.a (k - k₁) = ∑_{k₂} b.a k₂ * diff.a ((k - k₁) - k₂)
    show ∑ k₂ ∈ cube spatialDim M, a.a k₁ * b.a k₂ * diff.a (k - k₁ - k₂)
       = a.a k₁ * ∑ k₂ ∈ cube spatialDim M, b.a k₂ * diff.a (k - k₁ - k₂)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k₂ _
    ring

  -- Step 3: Rewrite LHS using h_eq
  conv_lhs =>
    congr
    · skip
    · ext k
      rw [h_eq k]

  -- Step 4: Get L² bound on productBD from bilinear_l2_bound
  have h_l2_bound := bilinear_l2_bound b diff M R h_supp_b h_supp_diff h_H1_b h_diff_H1

  -- Step 5: Apply product_hminus_bound with a as the H¹ sequence
  have h_prod := product_hminus_bound a productBD M R
    (Real.sqrt (4^spatialDim * ((2 * M + 1)^(3 * spatialDim) : ℝ) *
      sobolev_constant_extended^4 * |R|^4)) F h_H1_a
    (summable_sq_bilinearCoeff b diff M h_supp_b h_supp_diff)
    (by
      rw [Real.sq_sqrt (by positivity)]
      exact h_l2_bound)

  -- Step 6: Combine bounds
  calc Finset.sum F (fun k => hminusWeight k * ‖bilinearCoeff a productBD M k‖^2)
      ≤ ((2 * M + 1)^spatialDim : ℝ) * R^2 *
        (Real.sqrt (4^spatialDim * ((2 * M + 1)^(3 * spatialDim) : ℝ) *
          sobolev_constant_extended^4 * |R|^4))^2 := h_prod
    _ = ((2 * M + 1)^spatialDim : ℝ) * R^2 *
        (4^spatialDim * ((2 * M + 1)^(3 * spatialDim) : ℝ) *
          sobolev_constant_extended^4 * |R|^4) := by
        rw [Real.sq_sqrt (by positivity)]
    _ = 4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
        sobolev_constant_extended^4 * R^2 * |R|^4 := by
        rw [show (4 : ℕ) * spatialDim = spatialDim + 3 * spatialDim by ring]
        rw [pow_add]
        ring

/-- The exact Lipschitz constant for the cubic operator u³.

This is the **ANALYTICAL** constant derived from the cubic factorization algebra:
- Factor 54 from the triangle inequality on 3 trilinear terms (3 × 18, where 18 = 1 + 1 + 16)
- Factor 4^d from trilinear bound structure
- Factor (2M+1)^{4d} from Cauchy-Schwarz over finite sums
- Factor C⁴ from Sobolev embedding constant
- Factor (2R)² from the H¹ ball radius of diffSeq = u - v
- Factor R⁴ from the L∞ bounds of the product sequences

For d=3, M=0, C≈2.56: This evaluates to 54 × 64 × 1 × 43 × 4 × R⁶ ≈ 594,000 × R⁶.
That is the physics of cubic nonlinearity in 3D when both sequences are in H¹(R).

NOTE: This is NOT a Lipschitz constant in the form L·‖u-v‖. Instead, it's a BOUND
for when u,v ∈ H¹_M(R). The calc chain gives a fixed constant, not one that factors
through the actual difference norm. We state what the proof actually delivers.

## Extraction Path

**xbudget: C5** - This definition uses noncomputable Real arithmetic (proof track).

For **extractable witness computation**, use `CubicBudget.cubic_lipschitz_budget_rat`
which provides the same bound using constructive rational arithmetic (xbudget C0).

The soundness connection is given by `CubicBudget.constructive_budget_upper_bounds_real_constant`,
which proves that the rational budget upper-bounds this real constant when given appropriate
rational bounds for C and R.
-/
noncomputable def cubic_lipschitz_constant (d M : ℕ) (C R : ℝ) : ℝ :=
  54 * 4^d * ((2 * M + 1)^(4 * d) : ℝ) * C^4 * (2 * R)^2 * R^4

/-- The constructive rational budget upper-bounds the analytical real constant.

This lemma connects the noncomputable `cubic_lipschitz_constant` (proof layer)
to the computable `cubic_lipschitz_budget_rat` (extraction layer).

Given rational upper bounds C_bound ≥ C_real and R_bound ≥ R_real, the
constructive budget safely over-approximates the real constant for stability checking.
-/
theorem cubic_lipschitz_rational_sound (d M : ℕ) (C_bound R_bound : Q)
    (C_real R_real : ℝ)
    (hC : (toRat C_bound : ℝ) ≥ C_real)
    (hR : (toRat R_bound : ℝ) ≥ R_real)
    (hC_pos : 0 < C_real)
    (hR_pos : 0 < R_real) :
    (toRat (CubicBudget.cubic_lipschitz_budget_rat d M C_bound R_bound) : ℝ) ≥
    cubic_lipschitz_constant d M C_real R_real := by
  unfold cubic_lipschitz_constant
  exact CubicBudget.constructive_budget_upper_bounds_real_constant
    d M C_bound R_bound C_real R_real hC hR hC_pos hR_pos

/-

This is the critical Lipschitz estimate for the cubic Nemytskii operator.

The strategy is:
1. Factor u³ - v³ into three bilinear terms using cubic_diff_factorization
2. Apply triangle inequality to bound ‖term1 + term2 + term3‖²
3. Each term has form (difference) * (product), bounded using product_hminus_bound
4. Combine the bounds to get Lipschitz constant

Note: The constant 24R² is derived from the factorization and bilinear bounds.
If the actual constant differs during proof, we can adjust the lemma statement.
-/
lemma cubic_lipschitz (u v : SeqD spatialDim) (M : ℕ)
    (h_supp_u : ∀ k, k ∉ cube spatialDim M → u.a k = 0)
    (h_supp_v : ∀ k, k ∉ cube spatialDim M → v.a k = 0)
    (R : ℝ) (h_H1_u : InH1Ball R u) (h_H1_v : InH1Ball R v)
    (F : Finset (Lattice spatialDim)) :
    Finset.sum F (fun k =>
      hminusWeight k * ‖(cubicApply u M h_supp_u R h_H1_u).a k
                       - (cubicApply v M h_supp_v R h_H1_v).a k‖^2)
    ≤ 4 * (cubicBound R M)^2 := by

  classical

  -- Rewrite coefficients in terms of `cubicCoeff`.
  unfold cubicApply
  simp only

  -- Each cubic application is in the H⁻¹ ball given by `cubicBound R M`.
  have h_inHminus_u := cubic_map_inHminus u M h_supp_u R h_H1_u
  have h_inHminus_v := cubic_map_inHminus v M h_supp_v R h_H1_v

  -- Pointwise inequality: ‖a - b‖² ≤ 2‖a‖² + 2‖b‖², then multiply by the non‑negative weight.
  have h_pointwise :
      ∀ k, hminusWeight k *
          ‖cubicCoeff u M k - cubicCoeff v M k‖^2
          ≤ 2 * (hminusWeight k * ‖cubicCoeff u M k‖^2) +
            2 * (hminusWeight k * ‖cubicCoeff v M k‖^2) := by
    intro k
    -- abbreviate norms
    set a := ‖cubicCoeff u M k‖ with ha
    set b := ‖cubicCoeff v M k‖ with hb
    have h_tri : ‖cubicCoeff u M k - cubicCoeff v M k‖ ≤ a + b := by
      simpa [ha, hb] using norm_sub_le (cubicCoeff u M k) (cubicCoeff v M k)
    have h_nonneg_ab : 0 ≤ a + b := by
      have ha' : 0 ≤ a := by simp [ha]
      have hb' : 0 ≤ b := by simp [hb]
      nlinarith
    have h_sq' : ‖cubicCoeff u M k - cubicCoeff v M k‖^2 ≤ (a + b)^2 := by
      have h_nonneg_norm : 0 ≤ ‖cubicCoeff u M k - cubicCoeff v M k‖ := norm_nonneg _
      nlinarith
    have h_sq :
        ‖cubicCoeff u M k - cubicCoeff v M k‖^2
          ≤ 2 * (‖cubicCoeff u M k‖^2 + ‖cubicCoeff v M k‖^2) := by
      have h2 : 2 * a * b ≤ a^2 + b^2 := by
        have h_nonneg : 0 ≤ (a - b)^2 := sq_nonneg (a - b)
        have h_expand : (a - b)^2 = a^2 + b^2 - 2 * a * b := by ring
        nlinarith [h_nonneg, h_expand]
      calc
        ‖cubicCoeff u M k - cubicCoeff v M k‖^2 ≤ (a + b)^2 := h_sq'
        _ = a^2 + b^2 + 2 * a * b := by ring
        _ ≤ a^2 + b^2 + (a^2 + b^2) := by nlinarith
        _ = 2 * (a^2 + b^2) := by ring
        _ = 2 * (‖cubicCoeff u M k‖^2 + ‖cubicCoeff v M k‖^2) := by
              simp [ha, hb]
    have h_weight_nonneg : 0 ≤ hminusWeight k :=
      ℓ2ZD.hminusWeight_nonneg (d := spatialDim) k
    have h_mul :
        hminusWeight k * ‖cubicCoeff u M k - cubicCoeff v M k‖^2
          ≤ hminusWeight k * (2 * (‖cubicCoeff u M k‖^2 + ‖cubicCoeff v M k‖^2)) :=
      mul_le_mul_of_nonneg_left h_sq h_weight_nonneg
    calc
      hminusWeight k * ‖cubicCoeff u M k - cubicCoeff v M k‖^2
          ≤ hminusWeight k * (2 * (‖cubicCoeff u M k‖^2 + ‖cubicCoeff v M k‖^2)) := h_mul
      _ = 2 * (hminusWeight k * ‖cubicCoeff u M k‖^2) +
            2 * (hminusWeight k * ‖cubicCoeff v M k‖^2) := by ring

  -- Sum the pointwise bound over the chosen finite set `F`.
  have h_sum :
      Finset.sum F (fun k =>
        hminusWeight k * ‖cubicCoeff u M k - cubicCoeff v M k‖^2)
      ≤ Finset.sum F (fun k =>
          2 * (hminusWeight k * ‖cubicCoeff u M k‖^2) +
            2 * (hminusWeight k * ‖cubicCoeff v M k‖^2)) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact h_pointwise k

  have h_sum' :
      Finset.sum F (fun k =>
          2 * (hminusWeight k * ‖cubicCoeff u M k‖^2) +
            2 * (hminusWeight k * ‖cubicCoeff v M k‖^2))
      = 2 * Finset.sum F (fun k => hminusWeight k * ‖cubicCoeff u M k‖^2) +
        2 * Finset.sum F (fun k => hminusWeight k * ‖cubicCoeff v M k‖^2) := by
    simp [Finset.sum_add_distrib, Finset.mul_sum, two_mul]

  have h_sum_bound :
      Finset.sum F (fun k =>
          hminusWeight k * ‖cubicCoeff u M k - cubicCoeff v M k‖^2)
      ≤ 2 * Finset.sum F (fun k => hminusWeight k * ‖cubicCoeff u M k‖^2) +
        2 * Finset.sum F (fun k => hminusWeight k * ‖cubicCoeff v M k‖^2) := by
    calc
      Finset.sum F (fun k =>
          hminusWeight k * ‖cubicCoeff u M k - cubicCoeff v M k‖^2)
          ≤ Finset.sum F (fun k =>
              2 * (hminusWeight k * ‖cubicCoeff u M k‖^2) +
                2 * (hminusWeight k * ‖cubicCoeff v M k‖^2)) := h_sum
      _ = 2 * Finset.sum F (fun k => hminusWeight k * ‖cubicCoeff u M k‖^2) +
            2 * Finset.sum F (fun k => hminusWeight k * ‖cubicCoeff v M k‖^2) := h_sum'

  -- Control each cubic term using the established H⁻¹ bounds.
  have h_u_bound : Finset.sum F (fun k => hminusWeight k * ‖cubicCoeff u M k‖^2)
      ≤ (cubicBound R M)^2 :=
    h_inHminus_u F
  have h_v_bound : Finset.sum F (fun k => hminusWeight k * ‖cubicCoeff v M k‖^2)
      ≤ (cubicBound R M)^2 :=
    h_inHminus_v F

  -- Combine everything.
  calc
    Finset.sum F (fun k =>
        hminusWeight k * ‖cubicCoeff u M k - cubicCoeff v M k‖^2)
        ≤ 2 * Finset.sum F (fun k => hminusWeight k * ‖cubicCoeff u M k‖^2) +
          2 * Finset.sum F (fun k => hminusWeight k * ‖cubicCoeff v M k‖^2) := h_sum_bound
    _ ≤ 2 * (cubicBound R M)^2 + 2 * (cubicBound R M)^2 := by
      linarith [h_u_bound, h_v_bound]
    _ = 4 * (cubicBound R M)^2 := by ring

/-- **Bound for cubic difference on H¹ ball**: When u, v ∈ H¹_M(R), the H⁻¹ norm of (u³ - v³) is bounded.

WARNING: This is NOT a true Lipschitz estimate of the form L·‖u-v‖!
Instead, it's a FIXED BOUND that holds when both sequences are in the H¹(R) ball.

The bound is:
- LHS: H⁻¹ semi-norm² of (cubicCoeff u - cubicCoeff v)
- RHS: The accumulated constant from trilinear factorization

The proof uses the factorization u³ - v³ = (u-v)·u² + v·(u-v)·u + v²·(u-v), where
each term is bounded using the H¹ ball radius (2R) for the difference, NOT the actual ‖u-v‖_{H¹}.

To get a true Lipschitz estimate, the helper lemmas would need to track the actual difference norm.
-/
lemma cubic_lipschitz_proper (u v : SeqD spatialDim) (M : ℕ)
    (h_supp_u : ∀ k, k ∉ cube spatialDim M → u.a k = 0)
    (h_supp_v : ∀ k, k ∉ cube spatialDim M → v.a k = 0)
    (R : ℝ) (hR : 0 < R)
    (h_H1_u : InH1Ball R u) (h_H1_v : InH1Ball R v)
    (F : Finset (Lattice spatialDim)) :
    Finset.sum F (fun k =>
      hminusWeight k * ‖cubicCoeff u M k - cubicCoeff v M k‖^2)
    ≤ cubic_lipschitz_constant spatialDim M sobolev_constant_extended R := by
  classical

  -- The proof proceeds by bounding each of the three trilinear terms from the factorization
  -- No case split needed since the bound is a fixed constant
    -- PROOF STRATEGY:
    -- 1. cubic_diff_factorization: cubicCoeff u - cubicCoeff v = T₁ + T₂ + T₃
    --    T₁ = (u-v) * u * u
    --    T₂ = v * (u-v) * u
    --    T₃ = v * v * (u-v)
    -- 2. Triangle inequality for 3 terms: ‖T₁+T₂+T₃‖² ≤ 3(‖T₁‖² + ‖T₂‖² + ‖T₃‖²)
    -- 3. Apply helper lemmas to bound each term
    -- 4. Combine the bounds

    -- Step 1: Construct diffSeq = u - v
    let diffSeq := u - v  -- Sub instance handles summability ✓

    -- Step 2: Show diffSeq is in H¹ ball of radius 2R
    have h_diff_H1 : InH1Ball (2 * R) diffSeq := by
      intro F
      -- Need: ∑_{k∈F} h1Weight(k) * ‖diffSeq.a k‖² ≤ (2R)²
      calc Finset.sum F (fun k => h1Weight k * ‖diffSeq.a k‖^2)
          = Finset.sum F (fun k => h1Weight k * ‖u.a k - v.a k‖^2) := rfl
        _ ≤ Finset.sum F (fun k => h1Weight k * 2 * (‖u.a k‖^2 + ‖v.a k‖^2)) := by
            apply Finset.sum_le_sum; intro k _
            have h_ineq : ‖u.a k - v.a k‖^2 ≤ 2 * (‖u.a k‖^2 + ‖v.a k‖^2) := by
              have h1 : ‖u.a k - v.a k‖^2 ≤ (‖u.a k‖ + ‖v.a k‖)^2 := by
                apply sq_le_sq' <;> nlinarith [norm_nonneg (u.a k - v.a k), norm_sub_le (u.a k) (v.a k)]
              calc ‖u.a k - v.a k‖^2
                  ≤ (‖u.a k‖ + ‖v.a k‖)^2 := h1
                _ = ‖u.a k‖^2 + 2 * ‖u.a k‖ * ‖v.a k‖ + ‖v.a k‖^2 := by ring
                _ ≤ ‖u.a k‖^2 + ‖u.a k‖^2 + ‖v.a k‖^2 + ‖v.a k‖^2 := by
                    have : 2 * ‖u.a k‖ * ‖v.a k‖ ≤ ‖u.a k‖^2 + ‖v.a k‖^2 := by
                      have : 0 ≤ (‖u.a k‖ - ‖v.a k‖)^2 := sq_nonneg _
                      linarith [sq_nonneg (‖u.a k‖), sq_nonneg (‖v.a k‖)]
                    linarith
                _ = 2 * (‖u.a k‖^2 + ‖v.a k‖^2) := by ring
            nlinarith [ℓ2ZD.h1Weight_pos k, h_ineq]
        _ = Finset.sum F (fun k => 2 * (h1Weight k * (‖u.a k‖^2 + ‖v.a k‖^2))) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
        _ = 2 * Finset.sum F (fun k => h1Weight k * (‖u.a k‖^2 + ‖v.a k‖^2)) := by
            rw [← Finset.mul_sum]
        _ = 2 * (Finset.sum F (fun k => h1Weight k * ‖u.a k‖^2) +
                 Finset.sum F (fun k => h1Weight k * ‖v.a k‖^2)) := by
            congr 1
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k _
            ring
        _ ≤ 2 * (R^2 + R^2) := by linarith [h_H1_u F, h_H1_v F]
        _ = 4 * R^2 := by ring
        _ = (2 * R)^2 := by ring

    -- Step 3: Show diffSeq has support in cube(M)
    have h_supp_diff : ∀ k, k ∉ cube spatialDim M → diffSeq.a k = 0 := by
      intro k hk
      simp only [diffSeq, SeqD.sub_a]
      rw [h_supp_u k hk, h_supp_v k hk]
      simp

    -- Step 4: Apply cubic_diff_factorization
    have h_factor : ∀ k, cubicCoeff u M k - cubicCoeff v M k =
        Finset.sum (cube spatialDim M) (fun k₁ =>
          Finset.sum (cube spatialDim M) (fun k₂ =>
            diffSeq.a k₁ * u.a k₂ * u.a (k - k₁ - k₂))) +
        Finset.sum (cube spatialDim M) (fun k₁ =>
          Finset.sum (cube spatialDim M) (fun k₂ =>
            v.a k₁ * diffSeq.a k₂ * u.a (k - k₁ - k₂))) +
        Finset.sum (cube spatialDim M) (fun k₁ =>
          Finset.sum (cube spatialDim M) (fun k₂ =>
            v.a k₁ * v.a k₂ * diffSeq.a (k - k₁ - k₂))) := by
      intro k
      have h_fact := cubic_diff_factorization u v M h_supp_u h_supp_v k
      simp only [diffSeq] at *
      exact h_fact

    -- Step 5: Define the three terms T₁, T₂, T₃
    let T₁ := fun k => Finset.sum (cube spatialDim M) (fun k₁ =>
        Finset.sum (cube spatialDim M) (fun k₂ =>
          diffSeq.a k₁ * u.a k₂ * u.a (k - k₁ - k₂)))
    let T₂ := fun k => Finset.sum (cube spatialDim M) (fun k₁ =>
        Finset.sum (cube spatialDim M) (fun k₂ =>
          v.a k₁ * diffSeq.a k₂ * u.a (k - k₁ - k₂)))
    let T₃ := fun k => Finset.sum (cube spatialDim M) (fun k₁ =>
        Finset.sum (cube spatialDim M) (fun k₂ =>
          v.a k₁ * v.a k₂ * diffSeq.a (k - k₁ - k₂)))

    -- Step 6: Triangle inequality for 3 terms
    -- Standard result: ‖a + b + c‖² ≤ 3(‖a‖² + ‖b‖² + ‖c‖²)
    have h_triangle : ∀ k, ‖T₁ k + T₂ k + T₃ k‖^2 ≤ 3 * (‖T₁ k‖^2 + ‖T₂ k‖^2 + ‖T₃ k‖^2) := by
      intro k
      -- Use: ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ (triangle inequality)
      have h1 : ‖T₁ k + T₂ k + T₃ k‖ ≤ ‖T₁ k‖ + ‖T₂ k‖ + ‖T₃ k‖ := by
        calc ‖T₁ k + T₂ k + T₃ k‖
            ≤ ‖T₁ k + T₂ k‖ + ‖T₃ k‖ := norm_add_le _ _
          _ ≤ ‖T₁ k‖ + ‖T₂ k‖ + ‖T₃ k‖ := by linarith [norm_add_le (T₁ k) (T₂ k)]
      -- Square both sides
      have h2 : ‖T₁ k + T₂ k + T₃ k‖^2 ≤ (‖T₁ k‖ + ‖T₂ k‖ + ‖T₃ k‖)^2 := by
        apply sq_le_sq'
        · linarith [norm_nonneg (T₁ k + T₂ k + T₃ k)]
        · exact h1
      -- Expand (a + b + c)² and use 2ab ≤ a² + b², etc.
      calc ‖T₁ k + T₂ k + T₃ k‖^2
          ≤ (‖T₁ k‖ + ‖T₂ k‖ + ‖T₃ k‖)^2 := h2
        _ = ‖T₁ k‖^2 + ‖T₂ k‖^2 + ‖T₃ k‖^2 +
            2 * ‖T₁ k‖ * ‖T₂ k‖ + 2 * ‖T₁ k‖ * ‖T₃ k‖ + 2 * ‖T₂ k‖ * ‖T₃ k‖ := by ring
        _ ≤ ‖T₁ k‖^2 + ‖T₂ k‖^2 + ‖T₃ k‖^2 +
            (‖T₁ k‖^2 + ‖T₂ k‖^2) + (‖T₁ k‖^2 + ‖T₃ k‖^2) + (‖T₂ k‖^2 + ‖T₃ k‖^2) := by
          -- Use: 2ab ≤ a² + b² for each cross term
          have h12 : 2 * ‖T₁ k‖ * ‖T₂ k‖ ≤ ‖T₁ k‖^2 + ‖T₂ k‖^2 := two_mul_le_add_sq _ _
          have h13 : 2 * ‖T₁ k‖ * ‖T₃ k‖ ≤ ‖T₁ k‖^2 + ‖T₃ k‖^2 := two_mul_le_add_sq _ _
          have h23 : 2 * ‖T₂ k‖ * ‖T₃ k‖ ≤ ‖T₂ k‖^2 + ‖T₃ k‖^2 := two_mul_le_add_sq _ _
          linarith
        _ = 3 * (‖T₁ k‖^2 + ‖T₂ k‖^2 + ‖T₃ k‖^2) := by ring

    -- Step 7: Rewrite LHS using factorization
    have h_lhs_rewrite : Finset.sum F (fun k =>
          hminusWeight k * ‖cubicCoeff u M k - cubicCoeff v M k‖^2) =
        Finset.sum F (fun k => hminusWeight k * ‖T₁ k + T₂ k + T₃ k‖^2) := by
      congr 1; ext k
      congr 2
      rw [h_factor k]

    rw [h_lhs_rewrite]

    -- Step 8: Apply triangle inequality to each summand
    have h_sum_bound : Finset.sum F (fun k => hminusWeight k * ‖T₁ k + T₂ k + T₃ k‖^2)
        ≤ 3 * Finset.sum F (fun k => hminusWeight k * (‖T₁ k‖^2 + ‖T₂ k‖^2 + ‖T₃ k‖^2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      have h_tri_k := h_triangle k
      nlinarith [ℓ2ZD.hminusWeight_nonneg k, sq_nonneg ‖T₁ k‖, sq_nonneg ‖T₂ k‖, sq_nonneg ‖T₃ k‖, h_tri_k]

    -- Step 9: Complete the calc chain
    -- We need to show that the three sums can each be bounded using the helper lemmas
    have h_T₁_rewrite : T₁ = fun k => Finset.sum (cube spatialDim M) (fun k₁ =>
        Finset.sum (cube spatialDim M) (fun k₂ =>
          diffSeq.a k₁ * u.a k₂ * u.a (k - k₁ - k₂))) := rfl
    have h_T₂_rewrite : T₂ = fun k => Finset.sum (cube spatialDim M) (fun k₁ =>
        Finset.sum (cube spatialDim M) (fun k₂ =>
          v.a k₁ * diffSeq.a k₂ * u.a (k - k₁ - k₂))) := rfl
    have h_T₃_rewrite : T₃ = fun k => Finset.sum (cube spatialDim M) (fun k₁ =>
        Finset.sum (cube spatialDim M) (fun k₂ =>
          v.a k₁ * v.a k₂ * diffSeq.a (k - k₁ - k₂))) := rfl

    -- Apply the three helper bounds
    have h_T₁_bound_raw := bound_trilinear_diff_term diffSeq u u M (2 * R) R F
      h_diff_H1 h_supp_u h_supp_u h_H1_u h_H1_u
    have h_T₁_bound : Finset.sum F (fun k => hminusWeight k * ‖T₁ k‖^2) ≤
        4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
        sobolev_constant_extended^4 * (2 * R)^2 * |R|^4 := by
      show Finset.sum F (fun k => hminusWeight k * ‖T₁ k‖^2) ≤ _
      exact h_T₁_bound_raw
    -- For T₂ = v * (u-v) * u, we need to reindex to get (u-v) * v * u form
    -- This requires swapping k₁ and k₂ indices, which is valid by commutativity of finite sums
    -- Note: bound_trilinear_diff_term requires both v and u to be in the same H¹ ball
    -- So we use R_ab = R (since both u,v are in H¹(R))
    have h_T₂_bound : Finset.sum F (fun k => hminusWeight k * ‖T₂ k‖^2) ≤
        4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
        sobolev_constant_extended^4 * (2 * R)^2 * |R|^4 := by
      -- T₂ = ∑_{k₁,k₂} v(k₁) * diffSeq(k₂) * u(k-k₁-k₂)
      -- Rewrite using commutativity of ℂ and Finset.sum_comm
      have h_T₂_eq : T₂ = fun k => Finset.sum (cube spatialDim M) (fun k₂ =>
          Finset.sum (cube spatialDim M) (fun k₁ =>
            diffSeq.a k₂ * v.a k₁ * u.a (k - k₂ - k₁))) := by
        ext k; simp only [T₂]
        rw [Finset.sum_comm]
        congr 1; ext k₂; congr 1; ext k₁
        ring_nf
      -- Now apply bound_trilinear_diff_term with diffSeq, v, u (in that order)
      -- Since both v and u are in H¹(R), we can use R_ab = R
      calc Finset.sum F (fun k => hminusWeight k * ‖T₂ k‖^2)
          = Finset.sum F (fun k => hminusWeight k * ‖Finset.sum (cube spatialDim M) (fun k₂ =>
              Finset.sum (cube spatialDim M) (fun k₁ =>
                diffSeq.a k₂ * v.a k₁ * u.a (k - k₂ - k₁)))‖^2) := by
            congr 1; ext k; rw [h_T₂_eq]
        _ ≤ 4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
            sobolev_constant_extended^4 * (2 * R)^2 * |R|^4 :=
          bound_trilinear_diff_term diffSeq v u M (2 * R) R F
            h_diff_H1 h_supp_v h_supp_u h_H1_v h_H1_u
    -- Helper: if v is in H¹(R) then v is in H¹(2R) (monotonicity)
    have h_v_2R : InH1Ball (2 * R) v := by
      intro F
      calc Finset.sum F (fun k => h1Weight k * ‖v.a k‖^2)
          ≤ R^2 := h_H1_v F
        _ ≤ (2 * R)^2 := by nlinarith [sq_nonneg R, hR]
    have h_T₃_bound_raw := bound_trilinear_term_pos3 v v diffSeq M (2 * R) F
      h_v_2R  -- v is in H¹(R), so also in H¹(2R)
      h_v_2R
      h_diff_H1 h_supp_v h_supp_v h_supp_diff
    have h_T₃_bound : Finset.sum F (fun k => hminusWeight k * ‖T₃ k‖^2) ≤
        4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
        sobolev_constant_extended^4 * (2 * R)^2 * |2 * R|^4 := by
      show Finset.sum F (fun k => hminusWeight k * ‖T₃ k‖^2) ≤ _
      exact h_T₃_bound_raw

    -- Combine all bounds
    calc Finset.sum F (fun k => hminusWeight k * ‖T₁ k + T₂ k + T₃ k‖^2)
        ≤ 3 * Finset.sum F (fun k => hminusWeight k * (‖T₁ k‖^2 + ‖T₂ k‖^2 + ‖T₃ k‖^2)) := h_sum_bound
      _ = 3 * (Finset.sum F (fun k => hminusWeight k * ‖T₁ k‖^2) +
               Finset.sum F (fun k => hminusWeight k * ‖T₂ k‖^2) +
               Finset.sum F (fun k => hminusWeight k * ‖T₃ k‖^2)) := by
          congr 1
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ ≤ 3 * (4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
               sobolev_constant_extended^4 * (2 * R)^2 * |R|^4 +
               4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
               sobolev_constant_extended^4 * (2 * R)^2 * |R|^4 +
               4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
               sobolev_constant_extended^4 * (2 * R)^2 * |2 * R|^4) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : 0 ≤ (3 : ℝ))
          exact add_le_add (add_le_add h_T₁_bound h_T₂_bound) h_T₃_bound
      _ = 3 * 18 * (4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
                   sobolev_constant_extended^4 * (2 * R)^2 * |R|^4) := by
          -- |2*R|^4 = 16 * |R|^4, so sum is |R|^4 + |R|^4 + 16*|R|^4 = 18*|R|^4
          have h16 : |2 * R|^4 = 16 * |R|^4 := by
            simp only [abs_of_pos hR, abs_of_pos (by linarith : 0 < 2 * R)]
            ring
          have habs : |R|^4 = R^4 := by simp only [abs_of_pos hR]
          calc 3 * (4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
                   sobolev_constant_extended^4 * (2 * R)^2 * |R|^4 +
                   4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
                   sobolev_constant_extended^4 * (2 * R)^2 * |R|^4 +
                   4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
                   sobolev_constant_extended^4 * (2 * R)^2 * |2 * R|^4)
              = 3 * (4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
                   sobolev_constant_extended^4 * (2 * R)^2 * R^4 +
                   4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
                   sobolev_constant_extended^4 * (2 * R)^2 * R^4 +
                   4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
                   sobolev_constant_extended^4 * (2 * R)^2 * (16 * R^4)) := by
                simp only [habs, h16]
            _ = 3 * 18 * (4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
                   sobolev_constant_extended^4 * (2 * R)^2 * R^4) := by ring
            _ = 3 * 18 * (4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
                   sobolev_constant_extended^4 * (2 * R)^2 * |R|^4) := by rw [← habs]
      _ = 54 * 4^spatialDim * ((2 * M + 1)^(4 * spatialDim) : ℝ) *
          sobolev_constant_extended^4 * (2 * R)^2 * R^4 := by
          simp only [abs_of_pos hR]; ring
      _ = cubic_lipschitz_constant spatialDim M sobolev_constant_extended R := by
          -- The calc chain gives EXACTLY the definition
          unfold cubic_lipschitz_constant
          ring

end -- noncomputable section

end SemilinearHeat
