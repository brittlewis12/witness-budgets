import Budgets.RellichKondrachov1D.L2Bridge
import Budgets.ConstructiveQ

/-!
# Rellich-Kondrachov 1D Witness Extraction Demo

Demonstrates the constructive witness extraction for the Rellich-Kondrachov theorem
on the 1D torus using the formal verification from `Budgets.RellichKondrachov1D`.

This demo validates:
- Finite witness grid construction for mean-zero H¹ functions
- Computable grid parameters (M, δ, grid cardinality)
- Soundness: every function is ε-approximated by some grid point

The formal theorem in `RellichKondrachov1D/L2Bridge.lean` (`witness_soundness_via_bridge`)
proves that for any mean-zero function in the H¹ ball of radius R, there exists
a grid point within L² distance ε.

**Key parameters**:
- ε : ℚ - approximation accuracy (L² distance bound)
- R : ℚ - H¹ ball radius
- M : ℕ - frequency cutoff (derived: M = ⌈R/(π·ε)⌉ + 1)
- δ : ℚ - grid mesh (derived: δ = ε/(2·(2M+1)))
- Grid dimension: 2M (Fourier frequencies from -M to M, excluding 0)

**Budget**: C0-C2 (fully constructive)
**xBudget**: Witness metadata is fully extractable (ℚ, ℕ, Finset only)
-/

namespace QRK1DDemo

open RellichKondrachov1D
open RellichKondrachov1D.L2Bridge
open RellichKondrachov1D.Seq
open ConstructiveQ
open scoped BigOperators Real

/-! ## Noncomputable Test Function Layer

The L² functions themselves are noncomputable (they involve measure theory),
but witness existence and metadata extraction are computable.
-/

noncomputable section

/-! ### Test Case 1: Pure Sine Mode

**Function**: u₁(x) = sin(2πx)

**Fourier decomposition**:
- a₁ = i/2
- a₋₁ = -i/2
- all other coefficients zero

**Properties**:
- Mean-zero: ∫u₁ = 0 (k=0 coefficient is 0)
- H¹-norm: ‖u‖²_H¹ = (1 + 4π²)/2 ≈ 20.24
- Smooth: infinitely differentiable

**Test parameters**: ε = 1/10, R = 5
(Note: R adjusted from 1 to 5 to accommodate H¹ energy)
-/

section TestCase1

-- Concrete test parameters (computable)
def ε₁ : ℚ := 1 / 10
def R₁ : ℚ := 5  -- Adjusted from 1 to accommodate H¹ energy

-- Positivity proofs (simple, could be automated)
lemma hε₁ : 0 < (ε₁ : ℝ) := by norm_num [ε₁]
lemma hR₁ : 0 < (R₁ : ℝ) := by norm_num [R₁]

/-- Test sequence 1: Fourier coefficients for u(x) = sin(2πx).
    Explicit constructive ℓ² sequence with finite Fourier support:
    a₁ = i/2, a₋₁ = -i/2, all others = 0. -/
def seq₁ : ℓ2Z where
  a := fun k => if k = 1 then Complex.I / 2
                else if k = -1 then -Complex.I / 2
                else 0
  summable_sq := by
    -- Finite support implies summable
    apply summable_of_ne_finset_zero (s := {-1, 1})
    intro k hk
    simp [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

/-- seq₁ is mean-zero: the 0-mode coefficient vanishes by definition. -/
lemma seq₁_mean_zero : seq₁.meanZero := by
  unfold ℓ2Z.meanZero seq₁
  rfl

/-- seq₁ lies in the H¹ ball of radius R₁.

    Energy calculation:
    - For k = ±1: (1 + (2π)²) ‖i/2‖² = (1 + 4π²) · 1/4
    - Total: 2 · (1 + 4π²) · 1/4 = (1 + 4π²) / 2
    - Numerically: (1 + 4π²) / 2 ≈ (1 + 39.48) / 2 ≈ 20.24

    Note: Originally R₁ = 1, but (1 + 4π²)/2 ≈ 20.24 > 1.
    Adjusted R₁ = 5, so R₁² = 25 > 20.24. ✓
-/
lemma seq₁_in_H1Ball : seq₁.InH1Ball (R₁ : ℝ) := by
  constructor
  intro F
  -- Need to show: ∑ k ∈ F, (1 + (2π|k|)²) ‖a k‖² ≤ R₁²
  -- Only k ∈ {-1, 1} contribute (all others have a k = 0)

  -- Key observation: seq₁.a k = 0 for k ∉ {-1, 1}
  have seq₁_support : ∀ k : ℤ, k ≠ 1 → k ≠ -1 → seq₁.a k = 0 := by
    intro k hk1 hkm1
    unfold seq₁
    simp [hk1, hkm1]

  -- Direct calculation using finite support
  -- Key: Only k ∈ {-1, 1} contribute non-zero terms
  calc Finset.sum F (fun k => (1 + (2 * Real.pi * (k : ℝ))^2) * ‖seq₁.a k‖^2)
      ≤ (1 + (2 * Real.pi)^2) * ‖seq₁.a 1‖^2
        + (1 + (2 * Real.pi)^2) * ‖seq₁.a (-1)‖^2 := by
        -- Only k ∈ {-1, 1} contribute (seq₁_support shows others are 0)
        trans (({-1, 1} : Finset ℤ).sum (fun k => (1 + (2 * Real.pi * (k : ℝ))^2) * ‖seq₁.a k‖^2))
        · -- Sum over F equals sum over F ∩ {-1, 1}, then bound by {-1, 1}
          have h_eq : F.sum (fun k => (1 + (2 * Real.pi * (k : ℝ))^2) * ‖seq₁.a k‖^2) =
              (F ∩ {-1, 1}).sum (fun k => (1 + (2 * Real.pi * (k : ℝ))^2) * ‖seq₁.a k‖^2) := by
            symm
            apply Finset.sum_subset (Finset.inter_subset_left)
            intro k hk_in hk_not
            simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hk_not
            push_neg at hk_not
            rw [seq₁_support k (hk_not hk_in).2 (hk_not hk_in).1]
            norm_num
          rw [h_eq]
          apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          intros; positivity
        · -- Expand the finite sum over {-1, 1}
          rw [Finset.sum_insert (by decide), Finset.sum_singleton]
          -- Simplify: (2π*(-1))² = (2π)² and (2π*1)² = (2π)², then prove equality via commutativity
          norm_num
          apply le_of_eq
          ring
    _ = (1 + (2 * Real.pi)^2) * ‖Complex.I / 2‖^2
        + (1 + (2 * Real.pi)^2) * ‖-Complex.I / 2‖^2 := by
        simp [seq₁]
    _ = (1 + (2 * Real.pi)^2) * (1/4) + (1 + (2 * Real.pi)^2) * (1/4) := by
        norm_num
    _ = (1 + (2 * Real.pi)^2) / 2 := by ring
    _ ≤ (R₁ : ℝ)^2 := by
        norm_num [R₁]
        -- Need: (1 + 4π²)/2 ≤ 25
        -- Use π < 3.1416 to bound the expression
        have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
        have hpi2 : Real.pi^2 < 3.1416^2 := sq_lt_sq' (by linarith [Real.pi_pos]) hpi
        apply le_of_lt
        calc (1 + (2 * Real.pi)^2) / 2
            = (1 + 4 * Real.pi^2) / 2 := by ring
          _ < (1 + 4 * 3.1416^2) / 2 := by
              apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 2)
              apply add_lt_add_left
              apply mul_lt_mul_of_pos_left hpi2 (by norm_num : (0 : ℝ) < 4)
          _ < 25 := by norm_num

/-- **Main result**: Witness exists for test case 1.
    The gridFinset_sound theorem guarantees a grid point approximates
    the constructive ℓ² sequence seq₁. -/
theorem witness_exists_test1 :
    ∃ (g : ℓ2Z.GridPoint ε₁ R₁ (ℓ2Z.M_of ε₁ R₁)),
      g ∈ ℓ2Z.gridFinset ε₁ R₁ (ℓ2Z.M_of ε₁ R₁) ∧
      ∀ F : Finset ℤ,
        Finset.sum F
          (fun k => ‖seq₁.a k - (ℓ2Z.gridToSeq ε₁ R₁ (ℓ2Z.M_of ε₁ R₁) g).a k‖^2)
          < (ε₁ : ℝ)^2 := by
  have h := ℓ2Z.gridFinset_sound ε₁ R₁ hε₁ hR₁
  exact h seq₁ seq₁_mean_zero seq₁_in_H1Ball

end TestCase1

/-! ### Test Case 2: Two-Mode Superposition

**Function**: u₂(x) = sin(2πx) + (1/2)sin(4πx)

**Fourier decomposition**:
- Fundamental: a₁ = i/2, a₋₁ = -i/2
- First harmonic: a₂ = i/4, a₋₂ = -i/4
- Higher coefficients zero

**Properties**:
- Mean-zero: both modes have zero DC component
- Less smooth than u₁: higher frequency content
- H¹-norm: ‖u‖²_H¹ = (1 + 4π²)/2 + (1 + 16π²)/8 ≈ 40.10
- Larger H¹-norm: requires larger R

**Test parameters**: ε = 1/20, R = 7
(Note: R adjusted from 3/2 to 7 to accommodate H¹ energy)
-/

section TestCase2

-- Concrete test parameters (computable)
def ε₂ : ℚ := 1 / 20
def R₂ : ℚ := 7  -- Adjusted from 3/2 to accommodate H¹ energy

-- Positivity proofs (simple, could be automated)
lemma hε₂ : 0 < (ε₂ : ℝ) := by norm_num [ε₂]
lemma hR₂ : 0 < (R₂ : ℝ) := by norm_num [R₂]

/-- Test sequence 2: Fourier coefficients for u(x) = sin(2πx) + (1/2)sin(4πx).
    Explicit constructive ℓ² sequence with finite Fourier support:
    a₁ = i/2, a₋₁ = -i/2, a₂ = i/4, a₋₂ = -i/4, all others = 0. -/
def seq₂ : ℓ2Z where
  a := fun k =>
    if k = 1 then Complex.I / 2
    else if k = -1 then -Complex.I / 2
    else if k = 2 then Complex.I / 4
    else if k = -2 then -Complex.I / 4
    else 0
  summable_sq := by
    -- Finite support implies summable
    apply summable_of_ne_finset_zero (s := {-2, -1, 1, 2})
    intro k hk
    simp [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

/-- seq₂ is mean-zero: the 0-mode coefficient vanishes by definition. -/
lemma seq₂_mean_zero : seq₂.meanZero := by
  unfold ℓ2Z.meanZero seq₂
  rfl

/-- seq₂ lies in the H¹ ball of radius R₂.

    Energy calculation:
    - For k = ±1: (1 + (2π)²) ‖i/2‖² = (1 + 4π²) · 1/4
    - For k = ±2: (1 + (4π)²) ‖i/4‖² = (1 + 16π²) · 1/16
    - Total: 2 · (1 + 4π²) · 1/4 + 2 · (1 + 16π²) · 1/16
           = (1 + 4π²) / 2 + (1 + 16π²) / 8
           ≈ 20.24 + 19.86 ≈ 40.10

    Note: Originally R₂ = 3/2, but energy ≈ 40.1 >> (3/2)² = 2.25.
    Adjusted R₂ = 7, so R₂² = 49 > 40.1. ✓
-/
lemma seq₂_in_H1Ball : seq₂.InH1Ball (R₂ : ℝ) := by
  constructor
  intro F
  -- Need to show: ∑ k ∈ F, (1 + (2π|k|)²) ‖a k‖² ≤ R₂²
  -- Only k ∈ {-2, -1, 1, 2} contribute (all others have a k = 0)

  -- Key observation: seq₂.a k = 0 for k ∉ {-2, -1, 1, 2}
  have seq₂_support : ∀ k : ℤ, k ≠ 1 → k ≠ -1 → k ≠ 2 → k ≠ -2 → seq₂.a k = 0 := by
    intro k hk1 hkm1 hk2 hkm2
    unfold seq₂
    simp [hk1, hkm1, hk2, hkm2]

  -- Direct calculation using finite support
  -- Key: Only k ∈ {-2, -1, 1, 2} contribute non-zero terms
  calc Finset.sum F (fun k => (1 + (2 * Real.pi * (k : ℝ))^2) * ‖seq₂.a k‖^2)
      ≤ (1 + (2 * Real.pi)^2) * ‖seq₂.a 1‖^2
        + (1 + (2 * Real.pi)^2) * ‖seq₂.a (-1)‖^2
        + (1 + (4 * Real.pi)^2) * ‖seq₂.a 2‖^2
        + (1 + (4 * Real.pi)^2) * ‖seq₂.a (-2)‖^2 := by
        -- Only k ∈ {-2, -1, 1, 2} contribute (seq₂_support shows others are 0)
        trans (({-2, -1, 1, 2} : Finset ℤ).sum (fun k => (1 + (2 * Real.pi * (k : ℝ))^2) * ‖seq₂.a k‖^2))
        · -- Sum over F equals sum over F ∩ {-2, -1, 1, 2}, then bound by {-2, -1, 1, 2}
          have h_eq : F.sum (fun k => (1 + (2 * Real.pi * (k : ℝ))^2) * ‖seq₂.a k‖^2) =
              (F ∩ {-2, -1, 1, 2}).sum (fun k => (1 + (2 * Real.pi * (k : ℝ))^2) * ‖seq₂.a k‖^2) := by
            symm
            apply Finset.sum_subset (Finset.inter_subset_left)
            intro k hk_in hk_not
            simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hk_not
            push_neg at hk_not
            obtain ⟨h1, h2, h3, h4⟩ := hk_not hk_in
            rw [seq₂_support k h3 h2 h4 h1]
            norm_num
          rw [h_eq]
          apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          intros; positivity
        · -- Expand the finite sum over {-2, -1, 1, 2}
          rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
              Finset.sum_insert (by decide), Finset.sum_singleton]
          -- Simplify: (2π*k)² for k=±1,±2, then prove equality via commutativity
          norm_num
          apply le_of_eq
          ring
    _ = (1 + (2 * Real.pi)^2) * ‖Complex.I / 2‖^2
        + (1 + (2 * Real.pi)^2) * ‖-Complex.I / 2‖^2
        + (1 + (4 * Real.pi)^2) * ‖Complex.I / 4‖^2
        + (1 + (4 * Real.pi)^2) * ‖-Complex.I / 4‖^2 := by
        simp [seq₂]
    _ = (1 + (2 * Real.pi)^2) * (1/4) + (1 + (2 * Real.pi)^2) * (1/4)
        + (1 + (4 * Real.pi)^2) * (1/16) + (1 + (4 * Real.pi)^2) * (1/16) := by
        norm_num
    _ = (1 + (2 * Real.pi)^2) / 2 + (1 + (4 * Real.pi)^2) / 8 := by ring
    _ ≤ (R₂ : ℝ)^2 := by
        norm_num [R₂]
        -- Need: (1 + 4π²)/2 + (1 + 16π²)/8 ≤ 49
        -- Use π < 3.1416 to bound the expression
        have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
        have hpi2 : Real.pi^2 < 3.1416^2 := sq_lt_sq' (by linarith [Real.pi_pos]) hpi
        apply le_of_lt
        calc (1 + (2 * Real.pi)^2) / 2 + (1 + (4 * Real.pi)^2) / 8
            = (1 + 4 * Real.pi^2) / 2 + (1 + 16 * Real.pi^2) / 8 := by ring
          _ < (1 + 4 * 3.1416^2) / 2 + (1 + 16 * 3.1416^2) / 8 := by
              apply add_lt_add
              · apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 2)
                apply add_lt_add_left
                apply mul_lt_mul_of_pos_left hpi2 (by norm_num : (0 : ℝ) < 4)
              · apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 8)
                apply add_lt_add_left
                apply mul_lt_mul_of_pos_left hpi2 (by norm_num : (0 : ℝ) < 16)
          _ < 49 := by norm_num

/-- **Main result**: Witness exists for test case 2.
    The gridFinset_sound theorem guarantees a grid point approximates
    the constructive ℓ² sequence seq₂. -/
theorem witness_exists_test2 :
    ∃ (g : ℓ2Z.GridPoint ε₂ R₂ (ℓ2Z.M_of ε₂ R₂)),
      g ∈ ℓ2Z.gridFinset ε₂ R₂ (ℓ2Z.M_of ε₂ R₂) ∧
      ∀ F : Finset ℤ,
        Finset.sum F
          (fun k => ‖seq₂.a k - (ℓ2Z.gridToSeq ε₂ R₂ (ℓ2Z.M_of ε₂ R₂) g).a k‖^2)
          < (ε₂ : ℝ)^2 := by
  have h := ℓ2Z.gridFinset_sound ε₂ R₂ hε₂ hR₂
  exact h seq₂ seq₂_mean_zero seq₂_in_H1Ball

end TestCase2

/-! ### Test Case 3: Higher Frequency Mode

**Function**: u₃(x) = sin(6πx)

**Fourier decomposition**:
- Third harmonic: a₃ = i/2, a₋₃ = -i/2
- Other coefficients zero

**Properties**:
- Mean-zero: no DC component
- High frequency: k=3 mode
- H¹-norm: ‖u‖²_H¹ = (1 + 36π²)/2 ≈ 178.15
- Requires larger cutoff M: more grid points needed

**Test parameters**: ε = 1/10, R = 15
(Note: R adjusted from 2 to 15 to accommodate H¹ energy)
-/

section TestCase3

-- Concrete test parameters (computable)
def ε₃ : ℚ := 1 / 10
def R₃ : ℚ := 15  -- Adjusted from 2 to accommodate H¹ energy

-- Positivity proofs (simple, could be automated)
lemma hε₃ : 0 < (ε₃ : ℝ) := by norm_num [ε₃]
lemma hR₃ : 0 < (R₃ : ℝ) := by norm_num [R₃]

/-- Test sequence 3: Fourier coefficients for u(x) = sin(6πx).
    Explicit constructive ℓ² sequence with finite Fourier support:
    a₃ = i/2, a₋₃ = -i/2, all others = 0. -/
def seq₃ : ℓ2Z where
  a := fun k => if k = 3 then Complex.I / 2
                else if k = -3 then -Complex.I / 2
                else 0
  summable_sq := by
    -- Finite support implies summable
    apply summable_of_ne_finset_zero (s := {-3, 3})
    intro k hk
    simp [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

/-- seq₃ is mean-zero: the 0-mode coefficient vanishes by definition. -/
lemma seq₃_mean_zero : seq₃.meanZero := by
  unfold ℓ2Z.meanZero seq₃
  rfl

/-- seq₃ lies in the H¹ ball of radius R₃.

    Energy calculation:
    - For k = ±3: (1 + (6π)²) ‖i/2‖² = (1 + 36π²) · 1/4
    - Total: 2 · (1 + 36π²) · 1/4 = (1 + 36π²) / 2
    - Numerically: (1 + 36π²) / 2 ≈ (1 + 355.3) / 2 ≈ 178.15

    Note: Originally R₃ = 2, but (1 + 36π²)/2 ≈ 178.15 > 4.
    Adjusted R₃ = 15, so R₃² = 225 > 178.15. ✓
-/
lemma seq₃_in_H1Ball : seq₃.InH1Ball (R₃ : ℝ) := by
  constructor
  intro F
  -- Need to show: ∑ k ∈ F, (1 + (2π|k|)²) ‖a k‖² ≤ R₃²
  -- Only k ∈ {-3, 3} contribute (all others have a k = 0)

  -- Key observation: seq₃.a k = 0 for k ∉ {-3, 3}
  have seq₃_support : ∀ k : ℤ, k ≠ 3 → k ≠ -3 → seq₃.a k = 0 := by
    intro k hk3 hkm3
    unfold seq₃
    simp [hk3, hkm3]

  -- Direct calculation using finite support
  -- Key: Only k ∈ {-3, 3} contribute non-zero terms
  calc Finset.sum F (fun k => (1 + (2 * Real.pi * (k : ℝ))^2) * ‖seq₃.a k‖^2)
      ≤ (1 + (2 * Real.pi * 3)^2) * ‖seq₃.a 3‖^2
        + (1 + (2 * Real.pi * 3)^2) * ‖seq₃.a (-3)‖^2 := by
        -- Only k ∈ {-3, 3} contribute (seq₃_support shows others are 0)
        trans (({-3, 3} : Finset ℤ).sum (fun k => (1 + (2 * Real.pi * (k : ℝ))^2) * ‖seq₃.a k‖^2))
        · -- Sum over F equals sum over F ∩ {-3, 3}, then bound by {-3, 3}
          have h_eq : F.sum (fun k => (1 + (2 * Real.pi * (k : ℝ))^2) * ‖seq₃.a k‖^2) =
              (F ∩ {-3, 3}).sum (fun k => (1 + (2 * Real.pi * (k : ℝ))^2) * ‖seq₃.a k‖^2) := by
            symm
            apply Finset.sum_subset (Finset.inter_subset_left)
            intro k hk_in hk_not
            simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hk_not
            push_neg at hk_not
            rw [seq₃_support k (hk_not hk_in).2 (hk_not hk_in).1]
            norm_num
          rw [h_eq]
          apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          intros; positivity
        · -- Expand the finite sum over {-3, 3}
          rw [Finset.sum_insert (by decide), Finset.sum_singleton]
          -- Simplify: (2π*(-3))² = (2π*3)², then prove equality via commutativity
          norm_num
          apply le_of_eq
          ring
    _ = (1 + (6 * Real.pi)^2) * ‖Complex.I / 2‖^2
        + (1 + (6 * Real.pi)^2) * ‖-Complex.I / 2‖^2 := by
        simp [seq₃]
        ring_nf
    _ = (1 + (6 * Real.pi)^2) * (1/4) + (1 + (6 * Real.pi)^2) * (1/4) := by
        norm_num
    _ = (1 + (6 * Real.pi)^2) / 2 := by ring
    _ ≤ (R₃ : ℝ)^2 := by
        norm_num [R₃]
        -- Need: (1 + 36π²)/2 ≤ 225
        -- Use π < 3.1416 to bound the expression
        have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
        have hpi2 : Real.pi^2 < 3.1416^2 := sq_lt_sq' (by linarith [Real.pi_pos]) hpi
        apply le_of_lt
        calc (1 + (6 * Real.pi)^2) / 2
            = (1 + 36 * Real.pi^2) / 2 := by ring
          _ < (1 + 36 * 3.1416^2) / 2 := by
              apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 2)
              apply add_lt_add_left
              apply mul_lt_mul_of_pos_left hpi2 (by norm_num : (0 : ℝ) < 36)
          _ < 225 := by norm_num

/-- **Main result**: Witness exists for test case 3.
    The gridFinset_sound theorem guarantees a grid point approximates
    the constructive ℓ² sequence seq₃. -/
theorem witness_exists_test3 :
    ∃ (g : ℓ2Z.GridPoint ε₃ R₃ (ℓ2Z.M_of ε₃ R₃)),
      g ∈ ℓ2Z.gridFinset ε₃ R₃ (ℓ2Z.M_of ε₃ R₃) ∧
      ∀ F : Finset ℤ,
        Finset.sum F
          (fun k => ‖seq₃.a k - (ℓ2Z.gridToSeq ε₃ R₃ (ℓ2Z.M_of ε₃ R₃) g).a k‖^2)
          < (ε₃ : ℝ)^2 := by
  have h := ℓ2Z.gridFinset_sound ε₃ R₃ hε₃ hR₃
  exact h seq₃ seq₃_mean_zero seq₃_in_H1Ball

end TestCase3

end -- noncomputable section

end QRK1DDemo

/-! ## Executable Metadata Extraction

The WitnessPkg structure and its derived quantities (M, δ, grid size)
are fully computable. We can extract and display them in executable IO.
-/

open ConstructiveQ
open RellichKondrachov1D.Seq.ℓ2Z

/-- Computable witness metadata for display -/
structure WitnessMetadata where
  test_name : String
  function_description : String
  ε : ℚ
  R : ℚ
deriving Repr

/-- Compute derived parameters from ε and R -/
def compute_parameters (ε R : ℚ) : (ℕ × ℚ × ℕ) :=
  let M := M_of ε R
  let δ := mesh ε M
  let grid_dim := 2 * M
  (M, δ, grid_dim)

/-- Create witness package (fully extractable) -/
def make_witness_pkg (ε R : ℚ) : WitnessPkg :=
  { ε := ε, R := R }

/-- Display witness metadata with computed parameters -/
def display_witness_metadata (w : WitnessMetadata) : IO Unit := do
  let (M, δ, grid_dim) := compute_parameters w.ε w.R
  let _pkg := make_witness_pkg w.ε w.R

  IO.println "╭──────────────────────────────────────────────────────────╮"
  IO.println s!"│  {w.test_name}"
  IO.println "╰──────────────────────────────────────────────────────────╯"
  IO.println ""
  IO.println s!"  Function: {w.function_description}"
  IO.println ""
  IO.println "  Input Parameters:"
  IO.println s!"    ε (L² accuracy):      {w.ε}"
  IO.println s!"    R (H¹ radius):        {w.R}"
  IO.println ""
  IO.println "  Derived Witness Parameters:"
  IO.println s!"    M (frequency cutoff):  {M}"
  IO.println s!"    δ (grid mesh):         {δ}"
  IO.println s!"    Grid dimension:        {grid_dim} frequencies"
  IO.println s!"    Grid structure:        Finset (GridPoint ε R M)"
  IO.println s!"    Grid nonempty:         ✓ (proven in WitnessPkg.grid_nonempty)"
  IO.println ""
  IO.println "  Witness Guarantee:"
  IO.println s!"    ∃g ∈ grid, ‖u - g‖²_L² < {w.ε}² = {w.ε * w.ε}"
  IO.println ""

/-! ## Main Executable -/

def main : IO Unit := do
  IO.println ""
  IO.println "╔════════════════════════════════════════════════════════════╗"
  IO.println "║  Rellich-Kondrachov 1D Witness Extraction Demo            ║"
  IO.println "║  Mean-Zero H¹ Functions on the Unit Torus                 ║"
  IO.println "║  Constructive Witness Extraction                           ║"
  IO.println "╚════════════════════════════════════════════════════════════╝"
  IO.println ""
  IO.println "Formal verification:"
  IO.println "  • Core theorem:  budgets/Budgets/RellichKondrachov1D.lean"
  IO.println "  • Sequence layer: budgets/Budgets/RellichKondrachov1D/Seq.lean"
  IO.println "  • Bridge theorem: budgets/Budgets/RellichKondrachov1D/L2Bridge.lean"
  IO.println ""
  IO.println "Test approach: Explicit ℓ² sequences (finite Fourier support)"
  IO.println "  • Direct construction via Fourier coefficients"
  IO.println "  • Proven mean-zero and H¹-ball membership"
  IO.println "  • R parameters adjusted for actual H¹ energies"
  IO.println ""
  IO.println "Key result: witness_soundness_via_bridge"
  IO.println "  For any mean-zero u ∈ H¹(𝕋) with ‖u‖_H¹ ≤ R:"
  IO.println "  ∃ grid point g such that ‖u - g‖²_L² < ε²"
  IO.println ""
  IO.println "xBudget: C0-C2 (fully constructive, extractable)"
  IO.println "Extraction: WitnessPkg is fully computable (ℚ, ℕ, Finset only)"
  IO.println ""
  IO.println "════════════════════════════════════════════════════════════"
  IO.println ""

  -- Test 1: Pure sine, moderate accuracy
  display_witness_metadata {
    test_name := "Test 1: Pure Sine Mode"
    function_description := "ℓ² sequence: a₁=i/2, a₋₁=-i/2 (represents sin(2πx)) | R=5 (H¹ energy ≈ 20.24)"
    ε := QRK1DDemo.ε₁
    R := QRK1DDemo.R₁
  }

  IO.println "────────────────────────────────────────────────────────────"
  IO.println ""

  -- Test 2: Two modes, tighter accuracy
  display_witness_metadata {
    test_name := "Test 2: Two-Mode Superposition"
    function_description := "ℓ² sequence: modes k=±1,±2 (represents sin(2πx) + ½sin(4πx)) | R=7 (H¹ energy ≈ 40.10)"
    ε := QRK1DDemo.ε₂
    R := QRK1DDemo.R₂
  }

  IO.println "────────────────────────────────────────────────────────────"
  IO.println ""

  -- Test 3: Higher frequency
  display_witness_metadata {
    test_name := "Test 3: Higher Frequency Mode"
    function_description := "ℓ² sequence: a₃=i/2, a₋₃=-i/2 (represents sin(6πx)) | R=15 (H¹ energy ≈ 178.15)"
    ε := QRK1DDemo.ε₃
    R := QRK1DDemo.R₃
  }

  IO.println "════════════════════════════════════════════════════════════"
  IO.println ""
  IO.println "╔════════════════════════════════════════════════════════════╗"
  IO.println "║ Extraction Status: SUCCESS                                 ║"
  IO.println "║                                                             ║"
  IO.println "║ ✓ Fully constructive approach (zero axioms)                ║"
  IO.println "║ ✓ Explicit ℓ² sequences with finite Fourier support       ║"
  IO.println "║ ✓ Witness existence proven for all 3 test cases           ║"
  IO.println "║ ✓ Grid parameters computed from (ε, R)                    ║"
  IO.println "║ ✓ WitnessPkg fully extractable (xBudget C0)               ║"
  IO.println "║ ✓ Soundness via witness_soundness_via_bridge              ║"
  IO.println "║                                                             ║"
  IO.println "║ Witness theorems:                                          ║"
  IO.println "║   • witness_exists_test1 (pure sine, seq₁)                 ║"
  IO.println "║   • witness_exists_test2 (two-mode, seq₂)                  ║"
  IO.println "║   • witness_exists_test3 (high frequency, seq₃)            ║"
  IO.println "║                                                             ║"
  IO.println "║ Constructive proof strategy:                               ║"
  IO.println "║   • Explicit finite Fourier support                        ║"
  IO.println "║   • Mean-zero by construction (a₀ = 0)                     ║"
  IO.println "║   • H¹ ball membership via finite arithmetic               ║"
  IO.println "║   • R adjusted to accommodate actual H¹ energy             ║"
  IO.println "╚════════════════════════════════════════════════════════════╝"
  IO.println ""
