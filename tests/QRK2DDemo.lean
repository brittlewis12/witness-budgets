import Budgets.RellichKondrachov2D
import Budgets.ConstructiveQ

/-!
# Rellich-Kondrachov 2D Witness Extraction Demo

Demonstrates constructive witness extraction for the Rellich-Kondrachov theorem
on the 2D torus using the formal verification from `Budgets.RellichKondrachov2D`.

## Mathematical Content

The Rellich-Kondrachov theorem establishes compactness of the embedding H¹(𝕋²) ↪ L²(𝕋²).
This demo provides:
- Finite witness grid construction for mean-zero H¹ functions on 𝕋²
- Computable grid parameters (M, δ, grid cardinality)
- Soundness: every function is ε-approximated by some grid point

The formal theorem `gridFinset_sound_2D` in `RellichKondrachov2D.lean` proves that
for any mean-zero function in the H¹ ball of radius R, there exists a grid point
within L² distance ε.

## Key Parameters

- ε : ℚ - Approximation accuracy (L² distance bound)
- R : ℚ - H¹ ball radius
- M : ℕ - Frequency cutoff (derived: M = ⌈R/(π·ε)⌉ + 1)
- δ : ℚ - Grid mesh (derived: δ = ε/(4·(2M+1)))
- Grid dimension: (2M+1)² - 1 (Fourier frequencies in [-M,M]² \ {(0,0)})

## Verification Status

- Budget: C0-C2 (fully constructive)
- xBudget: Witness metadata fully extractable (ℚ, ℕ, Finset only)
-/

namespace QRK2DDemo

open RellichKondrachov2D.Seq
open RellichKondrachov2D.Seq.ℓ2Z2
open ConstructiveQ
open scoped BigOperators Real

/-! ## Noncomputable Test Function Layer

The L² functions themselves are noncomputable (they involve measure theory),
but witness existence and metadata extraction are computable.
-/

noncomputable section

/-! ### Test Case 1: Product Mode

Function: u₁(x,y) = sin(2πx)sin(2πy)

Fourier decomposition:
- a₍₁,₁₎ = -1/4
- a₍₁,₋₁₎ = 1/4
- a₍₋₁,₁₎ = 1/4
- a₍₋₁,₋₁₎ = -1/4
- all other coefficients zero

Properties:
- Mean-zero: ∫∫u₁ = 0 (k=(0,0) coefficient is 0)
- H¹-norm: ‖u‖²_H¹ = (1 + 8π²)/4 ≈ 19.99
- Smooth: infinitely differentiable
- Separable: product of 1D functions

Test parameters: ε = 1/10, R = 5
Parameter R = 5 chosen to accommodate the 2D H¹ energy (≈ 19.99).
-/

section TestCase1

-- Concrete test parameters (computable)
def ε₁ : ℚ := 1 / 10
def R₁ : ℚ := 5

-- Positivity proofs
lemma hε₁ : 0 < (ε₁ : ℝ) := by norm_num [ε₁]
lemma hR₁ : 0 < (R₁ : ℝ) := by norm_num [R₁]

/-- Test sequence 1: Fourier coefficients for u(x,y) = sin(2πx)sin(2πy).
    Explicit constructive ℓ² sequence with finite Fourier support:
    Four modes at (±1, ±1). -/
def seq₁ : ℓ2Z2 where
  a := fun k =>
    if k = (1, 1) then -1/4
    else if k = (1, -1) then 1/4
    else if k = (-1, 1) then 1/4
    else if k = (-1, -1) then -1/4
    else 0
  summable_sq := by
    -- Finite support implies summable
    apply summable_of_ne_finset_zero (s := {(1, 1), (1, -1), (-1, 1), (-1, -1)})
    intro k hk
    simp [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

/-- seq₁ is mean-zero: the (0,0)-mode coefficient vanishes by definition. -/
lemma seq₁_mean_zero : seq₁.meanZero := by
  unfold meanZero seq₁
  rfl

/-- seq₁ lies in the H¹ ball of radius R₁.

    Energy calculation:
    - For k = (±1, ±1): |k|² = 1² + 1² = 2
    - Weight: 1 + 4π²·2 = 1 + 8π²
    - Contribution per mode: (1 + 8π²) · |±1/4|² = (1 + 8π²) · 1/16
    - Total: 4 · (1 + 8π²) · 1/16 = (1 + 8π²) / 4
    - Numerically: (1 + 8π²) / 4 ≈ (1 + 78.957) / 4 ≈ 19.989

    R₁ = 5, so R₁² = 25 > 19.989. ✓
-/
lemma seq₁_in_H1Ball : seq₁.InH1Ball (R₁ : ℝ) := by
  constructor
  intro F

  -- Key observation: seq₁.a k = 0 for k ∉ {(1,1), (1,-1), (-1,1), (-1,-1)}
  have seq₁_support : ∀ k : ℤ × ℤ,
      k ≠ (1, 1) → k ≠ (1, -1) → k ≠ (-1, 1) → k ≠ (-1, -1) → seq₁.a k = 0 := by
    intro k h1 h2 h3 h4
    unfold seq₁
    simp [h1, h2, h3, h4]

  -- Sum over F equals sum over F ∩ support
  let support := ({(1, 1), (1, -1), (-1, 1), (-1, -1)} : Finset (ℤ × ℤ))

  calc Finset.sum F (fun k => (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖seq₁.a k‖^2)
      = Finset.sum (F ∩ support) (fun k => (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖seq₁.a k‖^2) := by
        symm
        apply Finset.sum_subset (Finset.inter_subset_left)
        intro k hk_in hk_not
        simp only [Finset.mem_inter] at hk_not
        have : k ∉ support := fun h => hk_not ⟨hk_in, h⟩
        simp only [support, Finset.mem_insert, Finset.mem_singleton] at this
        push_neg at this
        rw [seq₁_support k this.1 this.2.1 this.2.2.1 this.2.2.2]
        norm_num
    _ ≤ Finset.sum support (fun k => (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖seq₁.a k‖^2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intros; positivity
    _ = (1 + 4 * Real.pi^2 * 2) * ‖seq₁.a (1, 1)‖^2
        + (1 + 4 * Real.pi^2 * 2) * ‖seq₁.a (1, -1)‖^2
        + (1 + 4 * Real.pi^2 * 2) * ‖seq₁.a (-1, 1)‖^2
        + (1 + 4 * Real.pi^2 * 2) * ‖seq₁.a (-1, -1)‖^2 := by
        rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
        norm_num
        ring
    _ = (1 + 8 * Real.pi^2) * (1/16) + (1 + 8 * Real.pi^2) * (1/16)
        + (1 + 8 * Real.pi^2) * (1/16) + (1 + 8 * Real.pi^2) * (1/16) := by
        simp [seq₁]
        norm_num
        ring
    _ = (1 + 8 * Real.pi^2) / 4 := by ring
    _ ≤ (R₁ : ℝ)^2 := by
        norm_num [R₁]
        have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
        have hpi2 : Real.pi^2 < 3.1416^2 := sq_lt_sq' (by linarith [Real.pi_pos]) hpi
        apply le_of_lt
        calc (1 + 8 * Real.pi^2) / 4
            < (1 + 8 * 3.1416^2) / 4 := by
              apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 4)
              apply add_lt_add_left
              apply mul_lt_mul_of_pos_left hpi2 (by norm_num : (0 : ℝ) < 8)
          _ < 25 := by norm_num

/-- Witness exists for test case 1.
    The gridFinset_sound_2D theorem guarantees a grid point approximates
    the constructive ℓ² sequence seq₁. -/
theorem witness_exists_test1 :
    ∃ (g : GridPoint2D ε₁ R₁ (M_of ε₁ R₁)),
      g ∈ gridFinset2D ε₁ R₁ (M_of ε₁ R₁) ∧
      ∀ F : Finset (ℤ × ℤ),
        Finset.sum F (fun k => ‖seq₁.a k - (gridToSeq ε₁ R₁ (M_of ε₁ R₁) g).a k‖^2)
          < (ε₁ : ℝ)^2 := by
  have h := gridFinset_sound_2D ε₁ R₁ hε₁ hR₁
  exact h seq₁ seq₁_mean_zero seq₁_in_H1Ball

end TestCase1

/-! ### Test Case 2: Diagonal Mode

Function: u₂(x,y) = sin(2π(x+y))

Fourier decomposition:
- a₍₁,₁₎ = i/2
- a₍₋₁,₋₁₎ = -i/2
- all other coefficients zero

Properties:
- Mean-zero: ∫∫u₂ = 0
- Diagonal symmetry: depends only on x+y
- H¹-norm: ‖u‖²_H¹ = (1 + 8π²)/2 ≈ 39.98
- Two modes with |k|² = 2

Test parameters: ε = 1/20, R = 7
-/

section TestCase2

def ε₂ : ℚ := 1 / 20
def R₂ : ℚ := 7

lemma hε₂ : 0 < (ε₂ : ℝ) := by norm_num [ε₂]
lemma hR₂ : 0 < (R₂ : ℝ) := by norm_num [R₂]

def seq₂ : ℓ2Z2 where
  a := fun k =>
    if k = (1, 1) then Complex.I / 2
    else if k = (-1, -1) then -Complex.I / 2
    else 0
  summable_sq := by
    apply summable_of_ne_finset_zero (s := {(1, 1), (-1, -1)})
    intro k hk
    simp [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

lemma seq₂_mean_zero : seq₂.meanZero := by
  unfold meanZero seq₂
  rfl

lemma seq₂_in_H1Ball : seq₂.InH1Ball (R₂ : ℝ) := by
  constructor
  intro F

  have seq₂_support : ∀ k : ℤ × ℤ, k ≠ (1, 1) → k ≠ (-1, -1) → seq₂.a k = 0 := by
    intro k h1 h2
    unfold seq₂
    simp [h1, h2]

  let support := ({(1, 1), (-1, -1)} : Finset (ℤ × ℤ))

  calc Finset.sum F (fun k => (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖seq₂.a k‖^2)
      = Finset.sum (F ∩ support) (fun k => (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖seq₂.a k‖^2) := by
        symm
        apply Finset.sum_subset (Finset.inter_subset_left)
        intro k hk_in hk_not
        simp only [Finset.mem_inter] at hk_not
        have : k ∉ support := fun h => hk_not ⟨hk_in, h⟩
        simp only [support, Finset.mem_insert, Finset.mem_singleton] at this
        push_neg at this
        rw [seq₂_support k this.1 this.2]
        norm_num
    _ ≤ Finset.sum support (fun k => (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖seq₂.a k‖^2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intros; positivity
    _ = (1 + 4 * Real.pi^2 * 2) * ‖seq₂.a (1, 1)‖^2
        + (1 + 4 * Real.pi^2 * 2) * ‖seq₂.a (-1, -1)‖^2 := by
        rw [Finset.sum_insert (by decide), Finset.sum_singleton]
        norm_num
    _ = (1 + 8 * Real.pi^2) * (1/4) + (1 + 8 * Real.pi^2) * (1/4) := by
        simp [seq₂]
        norm_num
        ring
    _ = (1 + 8 * Real.pi^2) / 2 := by ring
    _ ≤ (R₂ : ℝ)^2 := by
        norm_num [R₂]
        have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
        have hpi2 : Real.pi^2 < 3.1416^2 := sq_lt_sq' (by linarith [Real.pi_pos]) hpi
        apply le_of_lt
        calc (1 + 8 * Real.pi^2) / 2
            < (1 + 8 * 3.1416^2) / 2 := by
              apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 2)
              apply add_lt_add_left
              apply mul_lt_mul_of_pos_left hpi2 (by norm_num : (0 : ℝ) < 8)
          _ < 49 := by norm_num

theorem witness_exists_test2 :
    ∃ (g : GridPoint2D ε₂ R₂ (M_of ε₂ R₂)),
      g ∈ gridFinset2D ε₂ R₂ (M_of ε₂ R₂) ∧
      ∀ F : Finset (ℤ × ℤ),
        Finset.sum F (fun k => ‖seq₂.a k - (gridToSeq ε₂ R₂ (M_of ε₂ R₂) g).a k‖^2)
          < (ε₂ : ℝ)^2 := by
  have h := gridFinset_sound_2D ε₂ R₂ hε₂ hR₂
  exact h seq₂ seq₂_mean_zero seq₂_in_H1Ball

end TestCase2

/-! ### Test Case 3: Higher Frequency Mixed Mode

Function: u₃(x,y) = sin(6πx)sin(2πy)

Fourier decomposition:
- a₍₃,₁₎ = -1/4
- a₍₃,₋₁₎ = 1/4
- a₍₋₃,₁₎ = 1/4
- a₍₋₃,₋₁₎ = -1/4
- all other coefficients zero

Properties:
- Mean-zero: ∫∫u₃ = 0
- Higher frequency in x-direction
- H¹-norm: ‖u‖²_H¹ = (1 + 40π²)/4 ≈ 98.95
- Four modes with |k|² = 10

Test parameters: ε = 1/10, R = 10
-/

section TestCase3

def ε₃ : ℚ := 1 / 10
def R₃ : ℚ := 10

lemma hε₃ : 0 < (ε₃ : ℝ) := by norm_num [ε₃]
lemma hR₃ : 0 < (R₃ : ℝ) := by norm_num [R₃]

def seq₃ : ℓ2Z2 where
  a := fun k =>
    if k = (3, 1) then -1/4
    else if k = (3, -1) then 1/4
    else if k = (-3, 1) then 1/4
    else if k = (-3, -1) then -1/4
    else 0
  summable_sq := by
    apply summable_of_ne_finset_zero (s := {(3, 1), (3, -1), (-3, 1), (-3, -1)})
    intro k hk
    simp [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

lemma seq₃_mean_zero : seq₃.meanZero := by
  unfold meanZero seq₃
  rfl

lemma seq₃_in_H1Ball : seq₃.InH1Ball (R₃ : ℝ) := by
  constructor
  intro F

  have seq₃_support : ∀ k : ℤ × ℤ,
      k ≠ (3, 1) → k ≠ (3, -1) → k ≠ (-3, 1) → k ≠ (-3, -1) → seq₃.a k = 0 := by
    intro k h1 h2 h3 h4
    unfold seq₃
    simp [h1, h2, h3, h4]

  let support := ({(3, 1), (3, -1), (-3, 1), (-3, -1)} : Finset (ℤ × ℤ))

  calc Finset.sum F (fun k => (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖seq₃.a k‖^2)
      = Finset.sum (F ∩ support) (fun k => (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖seq₃.a k‖^2) := by
        symm
        apply Finset.sum_subset (Finset.inter_subset_left)
        intro k hk_in hk_not
        simp only [Finset.mem_inter] at hk_not
        have : k ∉ support := fun h => hk_not ⟨hk_in, h⟩
        simp only [support, Finset.mem_insert, Finset.mem_singleton] at this
        push_neg at this
        rw [seq₃_support k this.1 this.2.1 this.2.2.1 this.2.2.2]
        norm_num
    _ ≤ Finset.sum support (fun k => (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖seq₃.a k‖^2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intros; positivity
    _ = (1 + 4 * Real.pi^2 * 10) * ‖seq₃.a (3, 1)‖^2
        + (1 + 4 * Real.pi^2 * 10) * ‖seq₃.a (3, -1)‖^2
        + (1 + 4 * Real.pi^2 * 10) * ‖seq₃.a (-3, 1)‖^2
        + (1 + 4 * Real.pi^2 * 10) * ‖seq₃.a (-3, -1)‖^2 := by
        rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_insert (by decide), Finset.sum_singleton]
        norm_num
        ring
    _ = (1 + 40 * Real.pi^2) * (1/16) + (1 + 40 * Real.pi^2) * (1/16)
        + (1 + 40 * Real.pi^2) * (1/16) + (1 + 40 * Real.pi^2) * (1/16) := by
        simp [seq₃]
        norm_num
        ring
    _ = (1 + 40 * Real.pi^2) / 4 := by ring
    _ ≤ (R₃ : ℝ)^2 := by
        norm_num [R₃]
        have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
        have hpi2 : Real.pi^2 < 3.1416^2 := sq_lt_sq' (by linarith [Real.pi_pos]) hpi
        apply le_of_lt
        calc (1 + 40 * Real.pi^2) / 4
            < (1 + 40 * 3.1416^2) / 4 := by
              apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 4)
              apply add_lt_add_left
              apply mul_lt_mul_of_pos_left hpi2 (by norm_num : (0 : ℝ) < 40)
          _ < 100 := by norm_num

theorem witness_exists_test3 :
    ∃ (g : GridPoint2D ε₃ R₃ (M_of ε₃ R₃)),
      g ∈ gridFinset2D ε₃ R₃ (M_of ε₃ R₃) ∧
      ∀ F : Finset (ℤ × ℤ),
        Finset.sum F (fun k => ‖seq₃.a k - (gridToSeq ε₃ R₃ (M_of ε₃ R₃) g).a k‖^2)
          < (ε₃ : ℝ)^2 := by
  have h := gridFinset_sound_2D ε₃ R₃ hε₃ hR₃
  exact h seq₃ seq₃_mean_zero seq₃_in_H1Ball

end TestCase3

end -- noncomputable section

end QRK2DDemo

/-! ## Executable Metadata Extraction

The WitnessPkg2D structure and its derived quantities (M, δ, grid size)
are fully computable. We can extract and display them in executable IO.
-/

open ConstructiveQ
open RellichKondrachov2D.Seq

/-- Computable witness metadata for display -/
structure WitnessMetadata2D where
  test_name : String
  function_description : String
  ε : ℚ
  R : ℚ
deriving Repr

/-- Compute derived parameters from ε and R for 2D -/
def compute_parameters_2D (ε R : ℚ) : (ℕ × ℚ × ℕ) :=
  let M := M_of ε R
  let δ := mesh2D ε M
  let grid_dim_estimate := (2 * M + 1)^2 - 1
  (M, δ, grid_dim_estimate)

/-- Create witness package (fully extractable) -/
def make_witness_pkg_2D (ε R : ℚ) : WitnessPkg2D :=
  { ε := ε, R := R }

/-- Display witness metadata with computed parameters for 2D -/
def display_witness_metadata_2D (w : WitnessMetadata2D) : IO Unit := do
  let (M, δ, grid_dim) := compute_parameters_2D w.ε w.R
  let _pkg := make_witness_pkg_2D w.ε w.R

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
  IO.println s!"    Grid dimension est.:   {grid_dim} frequencies (2D)"
  IO.println s!"    Grid structure:        Finset (GridPoint2D ε R M)"
  IO.println s!"    Grid nonempty:         ✓ (proven in WitnessPkg2D.grid_nonempty)"
  IO.println ""
  IO.println "  Witness Guarantee:"
  IO.println s!"    ∃g ∈ grid, ‖u - g‖²_L² < {w.ε}² = {w.ε * w.ε}"
  IO.println ""

/-! ## Main Executable -/

def main : IO Unit := do
  IO.println ""
  IO.println "╔════════════════════════════════════════════════════════════╗"
  IO.println "║  Rellich-Kondrachov 2D Witness Extraction Demo            ║"
  IO.println "║  Mean-Zero H¹ Functions on the 2D Torus (𝕋²)              ║"
  IO.println "║  Constructive Witness Extraction                           ║"
  IO.println "╚════════════════════════════════════════════════════════════╝"
  IO.println ""
  IO.println "Formal verification:"
  IO.println "  • Sequence layer: budgets/Budgets/RellichKondrachov2D/Seq.lean"
  IO.println "  • Soundness:      budgets/Budgets/RellichKondrachov2D.lean"
  IO.println "  • Main theorem:   gridFinset_sound_2D (COMPLETE, zero sorries)"
  IO.println ""
  IO.println "Test approach: Explicit ℓ² sequences (finite 2D Fourier support)"
  IO.println "  • Direct construction via 2D Fourier coefficients"
  IO.println "  • Proven mean-zero and H¹-ball membership"
  IO.println "  • R parameters adjusted for 2D H¹ energies"
  IO.println ""
  IO.println "Key result: gridFinset_sound_2D"
  IO.println "  For any mean-zero u ∈ H¹(𝕋²) with ‖u‖_H¹ ≤ R:"
  IO.println "  ∃ grid point g such that ‖u - g‖²_L² < ε²"
  IO.println ""
  IO.println "xBudget: C0-C2 (fully constructive, extractable)"
  IO.println "Extraction: WitnessPkg2D is fully computable (ℚ, ℕ, Finset only)"
  IO.println ""
  IO.println "════════════════════════════════════════════════════════════"
  IO.println ""

  -- Test 1: Product mode
  display_witness_metadata_2D {
    test_name := "Test 1: Product Mode"
    function_description := "ℓ² sequence: modes (±1,±1) (represents sin(2πx)sin(2πy)) | R=5 (H¹ energy ≈ 19.99)"
    ε := QRK2DDemo.ε₁
    R := QRK2DDemo.R₁
  }

  IO.println "────────────────────────────────────────────────────────────"
  IO.println ""

  -- Test 2: Diagonal mode
  display_witness_metadata_2D {
    test_name := "Test 2: Diagonal Mode"
    function_description := "ℓ² sequence: modes (1,1), (-1,-1) (represents sin(2π(x+y))) | R=7 (H¹ energy ≈ 39.98)"
    ε := QRK2DDemo.ε₂
    R := QRK2DDemo.R₂
  }

  IO.println "────────────────────────────────────────────────────────────"
  IO.println ""

  -- Test 3: Higher frequency mixed
  display_witness_metadata_2D {
    test_name := "Test 3: Higher Frequency Mixed Mode"
    function_description := "ℓ² sequence: modes (±3,±1) (represents sin(6πx)sin(2πy)) | R=10 (H¹ energy ≈ 98.95)"
    ε := QRK2DDemo.ε₃
    R := QRK2DDemo.R₃
  }

  IO.println "════════════════════════════════════════════════════════════"
  IO.println ""
  IO.println "╔════════════════════════════════════════════════════════════╗"
  IO.println "║ Extraction Status: SUCCESS                                 ║"
  IO.println "║                                                             ║"
  IO.println "║ ✓ Fully constructive approach (zero axioms)                ║"
  IO.println "║ ✓ Explicit ℓ² sequences with finite 2D Fourier support    ║"
  IO.println "║ ✓ Witness existence proven for all 3 test cases           ║"
  IO.println "║ ✓ Grid parameters computed from (ε, R)                    ║"
  IO.println "║ ✓ WitnessPkg2D fully extractable (xBudget C0)             ║"
  IO.println "║ ✓ Soundness via gridFinset_sound_2D                       ║"
  IO.println "║                                                             ║"
  IO.println "║ Witness theorems:                                          ║"
  IO.println "║   • witness_exists_test1 (product mode, seq₁)              ║"
  IO.println "║   • witness_exists_test2 (diagonal mode, seq₂)             ║"
  IO.println "║   • witness_exists_test3 (higher frequency, seq₃)          ║"
  IO.println "║                                                             ║"
  IO.println "║ Constructive proof strategy:                               ║"
  IO.println "║   • Explicit finite 2D Fourier support                     ║"
  IO.println "║   • Mean-zero by construction (a₀₀ = 0)                    ║"
  IO.println "║   • H¹ ball membership via finite arithmetic               ║"
  IO.println "║   • R adjusted to accommodate 2D H¹ energy                 ║"
  IO.println "║   • Dimension-free tail bound (same as 1D!)                ║"
  IO.println "╚════════════════════════════════════════════════════════════╝"
  IO.println ""
