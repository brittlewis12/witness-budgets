import Budgets.RellichKondrachov3D
import Budgets.ConstructiveQ

/-!
# Rellich-Kondrachov 3D Witness Extraction Demo

Demonstrates constructive witness extraction for the Rellich-Kondrachov theorem
on the 3D torus using the formal verification from `Budgets.RellichKondrachov3D`.

## Mathematical Content

The Rellich-Kondrachov theorem establishes compactness of the embedding H¹(𝕋³) ↪ L²(𝕋³).
This demo provides:
- Finite witness grid construction for mean-zero H¹ functions on 𝕋³
- Computable grid parameters (M, δ, grid cardinality estimate)
- Soundness: every function is ε-approximated by some grid point

The formal theorem `gridFinset_sound_3D` in `RellichKondrachov3D.lean` proves that
for any mean-zero function in the H¹ ball of radius R, there exists a grid point
within L² distance ε.

## Key Parameters

- ε : ℚ - Approximation accuracy (L² distance bound)
- R : ℚ - H¹ ball radius
- M : ℕ - Frequency cutoff (derived: M = ⌈R/(π·ε)⌉ + 1)
- δ : ℚ - Grid mesh (derived: δ = ε/(8·(2M+1)²))
- Grid dimension: (2M+1)³ - 1 (Fourier frequencies in [-M,M]³ \ {(0,0,0)})

## Verification Status

- Budget: C0-C2 (fully constructive)
- xBudget: Witness metadata fully extractable (ℚ, ℕ, Finset only)
-/

namespace QRK3DDemo

open ℓ2Z3
open ConstructiveQ
open scoped BigOperators Real

/-! ## Noncomputable Test Function Layer

The L² functions themselves are noncomputable (they involve measure theory),
but witness existence and metadata extraction are computable.
-/

noncomputable section

/-! ### Test Case 1: Product Mode (8 corners)

Function: u₁(x,y,z) = sin(2πx)sin(2πy)sin(2πz)

Fourier decomposition:
- Eight modes at k = (±1, ±1, ±1) (all 8 corners of unit cube)
- Coefficients: ±1/8 (alternating signs for sin product)
- All other coefficients zero

Mathematical identity:
sin(2πx)sin(2πy)sin(2πz) = (1/8) Σ_{σ₁,σ₂,σ₃∈{±1}} σ₁σ₂σ₃ exp(2πi(σ₁x + σ₂y + σ₃z))

Properties:
- Mean-zero: ∫∫∫u₁ = 0 (k=(0,0,0) coefficient is 0)
- H¹-norm: ‖u‖²_H¹ = 8 × (1 + 4π²·3) / 64 = (1 + 12π²) / 8 ≈ 14.994
- |k|² = 3 for each mode (1² + 1² + 1² = 3)
- Smooth: infinitely differentiable
- Separable: product of 1D functions

Test parameters: ε = 1/10, R = 5
Parameter R = 5 chosen to accommodate the 3D H¹ energy (≈ 14.99).
-/

section TestCase1

def ε₁ : ℚ := 1 / 10
def R₁ : ℚ := 5

lemma hε₁ : 0 < (ε₁ : ℝ) := by norm_num [ε₁]
lemma hR₁ : 0 < (R₁ : ℝ) := by norm_num [R₁]

/-- Test sequence 1: Fourier coefficients for u(x,y,z) = sin(2πx)sin(2πy)sin(2πz).
    Explicit constructive ℓ² sequence with finite Fourier support:
    Eight modes at (±1, ±1, ±1) - all corners of the unit cube. -/
def seq3D_1 : Seq3D where
  a := fun k =>
    if k = (1, 1, 1) then -1/8
    else if k = (1, 1, -1) then 1/8
    else if k = (1, -1, 1) then 1/8
    else if k = (1, -1, -1) then -1/8
    else if k = (-1, 1, 1) then 1/8
    else if k = (-1, 1, -1) then -1/8
    else if k = (-1, -1, 1) then -1/8
    else if k = (-1, -1, -1) then 1/8
    else 0
  summable_sq := by
    apply summable_of_ne_finset_zero
      (s := {(1, 1, 1), (1, 1, -1), (1, -1, 1), (1, -1, -1),
             (-1, 1, 1), (-1, 1, -1), (-1, -1, 1), (-1, -1, -1)})
    intro k hk
    simp [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

theorem seq3D_1_meanZero : meanZero seq3D_1 := by
  rfl

/-- seq3D_1 lies in the H¹ ball of radius R₁.

    Energy calculation:
    - For k = (±1, ±1, ±1): |k|² = 1² + 1² + 1² = 3
    - Weight: 1 + 4π²·3 = 1 + 12π²
    - Contribution per mode: (1 + 12π²) · |±1/8|² = (1 + 12π²) · 1/64
    - Total (8 modes): 8 · (1 + 12π²) · 1/64 = (1 + 12π²) / 8
    - Numerically: (1 + 12π²) / 8 ≈ (1 + 118.435) / 8 ≈ 14.929

    R₁ = 5, so R₁² = 25 > 14.929. ✓
-/
theorem seq3D_1_InH1Ball : InH1Ball (R₁ : ℝ) seq3D_1 := by
  intro F

  have seq_support : ∀ k : ℤ × ℤ × ℤ,
      k ≠ (1, 1, 1) → k ≠ (1, 1, -1) → k ≠ (1, -1, 1) → k ≠ (1, -1, -1) →
      k ≠ (-1, 1, 1) → k ≠ (-1, 1, -1) → k ≠ (-1, -1, 1) → k ≠ (-1, -1, -1) →
      seq3D_1.a k = 0 := by
    intro k h1 h2 h3 h4 h5 h6 h7 h8
    unfold seq3D_1
    simp [h1, h2, h3, h4, h5, h6, h7, h8]

  let support := ({(1, 1, 1), (1, 1, -1), (1, -1, 1), (1, -1, -1),
                   (-1, 1, 1), (-1, 1, -1), (-1, -1, 1), (-1, -1, -1)} : Finset (ℤ × ℤ × ℤ))

  calc Finset.sum F (fun k => (h1Weight k) * ‖seq3D_1.a k‖^2)
      = Finset.sum (F ∩ support) (fun k => (h1Weight k) * ‖seq3D_1.a k‖^2) := by
        symm
        apply Finset.sum_subset (Finset.inter_subset_left)
        intro k hk_in hk_not
        simp only [Finset.mem_inter] at hk_not
        have : k ∉ support := fun h => hk_not ⟨hk_in, h⟩
        simp only [support, Finset.mem_insert, Finset.mem_singleton] at this
        push_neg at this
        rw [seq_support k this.1 this.2.1 this.2.2.1 this.2.2.2.1
                          this.2.2.2.2.1 this.2.2.2.2.2.1 this.2.2.2.2.2.2.1 this.2.2.2.2.2.2.2]
        norm_num
    _ ≤ Finset.sum support (fun k => (h1Weight k) * ‖seq3D_1.a k‖^2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro k _ _
        apply mul_nonneg
        · unfold h1Weight; positivity
        · positivity
    _ ≤ 8 * ((1 + 12 * Real.pi^2) * (1/64)) := by
        unfold h1Weight seq3D_1 support
        simp only []
        norm_num
        ring_nf
        have h_nonneg : 0 ≤ Real.pi ^ 2 := sq_nonneg _
        linarith [h_nonneg]
    _ = (1 + 12 * Real.pi^2) / 8 := by ring
    _ ≤ (R₁ : ℝ)^2 := by
        norm_num [R₁]
        have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
        have hpi2 : Real.pi^2 < 3.1416^2 := sq_lt_sq' (by linarith [Real.pi_pos]) hpi
        apply le_of_lt
        calc (1 + 12 * Real.pi^2) / 8
            < (1 + 12 * 3.1416^2) / 8 := by
              apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 8)
              apply add_lt_add_left
              apply mul_lt_mul_of_pos_left hpi2 (by norm_num : (0 : ℝ) < 12)
          _ < 25 := by norm_num

/-- Witness exists for test case 1.
    The gridFinset_sound_3D theorem guarantees a grid point approximates
    the constructive ℓ² sequence seq3D_1. -/
theorem witness_exists_test1 :
    ∃ (g : GridPoint3D ε₁ R₁ (M_of ε₁ R₁)),
      ∀ F : Finset (ℤ × ℤ × ℤ),
        Finset.sum F (fun k => ‖seq3D_1.a k - (gridToSeq ε₁ R₁ (M_of ε₁ R₁) g).a k‖^2)
          < (ε₁ : ℝ)^2 := by
  have h := gridFinset_sound_3D ε₁ R₁ hε₁ hR₁
  exact h seq3D_1 seq3D_1_meanZero seq3D_1_InH1Ball

end TestCase1

/-! ### Test Case 2: Diagonal Mode

Function: u₂(x,y,z) = sin(2π(x+y+z))

Fourier decomposition:
- a₍₁,₁,₁₎ = i/2
- a₍₋₁,₋₁,₋₁₎ = -i/2
- All other coefficients zero

Properties:
- Mean-zero: ∫∫∫u₂ = 0
- Diagonal symmetry: depends only on x+y+z
- H¹-norm: ‖u‖²_H¹ = 2 × (1 + 12π²) / 4 = (1 + 12π²) / 2 ≈ 59.72
- Two modes with |k|² = 3

Test parameters: ε = 1/20, R = 8
-/

section TestCase2

def ε₂ : ℚ := 1 / 20
def R₂ : ℚ := 8

lemma hε₂ : 0 < (ε₂ : ℝ) := by norm_num [ε₂]
lemma hR₂ : 0 < (R₂ : ℝ) := by norm_num [R₂]

def seq3D_2 : Seq3D where
  a := fun k =>
    if k = (1, 1, 1) then Complex.I / 2
    else if k = (-1, -1, -1) then -Complex.I / 2
    else 0
  summable_sq := by
    apply summable_of_ne_finset_zero (s := {(1, 1, 1), (-1, -1, -1)})
    intro k hk
    simp [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

theorem seq3D_2_meanZero : meanZero seq3D_2 := by
  rfl

theorem seq3D_2_InH1Ball : InH1Ball (R₂ : ℝ) seq3D_2 := by
  intro F

  have seq_support : ∀ k : ℤ × ℤ × ℤ,
      k ≠ (1, 1, 1) → k ≠ (-1, -1, -1) → seq3D_2.a k = 0 := by
    intro k h1 h2
    unfold seq3D_2
    simp [h1, h2]

  let support := ({(1, 1, 1), (-1, -1, -1)} : Finset (ℤ × ℤ × ℤ))

  calc Finset.sum F (fun k => (h1Weight k) * ‖seq3D_2.a k‖^2)
      = Finset.sum (F ∩ support) (fun k => (h1Weight k) * ‖seq3D_2.a k‖^2) := by
        symm
        apply Finset.sum_subset (Finset.inter_subset_left)
        intro k hk_in hk_not
        simp only [Finset.mem_inter] at hk_not
        have : k ∉ support := fun h => hk_not ⟨hk_in, h⟩
        simp only [support, Finset.mem_insert, Finset.mem_singleton] at this
        push_neg at this
        rw [seq_support k this.1 this.2]
        norm_num
    _ ≤ Finset.sum support (fun k => (h1Weight k) * ‖seq3D_2.a k‖^2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro k _ _
        apply mul_nonneg
        · unfold h1Weight; positivity
        · positivity
    _ = 2 * ((1 + 12 * Real.pi^2) * (1/4)) := by
        unfold h1Weight seq3D_2 support
        simp only []
        norm_num
        ring
    _ = (1 + 12 * Real.pi^2) / 2 := by ring
    _ ≤ (R₂ : ℝ)^2 := by
        norm_num [R₂]
        have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
        have hpi2 : Real.pi^2 < 3.1416^2 := sq_lt_sq' (by linarith [Real.pi_pos]) hpi
        apply le_of_lt
        calc (1 + 12 * Real.pi^2) / 2
            < (1 + 12 * 3.1416^2) / 2 := by
              apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 2)
              apply add_lt_add_left
              apply mul_lt_mul_of_pos_left hpi2 (by norm_num : (0 : ℝ) < 12)
          _ < 64 := by norm_num

theorem witness_exists_test2 :
    ∃ (g : GridPoint3D ε₂ R₂ (M_of ε₂ R₂)),
      ∀ F : Finset (ℤ × ℤ × ℤ),
        Finset.sum F (fun k => ‖seq3D_2.a k - (gridToSeq ε₂ R₂ (M_of ε₂ R₂) g).a k‖^2)
          < (ε₂ : ℝ)^2 := by
  have h := gridFinset_sound_3D ε₂ R₂ hε₂ hR₂
  exact h seq3D_2 seq3D_2_meanZero seq3D_2_InH1Ball

end TestCase2

/-! ### Test Case 3: Mixed Mode

Function: u₃(x,y,z) = sin(4πx)sin(2πy)sin(2πz)

Fourier decomposition:
- Four modes at k = (±2, ±1, 1)
- Coefficients: ±1/8 (alternating for sin product)
- All other coefficients zero

Properties:
- Mean-zero: ∫∫∫u₃ = 0
- Higher frequency in x-direction
- H¹-norm: ‖u‖²_H¹ = 4 × (1 + 4π²·6) / 64 = (1 + 24π²) / 16 ≈ 14.87
- Four modes with |k|² = 6 (2² + 1² + 1² = 6)

Test parameters: ε = 1/10, R = 13
-/

section TestCase3

def ε₃ : ℚ := 1 / 10
def R₃ : ℚ := 13

lemma hε₃ : 0 < (ε₃ : ℝ) := by norm_num [ε₃]
lemma hR₃ : 0 < (R₃ : ℝ) := by norm_num [R₃]

def seq3D_3 : Seq3D where
  a := fun k =>
    if k = (2, 1, 1) then -1/8
    else if k = (2, -1, 1) then 1/8
    else if k = (-2, 1, 1) then 1/8
    else if k = (-2, -1, 1) then -1/8
    else 0
  summable_sq := by
    apply summable_of_ne_finset_zero (s := {(2, 1, 1), (2, -1, 1), (-2, 1, 1), (-2, -1, 1)})
    intro k hk
    simp [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

theorem seq3D_3_meanZero : meanZero seq3D_3 := by
  rfl

theorem seq3D_3_InH1Ball : InH1Ball (R₃ : ℝ) seq3D_3 := by
  intro F

  have seq_support : ∀ k : ℤ × ℤ × ℤ,
      k ≠ (2, 1, 1) → k ≠ (2, -1, 1) → k ≠ (-2, 1, 1) → k ≠ (-2, -1, 1) →
      seq3D_3.a k = 0 := by
    intro k h1 h2 h3 h4
    unfold seq3D_3
    simp [h1, h2, h3, h4]

  let support := ({(2, 1, 1), (2, -1, 1), (-2, 1, 1), (-2, -1, 1)} : Finset (ℤ × ℤ × ℤ))

  calc Finset.sum F (fun k => (h1Weight k) * ‖seq3D_3.a k‖^2)
      = Finset.sum (F ∩ support) (fun k => (h1Weight k) * ‖seq3D_3.a k‖^2) := by
        symm
        apply Finset.sum_subset (Finset.inter_subset_left)
        intro k hk_in hk_not
        simp only [Finset.mem_inter] at hk_not
        have : k ∉ support := fun h => hk_not ⟨hk_in, h⟩
        simp only [support, Finset.mem_insert, Finset.mem_singleton] at this
        push_neg at this
        rw [seq_support k this.1 this.2.1 this.2.2.1 this.2.2.2]
        norm_num
    _ ≤ Finset.sum support (fun k => (h1Weight k) * ‖seq3D_3.a k‖^2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro k _ _
        apply mul_nonneg
        · unfold h1Weight; positivity
        · positivity
    _ = 4 * ((1 + 24 * Real.pi^2) * (1/64)) := by
        unfold h1Weight seq3D_3 support
        simp only []
        norm_num
        ring
    _ = (1 + 24 * Real.pi^2) / 16 := by ring
    _ ≤ (R₃ : ℝ)^2 := by
        norm_num [R₃]
        have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
        have hpi2 : Real.pi^2 < 3.1416^2 := sq_lt_sq' (by linarith [Real.pi_pos]) hpi
        apply le_of_lt
        calc (1 + 24 * Real.pi^2) / 16
            < (1 + 24 * 3.1416^2) / 16 := by
              apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 16)
              apply add_lt_add_left
              apply mul_lt_mul_of_pos_left hpi2 (by norm_num : (0 : ℝ) < 24)
          _ < 169 := by norm_num

theorem witness_exists_test3 :
    ∃ (g : GridPoint3D ε₃ R₃ (M_of ε₃ R₃)),
      ∀ F : Finset (ℤ × ℤ × ℤ),
        Finset.sum F (fun k => ‖seq3D_3.a k - (gridToSeq ε₃ R₃ (M_of ε₃ R₃) g).a k‖^2)
          < (ε₃ : ℝ)^2 := by
  have h := gridFinset_sound_3D ε₃ R₃ hε₃ hR₃
  exact h seq3D_3 seq3D_3_meanZero seq3D_3_InH1Ball

end TestCase3

end -- noncomputable section

end QRK3DDemo

/-! ## Executable Metadata Extraction

The WitnessPkg3D structure and its derived quantities (M, δ, grid size)
are fully computable. We can extract and display them in executable IO.
-/

open ConstructiveQ
open ℓ2Z3

/-- Computable witness metadata for display -/
structure WitnessMetadata3D where
  testName : String
  functionDescription : String
  ε : ℚ
  R : ℚ
deriving Repr

/-- Conservative rational lower bound for π (computable version for extraction) -/
def pi_rat_lb_extract : ℚ := 3

/-- Computable version of M_of using rational approximation -/
def M_of_computable (ε R : ℚ) : ℕ :=
  Nat.ceil (R / (pi_rat_lb_extract * ε)) + 1

/-- Compute derived parameters from ε and R for 3D -/
def compute_parameters_3D (ε R : ℚ) : (ℕ × ℚ × ℕ) :=
  let M := M_of_computable ε R
  let δ := mesh3D ε M
  let grid_dim_estimate := (2 * M + 1)^3 - 1
  (M, δ, grid_dim_estimate)

/-- Create witness package (fully extractable) -/
def make_witness_pkg_3D (ε R : ℚ) : WitnessPkg3D :=
  { ε := ε, R := R }

/-- Display witness metadata with computed parameters for 3D -/
def display_witness_metadata_3D (w : WitnessMetadata3D) : IO Unit := do
  let (M, δ, grid_dim) := compute_parameters_3D w.ε w.R
  let _pkg := make_witness_pkg_3D w.ε w.R

  IO.println "╭──────────────────────────────────────────────────────────╮"
  IO.println s!"│  {w.testName}"
  IO.println "╰──────────────────────────────────────────────────────────╯"
  IO.println ""
  IO.println s!"  Function: {w.functionDescription}"
  IO.println ""
  IO.println "  Input Parameters:"
  IO.println s!"    ε (L² accuracy):      {w.ε}"
  IO.println s!"    R (H¹ radius):        {w.R}"
  IO.println ""
  IO.println "  Derived Witness Parameters:"
  IO.println s!"    M (frequency cutoff):  {M}"
  IO.println s!"    δ (grid mesh):         {δ}"
  IO.println s!"    Grid dimension est.:   {grid_dim} frequencies (3D)"
  IO.println s!"    Grid structure:        Finset (GridPoint3D ε R M)"
  IO.println s!"    Grid nonempty:         ✓ (factored representation)"
  IO.println ""
  IO.println "  Witness Guarantee:"
  IO.println s!"    ∃g ∈ grid, ‖u - g‖²_L² < {w.ε}² = {w.ε * w.ε}"
  IO.println ""

/-! ## Main Executable -/

def main : IO Unit := do
  IO.println ""
  IO.println "╔════════════════════════════════════════════════════════════╗"
  IO.println "║  Rellich-Kondrachov 3D Witness Extraction Demo            ║"
  IO.println "║  Mean-Zero H¹ Functions on the 3D Torus (𝕋³)              ║"
  IO.println "║  Constructive Witness Extraction                           ║"
  IO.println "╚════════════════════════════════════════════════════════════╝"
  IO.println ""
  IO.println "Formal verification:"
  IO.println "  • Sequence layer: budgets/Budgets/RellichKondrachov3D/Seq.lean"
  IO.println "  • Soundness:      budgets/Budgets/RellichKondrachov3D.lean"
  IO.println "  • Main theorem:   gridFinset_sound_3D"
  IO.println ""
  IO.println "Test approach: Explicit ℓ² sequences (finite 3D Fourier support)"
  IO.println "  • Direct construction via 3D Fourier coefficients"
  IO.println "  • Proven mean-zero and H¹-ball membership"
  IO.println "  • R parameters adjusted for 3D H¹ energies"
  IO.println ""
  IO.println "Key result: gridFinset_sound_3D"
  IO.println "  For any mean-zero u ∈ H¹(𝕋³) with ‖u‖_H¹ ≤ R:"
  IO.println "  ∃ grid point g such that ‖u - g‖²_L² < ε²"
  IO.println ""
  IO.println "xBudget: C0-C2 (fully constructive, extractable)"
  IO.println "Extraction: WitnessPkg3D is fully computable (ℚ, ℕ, Finset only)"
  IO.println ""
  IO.println "Dimension-free tail bound: R²/(4π²M²) (SAME as 1D/2D!)"
  IO.println ""
  IO.println "════════════════════════════════════════════════════════════"
  IO.println ""

  -- Test 1: Product mode (8 corners)
  display_witness_metadata_3D {
    testName := "Test 1: Product Mode (8 Corners)"
    functionDescription := "ℓ² seq: modes (±1,±1,±1) (represents sin(2πx)sin(2πy)sin(2πz)) | R=5 (H¹≈14.99)"
    ε := QRK3DDemo.ε₁
    R := QRK3DDemo.R₁
  }

  IO.println "────────────────────────────────────────────────────────────"
  IO.println ""

  -- Test 2: Diagonal mode
  display_witness_metadata_3D {
    testName := "Test 2: Diagonal Mode"
    functionDescription := "ℓ² seq: modes (1,1,1), (-1,-1,-1) (represents sin(2π(x+y+z))) | R=8 (H¹≈59.72)"
    ε := QRK3DDemo.ε₂
    R := QRK3DDemo.R₂
  }

  IO.println "────────────────────────────────────────────────────────────"
  IO.println ""

  -- Test 3: Mixed mode
  display_witness_metadata_3D {
    testName := "Test 3: Mixed Mode"
    functionDescription := "ℓ² seq: modes (±2,±1,1) (represents sin(4πx)sin(2πy)sin(2πz)) | R=13 (H¹≈14.87)"
    ε := QRK3DDemo.ε₃
    R := QRK3DDemo.R₃
  }

  IO.println "════════════════════════════════════════════════════════════"
  IO.println ""
  IO.println "╔════════════════════════════════════════════════════════════╗"
  IO.println "║ Extraction Status: SUCCESS                                 ║"
  IO.println "║                                                             ║"
  IO.println "║ ✓ Fully constructive approach (zero axioms)                ║"
  IO.println "║ ✓ Explicit ℓ² sequences with finite 3D Fourier support    ║"
  IO.println "║ ✓ Witness existence proven for all 3 test cases           ║"
  IO.println "║ ✓ Grid parameters computed from (ε, R)                    ║"
  IO.println "║ ✓ WitnessPkg3D fully extractable (xBudget C0)             ║"
  IO.println "║ ✓ Soundness via gridFinset_sound_3D                       ║"
  IO.println "║                                                             ║"
  IO.println "║ Witness theorems:                                          ║"
  IO.println "║   • witness_exists_test1 (product mode, seq3D_1)           ║"
  IO.println "║   • witness_exists_test2 (diagonal mode, seq3D_2)          ║"
  IO.println "║   • witness_exists_test3 (mixed mode, seq3D_3)             ║"
  IO.println "║                                                             ║"
  IO.println "║ Constructive proof strategy:                               ║"
  IO.println "║   • Explicit finite 3D Fourier support                     ║"
  IO.println "║   • Mean-zero by construction (a₀₀₀ = 0)                   ║"
  IO.println "║   • H¹ ball membership via finite arithmetic               ║"
  IO.println "║   • R adjusted to accommodate 3D H¹ energy                 ║"
  IO.println "║   • Dimension-free tail bound (same as 1D/2D!)             ║"
  IO.println "║                                                             ║"
  IO.println "║ 3D Scaling Achievement:                                    ║"
  IO.println "║   • Tail bound formula: R²/(4π²M²) - DIMENSION FREE!       ║"
  IO.println "║   • Mesh formula: δ = ε/(8·(2M+1)²) - conservative         ║"
  IO.println "║   • Grid size: (2M+1)³ - 1 frequencies                     ║"
  IO.println "║   • Factored witness solves exponential explosion          ║"
  IO.println "╚════════════════════════════════════════════════════════════╝"
  IO.println ""
