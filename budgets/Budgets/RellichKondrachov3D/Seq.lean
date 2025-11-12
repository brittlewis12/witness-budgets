import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate Real

/-!
# Rellich-Kondrachov 3D: Sequence Space Layer

This file implements the constructive witness extraction for 3D Rellich-Kondrachov compactness
via ℓ²(ℤ³) sequence space. This is the foundation for extractable C0-C2 witness data.

## Main definitions

* `Seq3D` - Square-summable sequences on ℤ³ (3D Fourier coefficients)
* `IndexSet3D M` - Frequency cube [-M,M]³ \ {(0,0,0)}
* `mesh3D ε M` - Coefficient discretization step (ε / (8 × (2M+1)²))
* `GridPoint3D ε R M` - Factored witness type (function, not enumeration)
* `roundToGrid3D` - C0 witness constructor
* `WitnessPkg3D` - Extractable metadata package

## Main results

* `tail_bound_finitary_3D` - Dimension-free tail bound R²/(4π²M²)
* `gridFinset_sound_3D` - Main soundness theorem (in RellichKondrachov3D.lean)

## Architecture

This file stays in ℓ² space (no measure theory). The sequence space approach enables:
- Constructive witness extraction (C0-C2 xBudget)
- Dimension-free tail bounds
- Factored representation (solves grid explosion)
- Zero axioms in extraction layer

## Implementation notes

- Uses nested pairs ℤ × (ℤ × ℤ) for ℤ³ (Mathlib convention)
- Projections: k.1 (x), k.2.1 (y), k.2.2 (z)
- Conservative mesh formula enables simple rational arithmetic
- Factored GridPoint3D as function type (not materialized Finset)

-/

set_option linter.unusedTactic false

namespace ℓ2Z3

/-! ## Type definitions -/

/-- Square-summable sequences on ℤ³ (3D Fourier coefficient space) -/
structure Seq3D where
  /-- Coefficient function: ℤ³ → ℂ -/
  a : ℤ × ℤ × ℤ → ℂ
  /-- Square-summability condition -/
  summable_sq : Summable (fun k => ‖a k‖^2)

/-! ## Basic properties -/

/-- Mean-zero property: a₍₀,₀,₀₎ = 0 -/
def meanZero (x : Seq3D) : Prop :=
  x.a (0, 0, 0) = 0

/-- H¹ weight function for ℤ³: 1 + 4π²(k₁² + k₂² + k₃²) -/
noncomputable def h1Weight (k : ℤ × ℤ × ℤ) : ℝ :=
  1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2)

/-- H¹-ball membership (finitary version for extraction) -/
def InH1Ball (R : ℝ) (x : Seq3D) : Prop :=
  ∀ (F : Finset (ℤ × ℤ × ℤ)),
    Finset.sum F (fun k => (h1Weight k) * ‖x.a k‖^2) ≤ R^2

/-! ## Frequency indexing -/

/-- Frequency cube: [-M,M]³ \ {(0,0,0)} -/
def IndexSet3D (M : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc (-M : ℤ) M) ×ˢ ((Finset.Icc (-M : ℤ) M) ×ˢ (Finset.Icc (-M : ℤ) M))).erase (0, (0, 0))

lemma card_IndexSet3D_le (M : ℕ) :
    (IndexSet3D M).card ≤ (2 * M + 1)^3 := by
  have h1 : (Finset.Icc (-M : ℤ) M).card = 2 * M + 1 := by
    rw [Int.card_Icc]
    omega
  calc (IndexSet3D M).card
      ≤ ((Finset.Icc (-M : ℤ) M) ×ˢ ((Finset.Icc (-M : ℤ) M) ×ˢ (Finset.Icc (-M : ℤ) M))).card := by
        apply Finset.card_erase_le
    _ = (Finset.Icc (-M : ℤ) M).card * ((Finset.Icc (-M : ℤ) M) ×ˢ (Finset.Icc (-M : ℤ) M)).card := by
        rw [Finset.card_product]
    _ = (Finset.Icc (-M : ℤ) M).card * ((Finset.Icc (-M : ℤ) M).card * (Finset.Icc (-M : ℤ) M).card) := by
        rw [Finset.card_product]
    _ = (2 * M + 1) * ((2 * M + 1) * (2 * M + 1)) := by rw [h1]
    _ = (2 * M + 1)^3 := by ring

lemma mem_IndexSet3D {M : ℕ} {k : ℤ × ℤ × ℤ} :
    k ∈ IndexSet3D M ↔
      -M ≤ k.1 ∧ k.1 ≤ M ∧
      -M ≤ k.2.1 ∧ k.2.1 ≤ M ∧
      -M ≤ k.2.2 ∧ k.2.2 ≤ M ∧
      k ≠ (0, (0, 0)) := by
  simp only [IndexSet3D, Finset.mem_erase, Finset.mem_product, Finset.mem_Icc]
  constructor
  · intro ⟨h_ne, h1, h2, h3⟩
    exact ⟨h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h_ne⟩
  · intro ⟨h1a, h1b, h2a, h2b, h3a, h3b, h_ne⟩
    exact ⟨h_ne, ⟨h1a, h1b⟩, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩⟩

/-! ## Grid parameter formulas -/

/-- Frequency cutoff M from (ε, R): same as 1D/2D (dimension-free!) -/
noncomputable def M_of (ε R : ℚ) : ℕ :=
  Nat.ceil (R / (Real.pi * ε)) + 1

/-- 3D mesh formula: ε / (8 × (2M+1)²)
    Conservative bound ensuring (2M+1)³ × 2δ² ≤ (ε/2)² -/
def mesh3D (ε : ℚ) (M : ℕ) : ℚ :=
  ε / (8 * (2 * M + 1)^2)

lemma mesh3D_pos (ε : ℚ) (M : ℕ) (hε : 0 < ε) :
    0 < (mesh3D ε M : ℝ) := by
  unfold mesh3D
  push_cast
  apply div_pos
  · exact_mod_cast hε
  · positivity

/-! ## Coefficient discretization -/

/-- Round complex number to δ-grid (floor-based for computability) -/
noncomputable def roundCoeff (δ : ℚ) (z : ℂ) : ℤ × ℤ :=
  (⌊z.re / (δ : ℝ)⌋, ⌊z.im / (δ : ℝ)⌋)

/-- Coefficient bound for frequency k based on H¹ ball radius.
    The origin (0,0,0) is constrained to zero (mean-zero condition). -/
def coeffBound (R : ℚ) (k : ℤ × ℤ × ℤ) : ℚ :=
  if k = (0, (0, 0)) then 0 else R

/-- Coefficient box for frequency k: [-rad, rad]² in integer lattice -/
def coeffBox (ε R : ℚ) (M : ℕ) (k : ℤ × ℤ × ℤ) : Finset (ℤ × ℤ) :=
  let δ := mesh3D ε M
  let bound := coeffBound R k
  let rad := Nat.ceil (bound / δ) + 1
  (Finset.Icc (-rad : ℤ) rad) ×ˢ (Finset.Icc (-rad : ℤ) rad)

/-- The origin always lies inside any coefficient box -/
lemma zero_in_coeffBox (ε R : ℚ) (M : ℕ) (k : ℤ × ℤ × ℤ) :
    (0, 0) ∈ coeffBox ε R M k := by
  unfold coeffBox
  set δ := mesh3D ε M
  set bound := coeffBound R k
  set rad := Nat.ceil (bound / δ) + 1
  have hrad : 0 ≤ (rad : ℤ) := by exact_mod_cast (Nat.zero_le rad)
  have hin : (0 : ℤ) ∈ Finset.Icc (-rad : ℤ) rad := by
    simp [Finset.mem_Icc, hrad]
  exact Finset.mem_product.mpr ⟨hin, hin⟩

/-- Coefficient box as a subtype finset (for dependent pi construction) -/
def coeffBoxSubtype (ε R : ℚ) (M : ℕ) (k : ℤ × ℤ × ℤ) :
    Finset {p : ℤ × ℤ // p ∈ coeffBox ε R M k} :=
  (coeffBox ε R M k).attach

/-! ## Factored witness structure -/

/-- Witness type: function from IndexSet3D to coefficient boxes (factored!) -/
def GridPoint3D (ε R : ℚ) (M : ℕ) : Type :=
  (k : ℤ × ℤ × ℤ) → k ∈ IndexSet3D M → {p : ℤ × ℤ // p ∈ coeffBox ε R M k}

/-- Canonical zero grid point (all coefficients zero) -/
def zeroGridPoint3D (ε R : ℚ) (M : ℕ) : GridPoint3D ε R M :=
  fun k _hk => ⟨(0, 0), zero_in_coeffBox ε R M k⟩

/-- Each coefficient box is finite, yielding a fintype structure. -/
instance boxFintype3D (ε R : ℚ) (M : ℕ) (k : ℤ × ℤ × ℤ) :
    Fintype {p : ℤ × ℤ // p ∈ coeffBox ε R M k} :=
  Fintype.ofFinset (coeffBox ε R M k) (fun _ => Iff.rfl)

/-- C0 witness constructor: round each coefficient independently -/
noncomputable def roundToGrid3D (ε R : ℚ) (M : ℕ) (x : Seq3D) : GridPoint3D ε R M :=
  fun k _hk =>
    let rounded := roundCoeff (mesh3D ε M) (x.a k)
    if h : rounded ∈ coeffBox ε R M k then ⟨rounded, h⟩
    else ⟨(0, 0), zero_in_coeffBox ε R M k⟩

/-- Convert GridPoint3D back to Seq3D for soundness statement -/
noncomputable def gridToSeq (ε R : ℚ) (M : ℕ) (g : GridPoint3D ε R M) : Seq3D where
  a := fun k =>
    if h : k ∈ IndexSet3D M then
      let δ := mesh3D ε M
      let p := g k h
      -- Scale integer pair back to complex: (p₁ + i·p₂) · δ
      ((p.val.1 : ℂ) * (δ : ℝ) + Complex.I * ((p.val.2 : ℂ) * (δ : ℝ)))
    else 0
  summable_sq := by
    -- Finite support → summable
    refine summable_of_ne_finset_zero (s := IndexSet3D M) ?_
    intro k hk
    simp only [dif_neg hk, norm_zero, sq, zero_mul]

/-- Proof-layer finite grid: gigantic Finset.pi over coefficient boxes.
    This is never enumerated during extraction (C5 only). -/
noncomputable def gridFinset3D (ε R : ℚ) (M : ℕ) :
    Finset (GridPoint3D ε R M) :=
  Finset.pi (IndexSet3D M) (fun k => coeffBoxSubtype ε R M k)

/-- The grid contains the zero grid point. -/
lemma gridFinset3D_nonempty (ε R : ℚ) (M : ℕ) :
    (gridFinset3D ε R M).Nonempty := by
  refine ⟨zeroGridPoint3D ε R M, ?_⟩
  refine Finset.mem_pi.mpr ?_
  intro k hk
  simp [zeroGridPoint3D, coeffBoxSubtype]

/-- Finite set of center sequences (used only in the proof layer). -/
noncomputable def centersFinset3D (ε R : ℚ) (M : ℕ) : Finset Seq3D := by
  classical
  exact (gridFinset3D ε R M).image (gridToSeq ε R M)

/-! ## Extractable metadata package -/

/-- Witness package: input parameters (fully extractable) -/
structure WitnessPkg3D where
  /-- Approximation accuracy -/
  ε : ℚ
  /-- H¹ ball radius -/
  R : ℚ

/-- Derive M from package -/
noncomputable def WitnessPkg3D.M (pkg : WitnessPkg3D) : ℕ :=
  M_of pkg.ε pkg.R

/-- Derive δ from package -/
noncomputable def WitnessPkg3D.δ (pkg : WitnessPkg3D) : ℚ :=
  mesh3D pkg.ε pkg.M

/-- Mathematical (proof-layer) Finset of grid points (not materialized in extraction). -/
noncomputable def WitnessPkg3D.grid (pkg : WitnessPkg3D) :
    Finset (GridPoint3D pkg.ε pkg.R pkg.M) :=
  gridFinset3D pkg.ε pkg.R pkg.M

/-- The witness grid is nonempty (contains the zero grid point). -/
lemma WitnessPkg3D.grid_nonempty (pkg : WitnessPkg3D) :
    (pkg.grid).Nonempty :=
  gridFinset3D_nonempty pkg.ε pkg.R pkg.M

/-- Proof-layer evaluation map from grid points to sequences. -/
noncomputable def WitnessPkg3D.eval (pkg : WitnessPkg3D) :
    (GridPoint3D pkg.ε pkg.R pkg.M) → Seq3D :=
  gridToSeq pkg.ε pkg.R pkg.M

/-- C0-extractable rounding function (constructive witness constructor). -/
noncomputable def WitnessPkg3D.round (pkg : WitnessPkg3D) :
    Seq3D → GridPoint3D pkg.ε pkg.R pkg.M :=
  roundToGrid3D pkg.ε pkg.R pkg.M

/-! ## Main theorems -/

/-- Dimension-free tail bound (identical to 1D/2D!) -/
theorem tail_bound_finitary_3D {x : Seq3D} {R M : ℝ}
    (hH1 : InH1Ball R x)
    (hM : 0 < M)
    (F : Finset {k : ℤ × ℤ × ℤ // M^2 < ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2)}) :
    Finset.sum F (fun k => ‖x.a k.val‖^2) ≤ R^2 / (4 * Real.pi^2 * M^2) := by
  by_cases hF : F.Nonempty
  · have hpi : 0 < Real.pi := Real.pi_pos
    -- Key: uniform lower bound on weights in tail
    have h_weight_bound : ∀ k ∈ F,
        4 * Real.pi^2 * M^2 ≤ 1 + 4 * Real.pi^2 * ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) := by
      intro k hk
      have hk_tail : M^2 < ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) := k.property
      calc 4 * Real.pi^2 * M^2
          ≤ 4 * Real.pi^2 * ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith
        _ ≤ 1 + 4 * Real.pi^2 * ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) := by linarith

    -- Apply H¹ bound to get weighted sum
    unfold InH1Ball at hH1
    have h_H1_bound := hH1 (F.map (Function.Embedding.subtype _))

    -- Extract bound on unweighted tail sum
    calc Finset.sum F (fun k => ‖x.a k.val‖^2)
        ≤ Finset.sum F (fun k =>
            (1 / (4 * Real.pi^2 * M^2)) *
            (1 + 4 * Real.pi^2 * ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2)) *
            ‖x.a k.val‖^2) := by
          apply Finset.sum_le_sum
          intro k hk
          have hw := h_weight_bound k hk
          have hM2_pos : 0 < 4 * Real.pi^2 * M^2 := by positivity
          have hM2_nonneg : 0 ≤ 4 * Real.pi^2 * M^2 := by positivity
          calc ‖x.a k.val‖^2
              = (4 * Real.pi^2 * M^2 / (4 * Real.pi^2 * M^2)) * ‖x.a k.val‖^2 := by
                rw [div_self]; linarith; positivity
            _ ≤ (1 / (4 * Real.pi^2 * M^2)) *
                (1 + 4 * Real.pi^2 * ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2)) *
                ‖x.a k.val‖^2 := by
                have : (1 + 4 * Real.pi^2 * ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2)) /
                         (4 * Real.pi^2 * M^2) * ‖x.a k.val‖^2 =
                       (1 / (4 * Real.pi^2 * M^2)) *
                       (1 + 4 * Real.pi^2 * ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2)) *
                       ‖x.a k.val‖^2 := by ring
                rw [←this]
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact div_le_div_of_nonneg_right hw hM2_nonneg
      _ = (1 / (4 * Real.pi^2 * M^2)) *
          Finset.sum F (fun k =>
            (1 + 4 * Real.pi^2 * ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2)) *
            ‖x.a k.val‖^2) := by
          rw [Finset.mul_sum]
          congr 1
          ext k
          ring
      _ ≤ (1 / (4 * Real.pi^2 * M^2)) * R^2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          convert h_H1_bound using 1
          rw [Finset.sum_map]
          rfl
      _ = R^2 / (4 * Real.pi^2 * M^2) := by ring
  · simp [Finset.not_nonempty_iff_eq_empty.mp hF]
    positivity

/-- Rounding error bound for mesh3D
    Verifies: (2M+1)³ × 2δ² ≤ (ε/2)²
    Conservative formula: δ = ε/(8(2M+1)²) ensures the bound holds -/
lemma rounding_bound_mesh_3D (ε : ℚ) (M : ℕ) (_hM : M ≠ 0) :
    ((2 * M + 1)^3 : ℝ) * (2 * ((mesh3D ε M : ℝ))^2) ≤ ((ε : ℝ) / 2)^2 := by
  unfold mesh3D
  push_cast
  have hM_pos : 0 < (2 * M + 1 : ℝ) := by norm_cast; omega
  have hM_ne : (2 * M + 1 : ℝ) ≠ 0 := ne_of_gt hM_pos

  -- Simplify LHS: (2M+1)³ × 2 × (ε/(8(2M+1)²))²
  have lhs_eq : (2 * M + 1 : ℝ)^3 * (2 * ((ε : ℝ) / (8 * (2 * M + 1 : ℝ)^2))^2) =
                (ε : ℝ)^2 / (32 * (2 * M + 1 : ℝ)) := by
    field_simp
    ring

  rw [lhs_eq]

  -- Show (ε²)/(32(2M+1)) ≤ (ε/2)²
  calc (ε : ℝ)^2 / (32 * (2 * M + 1 : ℝ))
      ≤ (ε : ℝ)^2 / 32 := by
        apply div_le_div_of_nonneg_left (sq_nonneg _)
        · norm_num
        · have : 1 ≤ (2 * M + 1 : ℝ) := by linarith
          calc 32 = 32 * 1 := by ring
              _ ≤ 32 * (2 * M + 1 : ℝ) := by
                apply mul_le_mul_of_nonneg_left this (by norm_num)
    _ ≤ (ε : ℝ)^2 / 4 := by
        have : (4 : ℝ) ≤ 32 := by norm_num
        apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) this
    _ = ((ε : ℝ) / 2)^2 := by
        have : ((ε : ℝ) / 2)^2 = (ε : ℝ)^2 / 4 := by field_simp; ring
        rw [←this]

end ℓ2Z3
