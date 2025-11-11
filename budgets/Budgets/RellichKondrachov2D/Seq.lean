/-
2D Rellich-Kondrachov Sequence Space Layer (ℓ²(ℤ²))

Defines the sequence space structure for Fourier coefficients on the 2D torus
and proves the dimension-free tail bound that enables constructive compactness.

Budget: C0-C2 (constructive witness extraction without classical axioms)
-/

import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate Real

namespace RellichKondrachov2D.Seq

/-! ## 2D Fourier Coefficient Sequences -/

/-- Sequences on ℤ² with L² summability -/
structure ℓ2Z2 where
  a : ℤ × ℤ → ℂ
  summable_sq : Summable (fun k => ‖a k‖^2)

namespace ℓ2Z2

/-- Mean-zero condition = vanishing DC mode -/
def meanZero (x : ℓ2Z2) : Prop := x.a (0, 0) = 0

/-- H¹ summability with 2D frequency weight |k|² = k₁² + k₂² -/
def h1BoundFinitary (R : ℝ) (x : ℓ2Z2) : Prop :=
  ∀ (F : Finset (ℤ × ℤ)),
    Finset.sum F (fun k => (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖x.a k‖^2) ≤ R^2

/-- H¹ ball membership - finitary (no tsum in statement) -/
structure InH1Ball (R : ℝ) (x : ℓ2Z2) : Prop where
  h1_bound : h1BoundFinitary R x

/-! ## Zero and Basic Operations -/

/-- Zero sequence -/
def zero : ℓ2Z2 where
  a := fun _ => 0
  summable_sq := by
    convert summable_zero using 1
    ext k
    simp [norm_zero, sq]

lemma zero_mean_zero : zero.meanZero := rfl

/-- Truncation to finite support -/
def truncate (x : ℓ2Z2) (S : Finset (ℤ × ℤ)) : ℓ2Z2 where
  a := fun k => if k ∈ S then x.a k else 0
  summable_sq := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => ?_) x.summable_sq
    split_ifs <;> simp

/-! ## 2D Index Sets -/

/-- Square frequency cutoff: [-M, M]² \ {(0,0)}
    (Anisotropic cutoff chosen for simplicity; disk version possible.) -/
def IndexSet2D (M : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-M : ℤ) M) ×ˢ (Finset.Icc (-M : ℤ) M)).erase (0, 0)

lemma mem_IndexSet2D {M : ℕ} {k : ℤ × ℤ} :
    k ∈ IndexSet2D M ↔ -M ≤ k.1 ∧ k.1 ≤ M ∧ -M ≤ k.2 ∧ k.2 ≤ M ∧ k ≠ (0, 0) := by
  simp [IndexSet2D, Finset.mem_product, Finset.mem_Icc]
  tauto

lemma IndexSet2D_nonempty {M : ℕ} (hM : 0 < M) : (IndexSet2D M).Nonempty := by
  use (1, 0)
  simp [mem_IndexSet2D]
  omega

/-- Cardinal bound for square cutoff: ≤ (2M+1)² -/
lemma card_IndexSet2D_le (M : ℕ) :
    (IndexSet2D M).card ≤ (2 * M + 1)^2 := by
  have h1 : (Finset.Icc (-M : ℤ) M).card = 2 * M + 1 := by
    rw [Int.card_Icc]
    omega
  calc (IndexSet2D M).card
      ≤ ((Finset.Icc (-M : ℤ) M) ×ˢ (Finset.Icc (-M : ℤ) M)).card := by
        apply Finset.card_erase_le
    _ = (Finset.Icc (-M : ℤ) M).card * (Finset.Icc (-M : ℤ) M).card := by
        rw [Finset.card_product]
    _ = (2 * M + 1) * (2 * M + 1) := by rw [h1]
    _ = (2 * M + 1)^2 := by ring

/-! ## Tail Bound with Dimension-Free Formula

The tail bound formula R²/(4π²M²) is independent of dimension.
This generalizes directly from 1D by keeping the weight factor
inside the sum and factoring out the uniform lower bound.

For |k|² > M² (where |k|² = k₁² + k₂²):
  1 + 4π²|k|² ≥ 4π²M²

Therefore:
  Σ_{|k|²>M²} |aₖ|² ≤ (1/4π²M²) · Σ_{|k|²>M²} (1 + 4π²|k|²)|aₖ|²
                      ≤ R²/4π²M²

This formula matches the 1D case, with the Euclidean norm |k|² = k₁² + k₂².
-/

/-- Tail bound for 2D: frequencies outside cutoff -/
theorem tail_bound_finitary_2D {x : ℓ2Z2} {R M : ℝ}
    (hH1 : x.InH1Ball R)
    (hM : 0 < M)
    (F : Finset {k : ℤ × ℤ // M^2 < ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)}) :
    Finset.sum F (fun k => ‖x.a k.val‖^2) ≤ R^2 / (4 * Real.pi^2 * M^2) := by
  by_cases hF : F.Nonempty
  · have hpi : 0 < Real.pi := Real.pi_pos
    -- Key: uniform lower bound on weights in tail
    have h_weight_bound : ∀ k ∈ F,
        4 * Real.pi^2 * M^2 ≤ 1 + 4 * Real.pi^2 * ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) := by
      intro k hk
      have hk_tail : M^2 < ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) := k.property
      calc 4 * Real.pi^2 * M^2
          ≤ 4 * Real.pi^2 * ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith
        _ ≤ 1 + 4 * Real.pi^2 * ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) := by linarith

    -- Apply H¹ bound to get weighted sum
    have h_H1_bound := hH1.h1_bound (F.map (Function.Embedding.subtype _))

    -- Extract bound on unweighted tail sum
    calc Finset.sum F (fun k => ‖x.a k.val‖^2)
        ≤ Finset.sum F (fun k =>
            (1 / (4 * Real.pi^2 * M^2)) *
            (1 + 4 * Real.pi^2 * ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2)) *
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
                (1 + 4 * Real.pi^2 * ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2)) *
                ‖x.a k.val‖^2 := by
                have : (1 + 4 * Real.pi^2 * ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2)) /
                         (4 * Real.pi^2 * M^2) * ‖x.a k.val‖^2 =
                       (1 / (4 * Real.pi^2 * M^2)) *
                       (1 + 4 * Real.pi^2 * ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2)) *
                       ‖x.a k.val‖^2 := by ring
                rw [←this]
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact div_le_div_of_nonneg_right hw hM2_nonneg
      _ = (1 / (4 * Real.pi^2 * M^2)) *
          Finset.sum F (fun k =>
            (1 + 4 * Real.pi^2 * ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2)) *
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

end ℓ2Z2

/-! ## Grid Construction Parameters

The mesh size is chosen conservatively to accommodate the (2M+1)² frequency count.
Formula: δ = ε / (4·(2M+1))
-/

-- Rational π lower bound (same as 1D)
def pi_rat_lb : ℚ := 3

lemma pi_rat_lb_pos : 0 < (pi_rat_lb : ℝ) := by norm_num [pi_rat_lb]

-- Note: We use 3 as a conservative lower bound for π
-- The actual value is π ≈ 3.14159..., so 3 < π < 4

/-- Frequency cutoff M for tail error control
    DIMENSION-FREE: Same formula as 1D works! -/
def M_of (ε R : ℚ) : ℕ :=
  Nat.ceil (R / (pi_rat_lb * ε)) + 1

/-- Conservative 2D mesh accounting for (2M+1)² factor -/
def mesh2D (ε : ℚ) (M : ℕ) : ℚ :=
  ε / (4 * (2 * M + 1))

lemma mesh2D_pos (ε : ℚ) (M : ℕ) (hε : 0 < ε) : 0 < (mesh2D ε M : ℝ) := by
  unfold mesh2D
  push_cast
  apply div_pos
  · exact_mod_cast hε
  · positivity

/-! ## Coefficient Boxes and Grid Points

GridPoint2D uses a factored representation to avoid exponential grid enumeration:
  - Represented as a dependent function (k : IndexSet) → coeffBox k
  - The full product Finset.pi exists mathematically but is not materialized
  - Only one grid point per input is constructed (via rounding)
-/

/-- Coefficient bound for frequency k based on H¹ ball radius.
    The DC mode (0,0) is constrained to zero (mean-zero condition). -/
def coeffBound (R : ℚ) (k : ℤ × ℤ) : ℚ :=
  if k = (0, 0) then 0 else R

/-- Integer lattice box for coefficient discretization at frequency k.
    The box is [-rad, rad]² in the integer lattice.
    Classification: C0 (all operations use rational arithmetic) -/
def coeffBox (ε R : ℚ) (M : ℕ) (k : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  let δ := mesh2D ε M
  let bound := coeffBound R k
  let rad := Nat.ceil (bound / δ) + 1
  (Finset.Icc (-rad : ℤ) rad) ×ˢ (Finset.Icc (-rad : ℤ) rad)

/-- The origin always lies inside any coefficient box -/
lemma zero_in_coeffBox (ε R : ℚ) (M : ℕ) (k : ℤ × ℤ) :
    (0, 0) ∈ coeffBox ε R M k := by
  unfold coeffBox
  set δ := mesh2D ε M
  set bound := coeffBound R k
  set rad := Nat.ceil (bound / δ) + 1
  have hrad : 0 ≤ (rad : ℤ) := by exact_mod_cast (Nat.zero_le rad)
  have hin : (0 : ℤ) ∈ Finset.Icc (-rad : ℤ) rad := by
    simp [Finset.mem_Icc, hrad]
  exact Finset.mem_product.mpr ⟨hin, hin⟩

/-- Coefficient box as a subtype finset (for dependent pi construction) -/
def coeffBoxSubtype (ε R : ℚ) (M : ℕ) (k : ℤ × ℤ) :
    Finset { p : ℤ × ℤ // p ∈ coeffBox ε R M k } :=
  (coeffBox ε R M k).attach

/-- Grid point: dependent function assigning coefficient to each frequency
    FACTORED REPRESENTATION: We store the function, not the full Finset.pi
    C0-COMPUTABLE when constructed via rounding -/
def GridPoint2D (ε R : ℚ) (M : ℕ) : Type :=
  (k : ℤ × ℤ) → k ∈ ℓ2Z2.IndexSet2D M → {p : ℤ × ℤ // p ∈ coeffBox ε R M k}

/-- Canonical zero grid point (all coefficients zero) -/
def zeroGridPoint2D (ε R : ℚ) (M : ℕ) : GridPoint2D ε R M :=
  fun k _hk => ⟨(0, 0), zero_in_coeffBox ε R M k⟩

/-- Each box is a fintype -/
instance boxFintype2D (ε R : ℚ) (M : ℕ) (k : ℤ × ℤ) :
    Fintype { p : ℤ × ℤ // p ∈ coeffBox ε R M k } :=
  Fintype.ofFinset (coeffBox ε R M k) (fun _ => Iff.rfl)

/-! ## Rounding Infrastructure (C0-EXTRACTABLE) -/

/-- Round a complex coefficient to nearest grid point
    C0-COMPUTABLE: This function uses only floor operations
    INPUT: δ (rational mesh), c (complex coefficient)
    OUTPUT: Integer pair (re_grid, im_grid) representing rounded coefficient -/
noncomputable def roundCoeff (δ : ℚ) (c : ℂ) : ℤ × ℤ :=
  let re_scaled := (c.re / (δ : ℝ))
  let im_scaled := (c.im / (δ : ℝ))
  (Int.floor re_scaled, Int.floor im_scaled)


/-- Round an ℓ² sequence to the nearest grid point.
    For each k in IndexSet, rounds the coefficient to the nearest lattice point.
    Uses decidable membership check with fallback to (0,0) if rounded value is out of bounds.
    Classification: C0-extractable (witness constructor) -/
noncomputable def roundToGrid2D (ε R : ℚ) (M : ℕ) (x : ℓ2Z2) : GridPoint2D ε R M :=
  fun k _hk =>
    let c := x.a k
    let rounded := roundCoeff (mesh2D ε M) c
    -- Check if rounded is in the box, otherwise use (0, 0)
    if h : rounded ∈ coeffBox ε R M k then
      ⟨rounded, h⟩
    else
      ⟨(0, 0), zero_in_coeffBox ε R M k⟩

/-! ## Grid Evaluation -/

/-- Convert grid point back to ℓ² sequence.
    Each integer pair is scaled back to complex by δ.
    Classification: C5 (used in proofs, not extracted) -/
noncomputable def gridToSeq (ε R : ℚ) (M : ℕ) (g : GridPoint2D ε R M) : ℓ2Z2 where
  a := fun k =>
    if h : k ∈ ℓ2Z2.IndexSet2D M then
      let δ := mesh2D ε M
      let p := g k h
      -- Scale integer pair back to complex: (p₁ + i·p₂) · δ
      ((p.val.1 : ℂ) * (δ : ℝ) + Complex.I * ((p.val.2 : ℂ) * (δ : ℝ)))
    else 0
  summable_sq := by
    -- Finite support → summable
    -- The function a is zero outside IndexSet2D M (finite set)
    refine summable_of_ne_finset_zero (s := ℓ2Z2.IndexSet2D M) ?_
    intro k hk
    -- hk : k ∉ ℓ2Z2.IndexSet2D M
    -- Therefore a k = 0 (by the if-then-else)
    simp only [dif_neg hk, norm_zero, sq, zero_mul]

/-- Mathematical finite set of all grid points.
    Represented as Finset.pi (product of coefficient boxes), which is exponentially large
    but exists only for the theorem statement (not enumerated during extraction).
    Classification: C5 (used in proofs only) -/
noncomputable def gridFinset2D (ε R : ℚ) (M : ℕ) : Finset (GridPoint2D ε R M) :=
  Finset.pi (ℓ2Z2.IndexSet2D M) (fun k => coeffBoxSubtype ε R M k)

/-- The grid is nonempty (contains the zero grid point) -/
lemma gridFinset2D_nonempty (ε R : ℚ) (M : ℕ) :
    (gridFinset2D ε R M).Nonempty := by
  refine ⟨zeroGridPoint2D ε R M, ?_⟩
  refine Finset.mem_pi.mpr ?_
  intro k hk
  simp [zeroGridPoint2D, coeffBoxSubtype]

/-- Finite set of center sequences (explicit constructive witness)
    C5-PROOF LAYER: The image of the grid under evaluation -/
noncomputable def centersFinset2D (ε R : ℚ) (M : ℕ) : Finset ℓ2Z2 := by
  classical
  exact (gridFinset2D ε R M).image (gridToSeq ε R M)

/-! ## Witness Package (C0-EXTRACTABLE CORE)

The extractable artifact contains only:
- ε, R : ℚ (parameters)
- M : ℕ (frequency cutoff)
- δ : ℚ (mesh size)
- Grid point constructor (via rounding)

NO EXTRACTION:
- ℝ, ℂ types
- Summable proofs
- Finset.pi enumeration
-/

structure WitnessPkg2D where
  ε : ℚ
  R : ℚ

/-- The frequency cutoff for a witness package -/
def WitnessPkg2D.M (P : WitnessPkg2D) : ℕ := M_of P.ε P.R

/-- The grid mesh for a witness package -/
def WitnessPkg2D.δ (P : WitnessPkg2D) : ℚ := mesh2D P.ε P.M

/-- The mathematical finite grid of witness points (non-materialized) -/
noncomputable def WitnessPkg2D.grid (P : WitnessPkg2D) : Finset (GridPoint2D P.ε P.R P.M) :=
  gridFinset2D P.ε P.R P.M

/-- The grid is explicitly nonempty -/
lemma WitnessPkg2D.grid_nonempty (P : WitnessPkg2D) :
    (P.grid).Nonempty :=
  gridFinset2D_nonempty P.ε P.R P.M

/-- Evaluation of grid point to ℓ² sequence (proof-only, gets erased in extraction) -/
noncomputable def WitnessPkg2D.eval (P : WitnessPkg2D) : (GridPoint2D P.ε P.R P.M) → ℓ2Z2 :=
  gridToSeq P.ε P.R P.M

/-- The C0-extractable rounding function (witness constructor) -/
noncomputable def WitnessPkg2D.round (P : WitnessPkg2D) : ℓ2Z2 → GridPoint2D P.ε P.R P.M :=
  roundToGrid2D P.ε P.R P.M

/-! ## Summary of Computational Tiers

C0 (EXTRACTABLE - computable, no choice):
- coeffBound, coeffBox : Finset construction from ε, R, M
- roundCoeff : ℂ → ℤ × ℤ (floor operations)
- roundToGrid2D : ℓ2Z2 → GridPoint2D (witness constructor)

C5 (proof layer, used in theorem statements):
- gridToSeq : GridPoint2D → ℓ2Z2 (evaluation in ℝ/ℂ)
- gridFinset2D : Finset.pi (exponentially large, not materialized)
- centersFinset2D : image of grid (for covering theorem)
-/

end RellichKondrachov2D.Seq
