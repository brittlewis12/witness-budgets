import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate Real

/-
! Rellich–Kondrachov in arbitrary dimension: core layer

This file assembles the ℓ²-side infrastructure for the constructive
Rellich–Kondrachov theorem in an arbitrary dimension `d`.

## Main definitions
* `Lattice d` : the lattice `Fin d → ℤ`.
* `cube`, `IndexSetD` : the cubic truncations used for witnesses.
* `SeqD`, `InH1Ball` : the sequence model of mean-zero H¹ functions.
* `meshD` : the dimension-dependent mesh size.
* `GridPointD`, `roundToGridD`, `WitnessPkgD` : the factored witness data.

These notions are the shared substrate for the remaining files:
`TailBound` supplies the spectral estimate, `Rounding` controls
discretisation, `Soundness` combines the bounds, and `L2Bridge`
connects to the analytical setting.
-/

namespace ℓ2ZD

/-! ## Type definitions -/

/-- Integer lattice in dimension d: ℤᵈ -/
abbrev Lattice (d : ℕ) := Fin d → ℤ

variable {d : ℕ} [NeZero d]

/-- Frequency cube [-M,M]ᵈ -/
def cube (d M : ℕ) : Finset (Lattice d) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(M : ℤ)) (M : ℤ))

/-- Frequency cube with origin removed: [-M,M]ᵈ \ {0} -/
def IndexSetD (d M : ℕ) : Finset (Lattice d) :=
  (cube d M).erase (fun _ => (0 : ℤ))

/-- Squared norm on the lattice: ∑ᵢ kᵢ² -/
def normSq {d : ℕ} (k : Lattice d) : ℝ :=
  ∑ i, ((k i : ℝ)^2)

/-- H¹ weight function: 1 + 4π² ∑ᵢ kᵢ² -/
noncomputable def h1Weight {d : ℕ} (k : Lattice d) : ℝ :=
  1 + 4 * Real.pi^2 * normSq k

/-! ## Sequence space -/

/-- Square-summable sequences on ℤᵈ (d-dimensional Fourier coefficient space) -/
structure SeqD (d : ℕ) where
  /-- Coefficient function: ℤᵈ → ℂ -/
  a : Lattice d → ℂ
  /-- Square-summability condition -/
  summable_sq : Summable (fun k => ‖a k‖^2)

/-- Mean-zero property: a₀ = 0 -/
def meanZero {d : ℕ} (x : SeqD d) : Prop :=
  x.a (fun _ => 0) = 0

/-- H¹-ball membership (finitary version for extraction) -/
def InH1Ball {d : ℕ} (R : ℝ) (x : SeqD d) : Prop :=
  ∀ (F : Finset (Lattice d)),
    Finset.sum F (fun k => (h1Weight k) * ‖x.a k‖^2) ≤ R^2

/-! ## Basic lemmas for cube and index set -/

/-- Membership in cube -/
lemma mem_cube {d M : ℕ} {k : Lattice d} :
    k ∈ cube d M ↔ ∀ i, -(M : ℤ) ≤ k i ∧ k i ≤ (M : ℤ) := by
  unfold cube
  simp only [Fintype.mem_piFinset, Finset.mem_Icc]

/-- Cardinality of cube: (2M+1)ᵈ -/
lemma card_cube {d M : ℕ} :
    (cube d M).card = (2 * M + 1)^d := by
  unfold cube
  rw [Fintype.card_piFinset]
  have h_card : ∀ i : Fin d, (Finset.Icc (-(M : ℤ)) (M : ℤ)).card = 2 * M + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  trans (∏ _i : Fin d, (2 * M + 1))
  · congr 1
    ext i
    exact h_card i
  · simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Cardinality of index set: (2M+1)ᵈ - 1 -/
lemma card_IndexSetD {d M : ℕ} :
    (IndexSetD d M).card = (2 * M + 1)^d - 1 := by
  unfold IndexSetD
  rw [Finset.card_erase_of_mem]
  · rw [card_cube]
  · -- Prove (fun _ => 0) ∈ cube d M
    rw [mem_cube]
    intro i
    simp

/-- Upper bound on IndexSetD cardinality -/
lemma card_IndexSetD_le {d M : ℕ} :
    (IndexSetD d M).card ≤ (2 * M + 1)^d := by
  unfold IndexSetD
  calc ((cube d M).erase (fun _ => 0)).card
      ≤ (cube d M).card := Finset.card_erase_le
    _ = (2 * M + 1)^d := card_cube

/-- Membership in IndexSetD -/
lemma mem_IndexSetD {d M : ℕ} {k : Lattice d} :
    k ∈ IndexSetD d M ↔ k ∈ cube d M ∧ k ≠ (fun _ => 0) := by
  unfold IndexSetD
  rw [Finset.mem_erase]
  tauto

/-! ## Grid parameter formulas -/

/-- Frequency cutoff M from (ε, R): dimension-free formula -/
noncomputable def M_of (ε R : ℚ) : ℕ :=
  Nat.ceil (R / (Real.pi * ε)) + 1

/-- Dimension-generic mesh formula: ε / (4 * (2M+1)^⌈d/2⌉)

    This corrected formula ensures:
    (2M+1)ᵈ × 2δ² ≤ (ε/2)²

    The exponent ⌈d/2⌉ keeps algebra straightforward while maintaining soundness.
-/
def meshD (d : ℕ) (ε : ℚ) (M : ℕ) : ℚ :=
  ε / (4 * (2 * M + 1)^(Nat.ceil ((d : ℚ) / 2)))

/-- Mesh is positive -/
lemma meshD_pos (d : ℕ) (ε : ℚ) (M : ℕ) (hε : 0 < ε) :
    0 < (meshD d ε M : ℝ) := by
  unfold meshD
  push_cast
  apply div_pos
  · exact_mod_cast hε
  · positivity

/-! ## Coefficient discretization -/

/-- Round complex number to δ-grid (floor-based for computability) -/
noncomputable def roundCoeff (δ : ℚ) (z : ℂ) : ℤ × ℤ :=
  (⌊z.re / (δ : ℝ)⌋, ⌊z.im / (δ : ℝ)⌋)

/-- Coefficient bound for frequency k based on H¹ ball radius.
    The origin is constrained to zero (mean-zero condition). -/
def coeffBound {d : ℕ} (R : ℚ) (k : Lattice d) : ℚ :=
  if k = (fun _ => 0) then 0 else R

/-- Coefficient box for frequency k: [-rad, rad]² in integer lattice -/
def coeffBox {d : ℕ} (ε R : ℚ) (M : ℕ) (k : Lattice d) : Finset (ℤ × ℤ) :=
  let δ := meshD d ε M
  let bound := coeffBound R k
  let rad := Nat.ceil (bound / δ) + 1
  (Finset.Icc (-rad : ℤ) rad) ×ˢ (Finset.Icc (-rad : ℤ) rad)

/-- The origin always lies inside any coefficient box -/
lemma zero_in_coeffBox {d : ℕ} (ε R : ℚ) (M : ℕ) (k : Lattice d) :
    (0, 0) ∈ coeffBox ε R M k := by
  unfold coeffBox
  set δ := meshD d ε M
  set bound := coeffBound R k
  set rad := Nat.ceil (bound / δ) + 1
  have hrad : 0 ≤ (rad : ℤ) := by exact_mod_cast (Nat.zero_le rad)
  have hin : (0 : ℤ) ∈ Finset.Icc (-(rad : ℤ)) rad := by
    simp [Finset.mem_Icc, hrad]
  exact Finset.mem_product.mpr ⟨hin, hin⟩

/-- Coefficient box as a subtype finset (for dependent pi construction) -/
def coeffBoxSubtype {d : ℕ} (ε R : ℚ) (M : ℕ) (k : Lattice d) :
    Finset {p : ℤ × ℤ // p ∈ coeffBox ε R M k} :=
  (coeffBox ε R M k).attach

/-! ## Factored witness structure -/

/-- Witness type: function from IndexSetD to coefficient boxes (factored!)

    This is the key to avoiding exponential grid enumeration.
    A grid point is a dependent function assigning each frequency k
    a rounded coefficient in its coefficient box.
-/
def GridPointD (d : ℕ) (ε R : ℚ) (M : ℕ) : Type :=
  (k : Lattice d) → k ∈ IndexSetD d M → {p : ℤ × ℤ // p ∈ coeffBox ε R M k}

/-- Canonical zero grid point (all coefficients zero) -/
def zeroGridPointD {d : ℕ} (ε R : ℚ) (M : ℕ) : GridPointD d ε R M :=
  fun k _hk => ⟨(0, 0), zero_in_coeffBox ε R M k⟩

/-- Each coefficient box is finite, yielding a fintype structure. -/
instance boxFintypeD {d : ℕ} (ε R : ℚ) (M : ℕ) (k : Lattice d) :
    Fintype {p : ℤ × ℤ // p ∈ coeffBox ε R M k} :=
  Fintype.ofFinset (coeffBox ε R M k) (fun _ => Iff.rfl)

/-- C0 witness constructor: round each coefficient independently -/
noncomputable def roundToGridD {d : ℕ} (ε R : ℚ) (M : ℕ) (x : SeqD d) :
    GridPointD d ε R M :=
  fun k _hk =>
    let rounded := roundCoeff (meshD d ε M) (x.a k)
    if h : rounded ∈ coeffBox ε R M k then ⟨rounded, h⟩
    else ⟨(0, 0), zero_in_coeffBox ε R M k⟩

/-- Convert GridPointD back to SeqD for soundness statement -/
noncomputable def gridToSeqD {d : ℕ} (ε R : ℚ) (M : ℕ) (g : GridPointD d ε R M) :
    SeqD d where
  a := fun k =>
    if h : k ∈ IndexSetD d M then
      let δ := meshD d ε M
      let p := g k h
      -- Scale integer pair back to complex: (p₁ + i·p₂) · δ
      ((p.val.1 : ℂ) * (δ : ℝ) + Complex.I * ((p.val.2 : ℂ) * (δ : ℝ)))
    else 0
  summable_sq := by
    -- Finite support → summable
    refine summable_of_ne_finset_zero (s := IndexSetD d M) ?_
    intro k hk
    simp only [dif_neg hk, norm_zero, sq, zero_mul]

/-- Proof-layer finite grid: Finset.pi over coefficient boxes.
    This is never enumerated during extraction (C5 only). -/
noncomputable def gridFinsetD {d : ℕ} (ε R : ℚ) (M : ℕ) :
    Finset (GridPointD d ε R M) :=
  Finset.pi (IndexSetD d M) (fun k => coeffBoxSubtype ε R M k)

/-- The grid contains the zero grid point. -/
lemma gridFinsetD_nonempty {d : ℕ} (ε R : ℚ) (M : ℕ) :
    (gridFinsetD (d := d) ε R M).Nonempty := by
  refine ⟨zeroGridPointD ε R M, ?_⟩
  refine Finset.mem_pi.mpr ?_
  intro k hk
  simp [zeroGridPointD, coeffBoxSubtype]

/-- Finite set of center sequences (used only in the proof layer). -/
noncomputable def centersFinsetD {d : ℕ} (ε R : ℚ) (M : ℕ) : Finset (SeqD d) := by
  classical
  exact (gridFinsetD ε R M).image (gridToSeqD ε R M)

/-! ## Extractable metadata package -/

/-- Witness package: input parameters (fully extractable) -/
structure WitnessPkgD (d : ℕ) where
  /-- Dimension (must be ≥ 1) -/
  dim : ℕ
  /-- Approximation accuracy -/
  ε : ℚ
  /-- H¹ ball radius -/
  R : ℚ
  /-- Dimension consistency -/
  dim_eq : dim = d

/-- Derive M from package -/
noncomputable def WitnessPkgD.M {d : ℕ} (pkg : WitnessPkgD d) : ℕ :=
  M_of pkg.ε pkg.R

/-- Derive δ from package -/
noncomputable def WitnessPkgD.δ {d : ℕ} (pkg : WitnessPkgD d) : ℚ :=
  meshD d pkg.ε pkg.M

/-- Mathematical (proof-layer) Finset of grid points (not materialized in extraction). -/
noncomputable def WitnessPkgD.grid {d : ℕ} (pkg : WitnessPkgD d) :
    Finset (GridPointD d pkg.ε pkg.R pkg.M) :=
  gridFinsetD pkg.ε pkg.R pkg.M

/-- The witness grid is nonempty (contains the zero grid point). -/
lemma WitnessPkgD.grid_nonempty {d : ℕ} (pkg : WitnessPkgD d) :
    (pkg.grid).Nonempty :=
  gridFinsetD_nonempty pkg.ε pkg.R pkg.M

/-- Proof-layer evaluation map from grid points to sequences. -/
noncomputable def WitnessPkgD.eval {d : ℕ} (pkg : WitnessPkgD d) :
    (GridPointD d pkg.ε pkg.R pkg.M) → SeqD d :=
  gridToSeqD pkg.ε pkg.R pkg.M

/-- C0-extractable rounding function (constructive witness constructor). -/
noncomputable def WitnessPkgD.round {d : ℕ} (pkg : WitnessPkgD d) :
    SeqD d → GridPointD d pkg.ε pkg.R pkg.M :=
  roundToGridD pkg.ε pkg.R pkg.M

end ℓ2ZD
