import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Basic

/-!
# Constructive 1D Rellich-Kondrachov (Sequence Space)

## Extractable Witness Construction

**Primary theorem:** `totallyBounded_data` returns `Finset (GridPoint ε R M)`

All witness data uses **computable rational arithmetic**:
- `GridPoint ε R M` - dependent functions from IndexSet to coefficient boxes
- `gridFinset ε R M : Finset (GridPoint ε R M)` - explicit via `Finset.pi`
- `WitnessPkg` - fully extractable record (ε, R, M, δ, grid)

**Computable layer (gets extracted):**
- Parameters: ℚ
- Structures: ℕ, ℤ, Finset, GridPoint
- No classical choice in construction

**Proof layer (erased in extraction):**
- `gridToSeq : GridPoint → ℓ2Z` - evaluation to sequences
- `ℓ2Z` contains `Summable` proof field (requires classical logic)
- Bounds proven over ℝ via monotone inequalities

**No classical choice**: Grid built via `Finset.pi` (not `Fintype.equivFin`).
**No tsum in statements**: All bounds finitary `∀ F : Finset ℤ`.

## Main Results

- `totallyBounded_data` - primary constructive theorem (grid data)
- `WitnessPkg.sound` - packaged extractable artifact
- `totallyBounded` - derived ℓ2Z corollary

For L²(𝕋) version, see `RellichKondrachov1D/L2Bridge.lean`.
-/

namespace RellichKondrachov1D.Seq

open scoped BigOperators

/-! ## Core Types -/

/-- ℓ² sequences of complex numbers on ℤ. -/
structure ℓ2Z where
  a : ℤ → ℂ
  summable_sq : Summable (fun k => ‖a k‖^2)

namespace ℓ2Z

/-- Mean-zero condition = vanishing 0-mode -/
def meanZero (x : ℓ2Z) : Prop := x.a 0 = 0

/-- H¹ summability (frequency-weighted norm) -/
def h1Summable (x : ℓ2Z) : Prop :=
  Summable (fun k : ℤ => (1 + (2 * Real.pi * (k : ℝ))^2) * ‖x.a k‖^2)

/-- Finitary H¹ bound property -/
def h1BoundFinitary (R : ℝ) (x : ℓ2Z) : Prop :=
  ∀ (F : Finset ℤ), Finset.sum F (fun k => (1 + (2 * Real.pi * (k : ℝ))^2) * ‖x.a k‖^2) ≤ R^2

/-- H¹ ball membership - **finitary** (no tsum in statement!) -/
structure InH1Ball (R : ℝ) (x : ℓ2Z) : Prop where
  h1_bound : h1BoundFinitary R x

/-! ## Basic Operations -/

/-- Zero sequence -/
def zero : ℓ2Z where
  a := 0
  summable_sq := by
    simp only [Pi.zero_apply, norm_zero, sq, zero_mul]
    exact summable_zero

/-- Index set: non-zero frequencies up to M -/
def IndexSet (M : ℕ) : Finset ℤ :=
  (Finset.Icc (-M : ℤ) M).erase 0

lemma card_IndexSet (M : ℕ) : (IndexSet M).card = 2 * M := by
  classical
  have h0 : (0 : ℤ) ∈ Finset.Icc (-M : ℤ) M := by
    simp [Finset.mem_Icc]
  have hI : (Finset.Icc (-M : ℤ) M).card = 2 * M + 1 := by
    rw [Int.card_Icc]
    omega
  simp [IndexSet, hI, Finset.card_erase_of_mem h0]

/-- Membership in IndexSet: positive characterization -/
lemma mem_IndexSet_iff (M : ℕ) {k : ℤ} :
    k ∈ IndexSet M ↔ k ≠ 0 ∧ (-(M : ℤ) ≤ k) ∧ (k ≤ (M : ℤ)) := by
  simp [IndexSet, Finset.mem_erase, Finset.mem_Icc]

/-- Membership in IndexSet: negative characterization (for tail reasoning) -/
lemma not_mem_IndexSet_iff (M : ℕ) {k : ℤ} :
    k ∉ IndexSet M ↔ k = 0 ∨ k < -(M : ℤ) ∨ (M : ℤ) < k := by
  rw [← not_iff_not]
  push_neg
  simp [mem_IndexSet_iff]

/-- A finset splits into the filter of a predicate and its negation. -/
lemma Finset.filter_union_filter_not
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    s.filter p ∪ s.filter (fun x => ¬ p x) = s := by
  classical
  ext x
  by_cases hx : x ∈ s
  · by_cases hp : p x
    · simp [hx, hp]
    · simp [hx, hp]
  · by_cases hp : p x
    · simp [hx]
    · simp [hx]

/-- The two filtered pieces are disjoint. -/
lemma Finset.disjoint_filter_filter_not
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    Disjoint (s.filter p) (s.filter (fun x => ¬ p x)) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro x hx hp
  simp [Finset.mem_filter] at hx hp
  exact hp.2 hx.2

/-- Truncate to frequency window [-M, M] \ {0} -/
def truncate (M : ℕ) (x : ℓ2Z) : ℓ2Z where
  a := fun k => if k ≠ 0 ∧ |k| ≤ M then x.a k else 0
  summable_sq := by
    classical
    refine summable_of_ne_finset_zero (s := IndexSet M) ?_
    intro k hk
    have hcond : ¬ (k ≠ 0 ∧ |k| ≤ M) := by
      simpa [IndexSet, Finset.mem_Icc, abs_le] using hk
    simp [hcond, norm_zero, sq]

lemma truncate_meanZero {M : ℕ} {x : ℓ2Z} (_ : x.meanZero) :
    (x.truncate M).meanZero := by
  simp [meanZero, truncate]

/-! ## Finitary Inequalities -/

/-- Finitary comparison between ℓ² and the weighted H¹ sum. -/
theorem l2_le_weighted_sum {x : ℓ2Z} {R : ℝ} (hH1 : x.InH1Ball R) (F : Finset ℤ) :
    Finset.sum F (fun k => ‖x.a k‖^2) ≤ R^2 := by
  have bound := hH1.h1_bound F
  calc Finset.sum F (fun k => ‖x.a k‖^2)
      ≤ Finset.sum F (fun k => (1 + (2 * Real.pi * (k : ℝ))^2) * ‖x.a k‖^2) := by
        apply Finset.sum_le_sum
        intro k _
        have : 1 ≤ 1 + (2 * Real.pi * (k : ℝ))^2 := by
          linarith [sq_nonneg (2 * Real.pi * (k : ℝ))]
        calc ‖x.a k‖^2 = 1 * ‖x.a k‖^2 := by ring
          _ ≤ (1 + (2 * Real.pi * (k : ℝ))^2) * ‖x.a k‖^2 := by
              apply mul_le_mul_of_nonneg_right this (sq_nonneg _)
    _ ≤ R^2 := bound

/-- Tail bound (finitary form): frequencies beyond M decay -/
theorem tail_bound_finitary {x : ℓ2Z} {R : ℝ} (M : ℕ) (hR : 0 < R)
    (hH1 : x.InH1Ball R) (hM : 0 < (M : ℝ)) (F : Finset {k : ℤ // (M : ℝ) < |(k : ℝ)|}) :
    Finset.sum F (fun k => ‖x.a k.val‖^2) ≤ R^2 / ((2 * Real.pi * M)^2) := by
  by_cases hF : F.Nonempty
  · have hpi : 0 < Real.pi := Real.pi_pos
    have h2piM : 0 < 2 * Real.pi * M := by
      apply mul_pos
      apply mul_pos
      · norm_num
      · exact hpi
      · exact hM
    have h2piM_sq : 0 < (2 * Real.pi * M)^2 := by
      apply sq_pos_of_pos h2piM

    -- Convert to regular finset
    let F' : Finset ℤ := F.image Subtype.val

    have bound := hH1.h1_bound F'

    calc Finset.sum F (fun k => ‖x.a k.val‖^2)
        ≤ Finset.sum F (fun k => (1 + (2 * Real.pi * (k.val : ℝ))^2) * ‖x.a k.val‖^2 / (2 * Real.pi * M)^2) := by
          apply Finset.sum_le_sum
          intro ⟨k, hk⟩ _
          dsimp
          have key : (2 * Real.pi * M)^2 ≤ 1 + (2 * Real.pi * (k : ℝ))^2 := by
            have habs : M ≤ |(k : ℝ)| := le_of_lt hk
            have h1 : 0 ≤ 2 * Real.pi * M := by
              apply mul_nonneg
              apply mul_nonneg
              · norm_num
              · apply le_of_lt hpi
              · linarith
            have h2 : 0 ≤ 2 * Real.pi * |(k : ℝ)| := by
              apply mul_nonneg
              apply mul_nonneg
              · norm_num
              · apply le_of_lt hpi
              · apply abs_nonneg
            have step1 : (2 * Real.pi * M)^2 ≤ (2 * Real.pi * |(k : ℝ)|)^2 := by
              apply sq_le_sq'
              · linarith
              · apply mul_le_mul_of_nonneg_left habs
                apply mul_nonneg
                · norm_num
                · apply le_of_lt hpi
            have step2 : (2 * Real.pi * |(k : ℝ)|)^2 = (2 * Real.pi * (k : ℝ))^2 := by
              have : |(k : ℝ)| * |(k : ℝ)| = (k : ℝ) * (k : ℝ) := abs_mul_abs_self (k : ℝ)
              rw [sq, sq]
              calc 2 * Real.pi * |(k : ℝ)| * (2 * Real.pi * |(k : ℝ)|)
                  = (2 * Real.pi) * (2 * Real.pi) * (|(k : ℝ)| * |(k : ℝ)|) := by ring
                _ = (2 * Real.pi) * (2 * Real.pi) * ((k : ℝ) * (k : ℝ)) := by rw [this]
                _ = 2 * Real.pi * (k : ℝ) * (2 * Real.pi * (k : ℝ)) := by ring
            calc (2 * Real.pi * M)^2
                ≤ (2 * Real.pi * |(k : ℝ)|)^2 := step1
              _ = (2 * Real.pi * (k : ℝ))^2 := step2
              _ ≤ 1 + (2 * Real.pi * (k : ℝ))^2 := by linarith [sq_nonneg (2 * Real.pi * (k : ℝ))]
          have h_ne : (2 * Real.pi * M)^2 ≠ 0 := ne_of_gt h2piM_sq
          calc ‖x.a k‖^2
              = (2 * Real.pi * M)^2 / (2 * Real.pi * M)^2 * ‖x.a k‖^2 := by
                  rw [div_self h_ne, one_mul]
            _ ≤ (1 + (2 * Real.pi * (k : ℝ))^2) / (2 * Real.pi * M)^2 * ‖x.a k‖^2 := by
                  apply mul_le_mul_of_nonneg_right
                  · apply div_le_div_of_nonneg_right key (le_of_lt h2piM_sq)
                  · exact sq_nonneg _
            _ = (1 + (2 * Real.pi * (k : ℝ))^2) * ‖x.a k‖^2 / (2 * Real.pi * M)^2 := by ring
      _ = Finset.sum F (fun k => (1 + (2 * Real.pi * (k.val : ℝ))^2) * ‖x.a k.val‖^2) / (2 * Real.pi * M)^2 := by
            rw [Finset.sum_div]
      _ ≤ Finset.sum F' (fun k => (1 + (2 * Real.pi * (k : ℝ))^2) * ‖x.a k‖^2) / (2 * Real.pi * M)^2 := by
            apply div_le_div_of_nonneg_right _ (le_of_lt h2piM_sq)
            have : F' = F.image Subtype.val := rfl
            rw [this]
            rw [Finset.sum_image]
            intro a _ b _ hab
            exact Subtype.ext hab
      _ ≤ R^2 / (2 * Real.pi * M)^2 := by
            apply div_le_div_of_nonneg_right bound (le_of_lt h2piM_sq)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hF]
    have : 0 < R^2 / (2 * Real.pi * M)^2 := by
      apply div_pos
      · exact sq_pos_of_pos hR
      · apply sq_pos_of_pos
        apply mul_pos
        apply mul_pos
        · norm_num
        · exact Real.pi_pos
        · exact hM
    linarith

/-! ## Helper Lemmas for Constructive Proof -/

/-- Sum over a filtered `Finset` equals the sum over the corresponding subtype. -/
lemma sum_filter_toSubtype {α : Type*} [AddCommMonoid α]
    (F : Finset ℤ) (p : ℤ → Prop) [DecidablePred p] (f : ℤ → α) :
    Finset.sum (F.filter p) f = Finset.sum (F.subtype p) (fun k => f k.val) := by
  simp

/-- Floor bound helper: if |x| ≤ B then the floor of x/δ has bounded natAbs -/
lemma natAbs_floor_div_le_of_le
    {δ x B : ℝ} (hδ : 0 < δ) (hx : |x| ≤ B) :
    Int.natAbs (Int.floor (x / δ)) ≤ Nat.ceil (B / δ) + 1 := by
  have h1 : x / δ ≤ B / δ :=
    div_le_div_of_nonneg_right (le_of_abs_le hx) (le_of_lt hδ)
  have h2 : -(B / δ) ≤ x / δ := by
    have : -B ≤ x := neg_le_of_abs_le hx
    calc -(B / δ) = -B / δ := by ring
      _ ≤ x / δ := div_le_div_of_nonneg_right this (le_of_lt hδ)
  have floor_le : (Int.floor (x / δ) : ℝ) ≤ B / δ :=
    calc (Int.floor (x / δ) : ℝ) ≤ x / δ := Int.floor_le _
      _ ≤ B / δ := h1
  have le_floor : -(B / δ) - 1 < (Int.floor (x / δ) : ℝ) := by
    have : x / δ - 1 < Int.floor (x / δ) := Int.sub_one_lt_floor _
    linarith
  have abs_bound_real : |(Int.floor (x / δ) : ℝ)| ≤ B / δ + 1 := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith
    · linarith
  have ceil_bound : B / δ ≤ Nat.ceil (B / δ) := Nat.le_ceil _
  have bound_with_ceil : |(Int.floor (x / δ) : ℝ)| ≤ ↑(Nat.ceil (B / δ) + 1) := by
    push_cast
    linarith
  have natabs_eq : (Int.natAbs (Int.floor (x / δ)) : ℝ) = |(Int.floor (x / δ) : ℝ)| := by
    norm_cast
    simp
  rw [← natabs_eq] at bound_with_ceil
  exact Nat.cast_le.mp bound_with_ceil

/-! ## Grid Construction -/

/-! ## Rational Bounds for Extractability -/

/-- Rational lower bound for π (used for computable witness generation) -/
def pi_rat_lb : ℚ := 3

lemma pi_gt_pi_rat_lb : (pi_rat_lb : ℝ) < Real.pi := by
  norm_num [pi_rat_lb]
  exact Real.pi_gt_three

/-- Coefficient radius bound (computable rational version) -/
def coeffBound (R : ℚ) (k : ℤ) : ℚ :=
  if k = 0 then 0 else R

/-- The rational bound is valid: actual coefficient is within it -/
lemma coeffBound_valid (R : ℝ) (k : ℤ) (hR : 0 ≤ R) :
    R / Real.sqrt (1 + (2 * Real.pi * (k : ℝ))^2) ≤ R := by
  by_cases hk : k = 0
  · simp [hk]
  · have h_base : 1 ≤ 1 + (2 * Real.pi * (k : ℝ))^2 := by
      have : 0 ≤ (2 * Real.pi * (k : ℝ))^2 := sq_nonneg _
      linarith
    have h_sqrt_ge : 1 ≤ Real.sqrt (1 + (2 * Real.pi * (k : ℝ))^2) := by
      calc 1 = Real.sqrt 1 := by rw [Real.sqrt_one]
        _ ≤ Real.sqrt (1 + (2 * Real.pi * (k : ℝ))^2) := Real.sqrt_le_sqrt h_base
    have h_sqrt_pos : 0 < Real.sqrt (1 + (2 * Real.pi * (k : ℝ))^2) := by
      calc 0 < 1 := by norm_num
        _ ≤ Real.sqrt (1 + (2 * Real.pi * (k : ℝ))^2) := h_sqrt_ge
    calc R / Real.sqrt (1 + (2 * Real.pi * (k : ℝ))^2)
        = R * (1 / Real.sqrt (1 + (2 * Real.pi * (k : ℝ))^2)) := by ring
      _ ≤ R * 1 := by
          apply mul_le_mul_of_nonneg_left _ hR
          rw [div_le_one h_sqrt_pos]
          exact h_sqrt_ge
      _ = R := by ring

/-- Frequency cutoff (computable with rational parameters) -/
def M_of (ε R : ℚ) : ℕ := Nat.ceil (R / (pi_rat_lb * ε)) + 1

/-- Grid mesh (computable, avoids sqrt) -/
def mesh (ε : ℚ) (M : ℕ) : ℚ :=
  ε / (2 * (2 * M + 1))

/-- The mesh formula gives a valid upper bound -/
lemma mesh_bound_valid (ε : ℝ) (M : ℕ) (hε : 0 < ε) (hM : 0 < M) :
    (ε : ℝ) / (2 * (2 * (M : ℝ) + 1)) ≤ ε / (2 * Real.sqrt (2 * (2 * (M : ℝ)))) := by
  have hM_cast : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have h_sqrt_arg_pos : 0 < 2 * (2 * (M : ℝ)) := by linarith
  have h_sqrt_pos : 0 < Real.sqrt (2 * (2 * (M : ℝ))) := by
    apply Real.sqrt_pos.mpr
    exact h_sqrt_arg_pos
  apply div_le_div_of_nonneg_left
  · exact le_of_lt hε
  · apply mul_pos; norm_num; exact h_sqrt_pos
  · apply mul_le_mul_of_nonneg_left
    · have h1 : Real.sqrt (2 * (2 * (M : ℝ))) ≤ 2 * (M : ℝ) + 1 := by
        have h_rhs_pos : 0 ≤ 2 * (M : ℝ) + 1 := by linarith
        rw [Real.sqrt_le_left h_rhs_pos]
        calc 2 * (2 * (M : ℝ))
            = 4 * (M : ℝ) := by ring
          _ ≤ 4 * (M : ℝ)^2 + 4 * (M : ℝ) + 1 := by
              have : 0 ≤ 4 * (M : ℝ)^2 + 1 := by
                have h1 : 0 ≤ (M : ℝ)^2 := sq_nonneg _
                linarith
              linarith
          _ = (2 * (M : ℝ) + 1)^2 := by ring
      exact h1
    · norm_num

/-- Integer box for coefficient k -/
def coeffBox (ε R : ℚ) (M : ℕ) (k : ℤ) : Finset (ℤ × ℤ) :=
  let δ := mesh ε M
  let bound := coeffBound R k
  let rad := Nat.ceil (bound / δ) + 1
  (Finset.Icc (-rad : ℤ) rad) ×ˢ (Finset.Icc (-rad : ℤ) rad)

/-- Coefficient box as a subtype finset (for dependent pi construction) -/
def coeffBoxSubtype (ε R : ℚ) (M : ℕ) (k : ℤ) :
    Finset { p : ℤ × ℤ // p ∈ coeffBox ε R M k } :=
  (coeffBox ε R M k).attach

/-- The origin always lies inside any coefficient box. -/
lemma zero_in_coeffBox (ε R : ℚ) (M : ℕ) (k : ℤ) :
    (0, 0) ∈ coeffBox ε R M k := by
  classical
  unfold coeffBox
  set δ := mesh ε M
  set bound := coeffBound R k
  set rad := Nat.ceil (bound / δ) + 1
  have hrad : 0 ≤ (rad : ℤ) := by exact_mod_cast (Nat.zero_le rad)
  have hin : (0 : ℤ) ∈ Finset.Icc (-rad : ℤ) rad := by
    simp [Finset.mem_Icc, hrad]
  exact Finset.mem_product.mpr ⟨hin, hin⟩

/-- Grid point: choice of integer pair for each frequency in IndexSet M -/
def GridPoint (ε R : ℚ) (M : ℕ) : Type :=
  (k : ℤ) → k ∈ IndexSet M → { p : ℤ × ℤ // p ∈ coeffBox ε R M k }

/-- Canonical zero grid point (all coefficients zero). -/
def zeroGridPoint (ε R : ℚ) (M : ℕ) : GridPoint ε R M :=
  fun k hk => ⟨(0, 0), by
    simpa using zero_in_coeffBox ε R M k⟩

/-- Each box is a fintype -/
instance boxFintype (ε R : ℚ) (M : ℕ) (k : ℤ) : Fintype { p : ℤ × ℤ // p ∈ coeffBox ε R M k } :=
  Fintype.ofFinset (coeffBox ε R M k) (fun _ => Iff.rfl)

/-- A canonical, choice-free enumeration of all grid points. -/
def gridFinset (ε R : ℚ) (M : ℕ) : Finset (GridPoint ε R M) :=
  Finset.pi (IndexSet M) (fun k => coeffBoxSubtype ε R M k)

lemma gridFinset_nonempty (ε R : ℚ) (M : ℕ) :
    (gridFinset ε R M).Nonempty := by
  classical
  refine ⟨zeroGridPoint ε R M, ?_⟩
  refine Finset.mem_pi.mpr ?_
  intro k hk
  simp [zeroGridPoint, coeffBoxSubtype]

/-- Convert grid point to ℓ2Z sequence (evaluation happens in proof layer) -/
def gridToSeq (ε R : ℚ) (M : ℕ) (g : GridPoint ε R M) : ℓ2Z where
  a := fun k =>
    if h : k ∈ IndexSet M then
      let δ := mesh ε M
      let p := g k h
      ⟨(δ : ℝ) * p.val.1, (δ : ℝ) * p.val.2⟩
    else 0
  summable_sq := by
    classical  -- Only in the proof, not the def
    apply summable_of_ne_finset_zero (s := IndexSet M)
    intro k hk
    by_cases h : k ∈ IndexSet M
    · contradiction
    · simp [h]

/-- Finite set of center sequences (explicit constructive witness) -/
noncomputable def centersFinset (ε R : ℚ) (M : ℕ) : Finset ℓ2Z := by
  classical
  exact (gridFinset ε R M).image (gridToSeq ε R M)

/-- **EXTRACTABLE ARTIFACT**: The object that can be serialized/exported.
    Contains only ℚ, ℕ, Finset data - no ℝ, no ℂ, no Summable proofs. -/
structure WitnessPkg where
  ε : ℚ
  R : ℚ

/-- The frequency cutoff for a witness package. -/
def WitnessPkg.M (P : WitnessPkg) : ℕ := M_of P.ε P.R

/-- The grid mesh for a witness package. -/
def WitnessPkg.δ (P : WitnessPkg) : ℚ := mesh P.ε P.M

/-- The finite grid of witness points. -/
def WitnessPkg.grid (P : WitnessPkg) : Finset (GridPoint P.ε P.R P.M) :=
  gridFinset P.ε P.R P.M

/-- The grid is explicitly nonempty (contains the zero grid point). -/
lemma WitnessPkg.grid_nonempty (P : WitnessPkg) :
    (P.grid).Nonempty :=
  gridFinset_nonempty P.ε P.R P.M

/-- Evaluation of grid point to ℓ² sequence (proof-only, gets erased in extraction). -/
def WitnessPkg.eval (P : WitnessPkg) : (GridPoint P.ε P.R P.M) → ℓ2Z :=
  gridToSeq P.ε P.R P.M

/-! ## Rounding -/

/-- Round coefficient to nearest grid point -/
noncomputable def roundCoeff (δ : ℝ) (c : ℂ) : ℤ × ℤ :=
  (Int.floor (c.re / δ), Int.floor (c.im / δ))

/-- Round a sequence to the grid -/
noncomputable def roundToGrid (ε _R : ℚ) (M : ℕ) (x : ℓ2Z) : ℓ2Z where
  a := fun k =>
    if k ∈ IndexSet M then
      let δ := mesh ε M
      let p := roundCoeff (δ : ℝ) (x.a k)
      ⟨(δ : ℝ) * p.1, (δ : ℝ) * p.2⟩
    else 0
  summable_sq := by
    apply summable_of_ne_finset_zero (s := IndexSet M)
    intro k hk
    by_cases h : k ∈ IndexSet M
    · contradiction
    · simp [h]

/-- Rounding error bound -/
lemma round_error (δ : ℝ) (hδ : 0 < δ) (c : ℂ) :
    ‖c - ⟨δ * (roundCoeff δ c).1, δ * (roundCoeff δ c).2⟩‖
      ≤ Real.sqrt 2 * δ := by
  simp only [roundCoeff]
  set n_re := Int.floor (c.re / δ)
  set n_im := Int.floor (c.im / δ)

  -- Error in each coordinate
  have re_err : |c.re - δ * n_re| ≤ δ := by
    have h1 : c.re / δ - 1 < n_re := Int.sub_one_lt_floor _
    have h2 : n_re ≤ c.re / δ := Int.floor_le (c.re / δ)
    rw [abs_sub_le_iff]
    constructor
    · have eq1 : c.re - δ * n_re = δ * (c.re / δ - n_re) := by field_simp
      rw [eq1]
      have bound : c.re / δ - n_re < 1 := by linarith
      have : δ * (c.re / δ - n_re) < δ * 1 := mul_lt_mul_of_pos_left bound hδ
      linarith
    · have eq1 : δ * n_re - c.re = δ * (n_re - c.re / δ) := by field_simp
      rw [eq1]
      have bound : n_re - c.re / δ ≤ 0 := by linarith
      have : δ * (n_re - c.re / δ) ≤ δ * 0 := mul_le_mul_of_nonneg_left bound (le_of_lt hδ)
      linarith

  have im_err : |c.im - δ * n_im| ≤ δ := by
    have h1 : c.im / δ - 1 < n_im := Int.sub_one_lt_floor _
    have h2 : n_im ≤ c.im / δ := Int.floor_le (c.im / δ)
    rw [abs_sub_le_iff]
    constructor
    · have eq1 : c.im - δ * n_im = δ * (c.im / δ - n_im) := by field_simp
      rw [eq1]
      have bound : c.im / δ - n_im < 1 := by linarith
      have : δ * (c.im / δ - n_im) < δ * 1 := mul_lt_mul_of_pos_left bound hδ
      linarith
    · have eq1 : δ * n_im - c.im = δ * (n_im - c.im / δ) := by field_simp
      rw [eq1]
      have bound : n_im - c.im / δ ≤ 0 := by linarith
      have : δ * (n_im - c.im / δ) ≤ δ * 0 := mul_le_mul_of_nonneg_left bound (le_of_lt hδ)
      linarith

  -- Complex norm bound
  set c' : ℂ := ⟨δ * n_re, δ * n_im⟩
  have h_re : (c - c').re = c.re - δ * n_re := by simp [c']
  have h_im : (c - c').im = c.im - δ * n_im := by simp [c']

  have hδpos : 0 ≤ δ := le_of_lt hδ

  -- Bound each coordinate square
  have re_sq_bound : (c.re - δ * n_re)^2 ≤ δ^2 := by
    calc (c.re - δ * n_re)^2
        = |c.re - δ * n_re|^2 := (sq_abs _).symm
      _ ≤ δ^2 := by
          rw [sq, sq]
          exact mul_self_le_mul_self (abs_nonneg _) re_err

  have im_sq_bound : (c.im - δ * n_im)^2 ≤ δ^2 := by
    calc (c.im - δ * n_im)^2
        = |c.im - δ * n_im|^2 := (sq_abs _).symm
      _ ≤ δ^2 := by
          rw [sq, sq]
          exact mul_self_le_mul_self (abs_nonneg _) im_err

  -- Bound the sum
  have sum_bound : (c.re - δ * n_re)^2 + (c.im - δ * n_im)^2 ≤ 2 * δ^2 := by
    calc (c.re - δ * n_re)^2 + (c.im - δ * n_im)^2
        ≤ δ^2 + δ^2 := add_le_add re_sq_bound im_sq_bound
      _ = 2 * δ^2 := by ring

  -- Main calculation
  calc ‖c - c'‖
      = Real.sqrt (‖c - c'‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (Complex.normSq (c - c')) := by
          congr 1
          exact (Complex.normSq_eq_norm_sq _).symm
    _ = Real.sqrt ((c - c').re^2 + (c - c').im^2) := by
          congr 1; rw [Complex.normSq_apply]; ring
    _ = Real.sqrt ((c.re - δ * n_re)^2 + (c.im - δ * n_im)^2) := by
          rw [h_re, h_im]
    _ ≤ Real.sqrt (2 * δ^2) := Real.sqrt_le_sqrt sum_bound
    _ = Real.sqrt 2 * δ := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hδpos]

/-! ## Helper Lemmas for Totally Bounded Proof -/

/-- Coefficient bound from H¹ norm (for ℚ parameters) -/
lemma coeff_bound_from_H1 {x : ℓ2Z} {R : ℝ} (_hR : 0 < R) (hx : x.InH1Ball R) (k : ℤ) (_hk : k ≠ 0) :
    ‖x.a k‖^2 ≤ R^2 := by
  have h_weight : 1 + (2 * Real.pi * (k : ℝ))^2 > 0 := by
    linarith [sq_nonneg (2 * Real.pi * (k : ℝ))]
  have bound := hx.h1_bound {k}
  simp only [Finset.sum_singleton] at bound
  have h1 : (1 + (2 * Real.pi * (k : ℝ))^2) * ‖x.a k‖^2 ≤ R^2 := bound
  have h2 : ‖x.a k‖^2 * (1 + (2 * Real.pi * (k : ℝ))^2) ≤ R^2 := by
    rwa [mul_comm] at h1
  have h3 : ‖x.a k‖^2 * 1 ≤ ‖x.a k‖^2 * (1 + (2 * Real.pi * (k : ℝ))^2) := by
    apply mul_le_mul_of_nonneg_left
    · linarith [sq_nonneg (2 * Real.pi * (k : ℝ))]
    · exact sq_nonneg _
  calc ‖x.a k‖^2
      = ‖x.a k‖^2 * 1 := by ring
    _ ≤ ‖x.a k‖^2 * (1 + (2 * Real.pi * (k : ℝ))^2) := h3
    _ ≤ R^2 := h2

/-- Mesh is positive when ε > 0 and M > 0 -/
lemma mesh_pos {ε : ℚ} {M : ℕ} (hε : 0 < ε) (hM : M ≠ 0) : 0 < (mesh ε M : ℝ) := by
  unfold mesh
  push_cast
  apply div_pos
  · exact_mod_cast hε
  · apply mul_pos
    · norm_num
    · apply add_pos_of_pos_of_nonneg
      · apply mul_pos
        · norm_num
        · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM)
      · norm_num

/-- M_of is always positive -/
lemma M_of_pos (ε R : ℚ) : 0 < M_of ε R := by
  unfold M_of
  exact Nat.succ_pos _

/-- Mesh is positive for M_of (eliminates M ≠ 0 hypothesis clutter) -/
lemma mesh_pos_M_of {ε R : ℚ} (hε : 0 < ε) : 0 < (mesh ε (M_of ε R) : ℝ) := by
  have hM : M_of ε R ≠ 0 := ne_of_gt (M_of_pos ε R)
  exact mesh_pos hε hM

/-- The tail bound for M_of is ≤ (ε/2)² -/
lemma tail_bound_M_of {ε R : ℚ} (hε : 0 < (ε : ℝ)) (hR : 0 < (R : ℝ)) :
    (R : ℝ)^2 / ((2 * Real.pi * (M_of ε R : ℝ))^2) ≤ ((ε : ℝ) / 2)^2 := by
  set M := M_of ε R with hM_def

  -- Rational positivity (for ℚ arithmetic)
  have ε_pos_rat : 0 < ε := Rat.cast_pos.mp hε
  have R_pos_rat : 0 < R := Rat.cast_pos.mp hR
  have pi_lb_pos : 0 < pi_rat_lb := by norm_num [pi_rat_lb]

  -- Key: M > R/(pi_rat_lb * ε) in ℚ
  have hM_ge_rat : (M : ℚ) > R / (pi_rat_lb * ε) := by
    unfold M M_of
    have h1 : R / (pi_rat_lb * ε) ≤ ↑⌈R / (pi_rat_lb * ε)⌉₊ := Nat.le_ceil _
    have h2 : (⌈R / (pi_rat_lb * ε)⌉₊ : ℕ) < ⌈R / (pi_rat_lb * ε)⌉₊ + 1 := Nat.lt_succ_self _
    have h2' : (⌈R / (pi_rat_lb * ε)⌉₊ : ℚ) < (⌈R / (pi_rat_lb * ε)⌉₊ + 1 : ℕ) := by exact_mod_cast h2
    exact h1.trans_lt h2'

  -- Transfer to ℝ: M > R/(Real.pi * ε)
  have hM_ge : (M : ℝ) > (R : ℝ) / (Real.pi * (ε : ℝ)) := by
    have h1 : (M : ℝ) > (R / (pi_rat_lb * ε) : ℚ) := by exact_mod_cast hM_ge_rat
    have h2 : (R / (pi_rat_lb * ε) : ℚ) = (R : ℝ) / ((pi_rat_lb : ℝ) * (ε : ℝ)) := by
      push_cast; rfl
    have h3 : (R : ℝ) / ((pi_rat_lb : ℝ) * (ε : ℝ)) ≥ (R : ℝ) / (Real.pi * (ε : ℝ)) := by
      apply div_le_div_of_nonneg_left (le_of_lt hR)
      · positivity
      · apply mul_le_mul_of_nonneg_right (le_of_lt pi_gt_pi_rat_lb) (le_of_lt hε)
    calc (M : ℝ)
        > (R / (pi_rat_lb * ε) : ℚ) := h1
      _ = (R : ℝ) / ((pi_rat_lb : ℝ) * (ε : ℝ)) := h2
      _ ≥ (R : ℝ) / (Real.pi * (ε : ℝ)) := h3

  -- Continue: 2πM > 2R/ε
  have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.mpr (M_of_pos ε R)
  have key : 2 * Real.pi * (M : ℝ) > 2 * (R : ℝ) / (ε : ℝ) := by
    have step : Real.pi * (M : ℝ) > (R : ℝ) / (ε : ℝ) := by
      calc Real.pi * (M : ℝ)
          > Real.pi * ((R : ℝ) / (Real.pi * (ε : ℝ))) := by
            apply mul_lt_mul_of_pos_left hM_ge Real.pi_pos
        _ = (R : ℝ) / (ε : ℝ) := by field_simp
    have : 2 * (Real.pi * (M : ℝ)) > 2 * ((R : ℝ) / (ε : ℝ)) := by
      apply mul_lt_mul_of_pos_left step; norm_num
    calc 2 * Real.pi * (M : ℝ)
        = 2 * (Real.pi * (M : ℝ)) := by ring
      _ > 2 * ((R : ℝ) / (ε : ℝ)) := this
      _ = 2 * (R : ℝ) / (ε : ℝ) := by ring

  -- Square and conclude
  have sq_bound : ((2 * Real.pi * (M : ℝ))^2) > ((2 * (R : ℝ) / (ε : ℝ))^2) := by
    have h1 : 0 < 2 * Real.pi * (M : ℝ) := by positivity
    have h2 : 0 < 2 * (R : ℝ) / (ε : ℝ) := by positivity
    exact sq_lt_sq' (by linarith) key

  have main_ineq : (R : ℝ)^2 / ((2 * Real.pi * (M : ℝ))^2) < ((ε : ℝ) / 2)^2 := by
    calc (R : ℝ)^2 / ((2 * Real.pi * (M : ℝ))^2)
        < (R : ℝ)^2 / ((2 * (R : ℝ) / (ε : ℝ))^2) := by
          apply div_lt_div_of_pos_left (sq_pos_of_pos hR) _ sq_bound
          apply sq_pos_of_pos; positivity
      _ = (ε : ℝ)^2 / 4 := by field_simp; ring
      _ = ((ε : ℝ) / 2)^2 := by ring

  exact le_of_lt main_ineq

/-- Helper lemma: rounding sum bound -/
lemma rounding_sum_le_quarter (M : ℕ) (hM : M ≠ 0) :
    (M : ℝ) / ((2 * (M : ℝ) + 1)^2) ≤ 1 / 4 := by
  -- Key insight: 4M ≤ (2M+1)² because (2M+1)² = 4M² + 4M + 1
  have key : 4 * (M : ℝ) ≤ (2 * (M : ℝ) + 1)^2 := by
    calc 4 * (M : ℝ)
        ≤ 4 * (M : ℝ)^2 + 4 * (M : ℝ) + 1 := by
          have : 0 ≤ 4 * (M : ℝ)^2 + 1 := by positivity
          linarith
      _ = (2 * (M : ℝ) + 1)^2 := by ring

  -- Divide both sides by 4 * (2M+1)²
  have den_pos : 0 < (2 * (M : ℝ) + 1)^2 := by
    apply sq_pos_of_pos
    have : 0 < (M : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM)
    linarith

  calc (M : ℝ) / ((2 * (M : ℝ) + 1)^2)
      = (4 * (M : ℝ)) / (4 * ((2 * (M : ℝ) + 1)^2)) := by
        have h : (4 : ℝ) ≠ 0 := by norm_num
        conv_lhs => rw [← mul_div_mul_left (M : ℝ) ((2 * (M : ℝ) + 1)^2) h]
    _ ≤ ((2 * (M : ℝ) + 1)^2) / (4 * ((2 * (M : ℝ) + 1)^2)) := by
        apply div_le_div_of_nonneg_right key
        positivity
    _ = 1 / 4 := by
        have h : (2 * (M : ℝ) + 1)^2 ≠ 0 := ne_of_gt den_pos
        calc ((2 * (M : ℝ) + 1)^2) / (4 * ((2 * (M : ℝ) + 1)^2))
            = ((2 * (M : ℝ) + 1)^2) / ((2 * (M : ℝ) + 1)^2) / 4 := by rw [div_mul_eq_div_div_swap]
          _ = 1 / 4 := by rw [div_self h]

/-- The rounding sum with the new mesh is exactly (ε/2)² -/
lemma rounding_bound_mesh (ε : ℚ) (M : ℕ) (hM : M ≠ 0) :
    (2 * M : ℝ) * (2 * ((mesh ε M : ℝ))^2) ≤ ((ε : ℝ) / 2)^2 := by
  unfold mesh
  push_cast

  -- LHS = 2M * 2 * (ε / (2*(2M+1)))²
  --     = 4M * ε² / (4*(2M+1)²)
  --     = M * ε² / (2M+1)²

  have expand : (2 * (M : ℝ)) * (2 * ((ε : ℝ) / (2 * (2 * (M : ℝ) + 1)))^2)
              = (M : ℝ) * (ε : ℝ)^2 / ((2 * (M : ℝ) + 1)^2) := by
    have h_den : 2 * (2 * (M : ℝ) + 1) ≠ 0 := by
      apply mul_ne_zero
      · norm_num
      · have : 0 < (M : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM)
        linarith
    have h_den_sq : (2 * (2 * (M : ℝ) + 1))^2 ≠ 0 := pow_ne_zero 2 h_den
    calc (2 * (M : ℝ)) * (2 * ((ε : ℝ) / (2 * (2 * (M : ℝ) + 1)))^2)
        = (2 * (M : ℝ)) * (2 * ((ε : ℝ)^2 / (2 * (2 * (M : ℝ) + 1))^2)) := by rw [div_pow]
      _ = 2 * (M : ℝ) * 2 * ((ε : ℝ)^2 / (2 * (2 * (M : ℝ) + 1))^2) := by ring
      _ = 4 * (M : ℝ) * ((ε : ℝ)^2 / (2 * (2 * (M : ℝ) + 1))^2) := by ring
      _ = 4 * (M : ℝ) * (ε : ℝ)^2 / (2 * (2 * (M : ℝ) + 1))^2 := by rw [mul_div_assoc]
      _ = (M : ℝ) * (ε : ℝ)^2 * 4 / (4 * ((2 * (M : ℝ) + 1)^2)) := by ring
      _ = (M : ℝ) * (ε : ℝ)^2 / ((2 * (M : ℝ) + 1)^2) := by
          have h4_ne : (4 : ℝ) ≠ 0 := by norm_num
          have h4_pos : (0 : ℝ) < 4 := by norm_num
          have h_denom_ne : 4 * ((2 * (M : ℝ) + 1)^2) ≠ 0 := by
            apply mul_ne_zero h4_ne
            apply ne_of_gt
            apply sq_pos_of_pos
            have : 0 < (M : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM)
            linarith
          calc (M : ℝ) * (ε : ℝ)^2 * 4 / (4 * ((2 * (M : ℝ) + 1)^2))
              = ((M : ℝ) * (ε : ℝ)^2 * 4) / (4 * ((2 * (M : ℝ) + 1)^2)) := rfl
            _ = ((M : ℝ) * (ε : ℝ)^2) * (4 / (4 * ((2 * (M : ℝ) + 1)^2))) := by rw [mul_div_assoc]
            _ = ((M : ℝ) * (ε : ℝ)^2) * (1 / ((2 * (M : ℝ) + 1)^2)) := by
                congr 1
                rw [div_mul_eq_div_div, div_self h4_ne, one_div]
            _ = ((M : ℝ) * (ε : ℝ)^2) / ((2 * (M : ℝ) + 1)^2) := by rw [mul_one_div]

  rw [expand]

  -- RHS = ε²/4
  -- Need: M*ε² / (2M+1)² ≤ ε²/4
  -- ⟺ M / (2M+1)² ≤ 1/4

  have : (M : ℝ) * (ε : ℝ)^2 / ((2 * (M : ℝ) + 1)^2)
       = (ε : ℝ)^2 * ((M : ℝ) / ((2 * (M : ℝ) + 1)^2)) := by
    ring

  rw [this]

  have ε_sq_nonneg : 0 ≤ (ε : ℝ)^2 := sq_nonneg _

  calc (ε : ℝ)^2 * ((M : ℝ) / ((2 * (M : ℝ) + 1)^2))
      ≤ (ε : ℝ)^2 * (1 / 4) := by
        apply mul_le_mul_of_nonneg_left _ ε_sq_nonneg
        exact rounding_sum_le_quarter M hM
    _ = ((ε : ℝ) / 2)^2 := by ring

/-- Rounded coefficient is in box (key geometric lemma) -/
lemma rounded_in_box {ε R : ℚ} {M : ℕ} {k : ℤ} {c : ℂ}
    (hε : 0 < (ε : ℝ)) (hR : 0 < (R : ℝ)) (hM : M ≠ 0) (hk : k ≠ 0)
    (hc : ‖c‖^2 ≤ (R : ℝ)^2) :
    roundCoeff (mesh ε M : ℝ) c ∈ coeffBox ε R M k := by
  simp only [coeffBox, roundCoeff, Finset.mem_product, Finset.mem_Icc]
  let δ := mesh ε M
  let bound := coeffBound R k
  let rad := Nat.ceil (bound / δ) + 1

  have hδ : 0 < (δ : ℝ) := mesh_pos (by exact_mod_cast hε : 0 < ε) hM
  have hbound : 0 ≤ (bound : ℝ) := by
    unfold bound coeffBound
    split_ifs
    · norm_num
    · exact_mod_cast le_of_lt hR
  have bound_eq_R : (bound : ℝ) = (R : ℝ) := by simp [bound, coeffBound, hk]

  -- |c| ≤ bound from the hypothesis
  have norm_le : ‖c‖ ≤ (bound : ℝ) := by
    rw [bound_eq_R]
    have : ‖c‖ = Real.sqrt (‖c‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    rw [this]
    have : (R : ℝ) = Real.sqrt ((R : ℝ)^2) := by
      rw [Real.sqrt_sq (le_of_lt hR)]
    rw [this]
    exact Real.sqrt_le_sqrt hc

  -- Component bounds
  have re_bound : |c.re| ≤ (bound : ℝ) := by
    have norm_sq_eq : ‖c‖^2 = c.re^2 + c.im^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have h1 : c.re^2 ≤ c.re^2 + c.im^2 := by
      linarith [sq_nonneg c.im]
    have h2 : |c.re|^2 ≤ ‖c‖^2 := by
      rw [sq_abs, norm_sq_eq]
      exact h1
    calc |c.re|
        = Real.sqrt (|c.re|^2) := by rw [Real.sqrt_sq (abs_nonneg _)]
      _ ≤ Real.sqrt (‖c‖^2) := Real.sqrt_le_sqrt h2
      _ = ‖c‖ := Real.sqrt_sq (norm_nonneg _)
      _ ≤ (bound : ℝ) := norm_le

  have im_bound : |c.im| ≤ (bound : ℝ) := by
    have norm_sq_eq : ‖c‖^2 = c.re^2 + c.im^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have h1 : c.im^2 ≤ c.re^2 + c.im^2 := by
      linarith [sq_nonneg c.re]
    have h2 : |c.im|^2 ≤ ‖c‖^2 := by
      rw [sq_abs, norm_sq_eq]
      exact h1
    calc |c.im|
        = Real.sqrt (|c.im|^2) := by rw [Real.sqrt_sq (abs_nonneg _)]
      _ ≤ Real.sqrt (‖c‖^2) := Real.sqrt_le_sqrt h2
      _ = ‖c‖ := Real.sqrt_sq (norm_nonneg _)
      _ ≤ (bound : ℝ) := norm_le

  -- Apply floor bound helper to each component
  -- First, relate the ℚ version of rad to the ℝ version used in natAbs_floor_div_le_of_le
  have rad_eq : rad = Nat.ceil ((bound : ℝ) / (δ : ℝ)) + 1 := by
    unfold rad
    congr 1
    -- After unfolding, need to prove: ⌈(bound / δ : ℚ)⌉₊ = ⌈((bound : ℝ) / (δ : ℝ))⌉₊
    -- Key: Nat.ceil commutes with ℚ→ℝ cast
    have h_cast : ((bound / δ : ℚ) : ℝ) = (bound : ℝ) / (δ : ℝ) := by
      push_cast
      rfl
    rw [← h_cast]
    -- Nat.ceil commutes with ℚ → ℝ cast (use Rat.ceil_cast from mathlib)
    have h_ceil_comm : (⌈(bound / δ : ℚ)⌉ : ℤ) = (⌈((bound / δ : ℚ) : ℝ)⌉ : ℤ) := by
      simp only [Rat.ceil_cast]
    calc Nat.ceil (bound / δ)
        = Int.toNat ⌈(bound / δ : ℚ)⌉ := rfl
      _ = Int.toNat ⌈((bound / δ : ℚ) : ℝ)⌉ := by rw [h_ceil_comm]
      _ = Nat.ceil ((bound / δ : ℚ) : ℝ) := rfl

  constructor
  · have re_natabs := natAbs_floor_div_le_of_le hδ re_bound
    -- re_natabs : Int.natAbs (Int.floor (c.re / (δ : ℝ))) ≤ Nat.ceil ((bound : ℝ) / (δ : ℝ)) + 1
    have re_natabs' : Int.natAbs (Int.floor (c.re / (δ : ℝ))) ≤ rad := by
      rw [rad_eq]
      exact re_natabs
    constructor
    · -- -(rad : ℤ) ≤ Int.floor (c.re / (δ : ℝ))
      have h_natabs : ((Int.floor (c.re / (δ : ℝ))).natAbs : ℤ) ≤ (rad : ℤ) := by
        exact Nat.cast_le.mpr re_natabs'
      calc -(rad : ℤ)
          ≤ -((Int.floor (c.re / (δ : ℝ))).natAbs : ℤ) := Int.neg_le_neg h_natabs
        _ ≤ Int.floor (c.re / (δ : ℝ)) := by
            have : -((Int.floor (c.re / (δ : ℝ))).natAbs : ℤ) ≤ Int.floor (c.re / (δ : ℝ)) := by
              cases Int.natAbs_eq (Int.floor (c.re / (δ : ℝ))) with
              | inl h => rw [h]; simp
              | inr h => rw [h]; simp
            exact this
    · -- Int.floor (c.re / (δ : ℝ)) ≤ rad
      calc Int.floor (c.re / (δ : ℝ))
          ≤ (Int.floor (c.re / (δ : ℝ))).natAbs := Int.le_natAbs
        _ ≤ rad := by exact Nat.cast_le.mpr re_natabs'
  · have im_natabs := natAbs_floor_div_le_of_le hδ im_bound
    have im_natabs' : Int.natAbs (Int.floor (c.im / (δ : ℝ))) ≤ rad := by
      rw [rad_eq]
      exact im_natabs
    constructor
    · -- -(rad : ℤ) ≤ Int.floor (c.im / (δ : ℝ))
      have h_natabs : ((Int.floor (c.im / (δ : ℝ))).natAbs : ℤ) ≤ (rad : ℤ) := by
        exact Nat.cast_le.mpr im_natabs'
      calc -(rad : ℤ)
          ≤ -((Int.floor (c.im / (δ : ℝ))).natAbs : ℤ) := Int.neg_le_neg h_natabs
        _ ≤ Int.floor (c.im / (δ : ℝ)) := by
            have : -((Int.floor (c.im / (δ : ℝ))).natAbs : ℤ) ≤ Int.floor (c.im / (δ : ℝ)) := by
              cases Int.natAbs_eq (Int.floor (c.im / (δ : ℝ))) with
              | inl h => rw [h]; simp
              | inr h => rw [h]; simp
            exact this
    · -- Int.floor (c.im / (δ : ℝ)) ≤ rad
      calc Int.floor (c.im / (δ : ℝ))
          ≤ (Int.floor (c.im / (δ : ℝ))).natAbs := Int.le_natAbs
        _ ≤ rad := by exact Nat.cast_le.mpr im_natabs'

/-! ## Main Theorem -/

/-- Core soundness lemma for the canonical grid. -/
lemma gridFinset_sound (ε R : ℚ) (hε : 0 < (ε : ℝ)) (hR : 0 < (R : ℝ)) :
    ∀ (x : ℓ2Z), x.meanZero → x.InH1Ball (R : ℝ) →
      ∃ g ∈ gridFinset ε R (M_of ε R), ∀ F : Finset ℤ,
        Finset.sum F (fun k => ‖x.a k - (gridToSeq ε R (M_of ε R) g).a k‖^2) < (ε : ℝ)^2 := by
  -- Step 1: Choose M using M_of to control tail error
  set M := M_of ε R with hMdef

  have hM : 0 < (M : ℝ) := by
    simpa [hMdef] using (Nat.cast_pos.mpr (M_of_pos ε R))

  have hM_ne : M ≠ 0 := by
    simpa [hMdef] using (Nat.pos_iff_ne_zero.mp (M_of_pos ε R))

  -- Step 2: Construct the finite grid
  intro x hx_mean hx_H1

  -- Step 3: Construct the grid point that x rounds to
  have grid_mem : ∀ k : {k : ℤ // k ∈ IndexSet M},
      roundCoeff (mesh ε M : ℝ) (x.a k.1) ∈ coeffBox ε R M k.1 := by
    intro k
    have hk_ne : k.1 ≠ 0 := by
      unfold IndexSet at k
      exact (Finset.mem_erase.mp k.2).1
    exact rounded_in_box hε hR hM_ne hk_ne (coeff_bound_from_H1 hR hx_H1 k.1 hk_ne)

  let g : GridPoint ε R M :=
    fun k hk => ⟨roundCoeff (mesh ε M : ℝ) (x.a k), grid_mem ⟨k, hk⟩⟩

  -- Step 4: Prove g ∈ gridFinset
  have g_in_grid : g ∈ gridFinset ε R M := by
    classical
    refine Finset.mem_pi.mpr ?_
    intro k hk
    simp [coeffBoxSubtype, g]

  use g, g_in_grid

  -- Step 5: Define center from grid point (evaluation in proof layer)
  let c := gridToSeq ε R M g

  -- Step 6: Center equation (same as before)
  have center_eq : ∀ k (hk : k ∈ IndexSet M),
      c.a k = ⟨(mesh ε M : ℝ) * (roundCoeff (mesh ε M : ℝ) (x.a k)).1,
                (mesh ε M : ℝ) * (roundCoeff (mesh ε M : ℝ) (x.a k)).2⟩ := by
    intro k hk
    simp only [c, gridToSeq, dif_pos hk, g]

  -- Step 7: Centers vanish outside IndexSet M
  have center_zero : ∀ k, k ∉ IndexSet M → c.a k = 0 := by
    intro k hk
    simp [c, gridToSeq, dif_neg hk]

  -- Step 8: For ANY finite set F, bound the approximation error
  intro F

  -- Split F into inside (IndexSet M) and outside
  let F_in := F.filter (fun k => k ∈ IndexSet M)
  let F_out := F.filter (fun k => k ∉ IndexSet M)

  -- F partitions into F_in and F_out
  have partition_union :
      F_in ∪ F_out = F := by
    simpa [F_in, F_out] using
      (Finset.filter_union_filter_not F (fun k => k ∈ IndexSet M))
  have partition : F = F_in ∪ F_out := partition_union.symm

  have disj : Disjoint F_in F_out := by
    simpa [F_in, F_out] using
      (Finset.disjoint_filter_filter_not F (fun k => k ∈ IndexSet M))

  have sum_split :
      Finset.sum F (fun k => ‖x.a k - c.a k‖^2)
      = Finset.sum F_in (fun k => ‖x.a k - c.a k‖^2)
      + Finset.sum F_out (fun k => ‖x.a k - c.a k‖^2) := by
    rw [partition]
    exact Finset.sum_union disj

  -- INSIDE BOUND: Rounding error on F_in ≤ (ε/2)²
  have inside_bound : Finset.sum F_in (fun k => ‖x.a k - c.a k‖^2) ≤ ((ε : ℝ)/2)^2 := by
    -- F_in ⊆ IndexSet M, so bound by sum over entire IndexSet M
    calc Finset.sum F_in (fun k => ‖x.a k - c.a k‖^2)
        ≤ Finset.sum (IndexSet M) (fun k => ‖x.a k - c.a k‖^2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            simp [F_in, Finset.mem_filter] at hk
            exact hk.2
          · intro k _ _
            exact sq_nonneg _
      _ ≤ Finset.sum (IndexSet M) (fun k => 2 * ((mesh ε M : ℝ))^2) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [center_eq k hk]
          have err := round_error (mesh ε M : ℝ) (mesh_pos (by exact_mod_cast hε) hM_ne) (x.a k)
          calc ‖x.a k - ⟨(mesh ε M : ℝ) * (roundCoeff (mesh ε M : ℝ) (x.a k)).1,
                           (mesh ε M : ℝ) * (roundCoeff (mesh ε M : ℝ) (x.a k)).2⟩‖^2
              ≤ (Real.sqrt 2 * (mesh ε M : ℝ))^2 := by
                have h_nonneg := norm_nonneg (x.a k - ⟨(mesh ε M : ℝ) * (roundCoeff (mesh ε M : ℝ) (x.a k)).1, (mesh ε M : ℝ) * (roundCoeff (mesh ε M : ℝ) (x.a k)).2⟩)
                calc ‖x.a k - ⟨(mesh ε M : ℝ) * (roundCoeff (mesh ε M : ℝ) (x.a k)).1, (mesh ε M : ℝ) * (roundCoeff (mesh ε M : ℝ) (x.a k)).2⟩‖^2
                    = ‖x.a k - ⟨(mesh ε M : ℝ) * (roundCoeff (mesh ε M : ℝ) (x.a k)).1, (mesh ε M : ℝ) * (roundCoeff (mesh ε M : ℝ) (x.a k)).2⟩‖ * ‖x.a k - ⟨(mesh ε M : ℝ) * (roundCoeff (mesh ε M : ℝ) (x.a k)).1, (mesh ε M : ℝ) * (roundCoeff (mesh ε M : ℝ) (x.a k)).2⟩‖ := sq _
                  _ ≤ ‖x.a k - ⟨(mesh ε M : ℝ) * (roundCoeff (mesh ε M : ℝ) (x.a k)).1, (mesh ε M : ℝ) * (roundCoeff (mesh ε M : ℝ) (x.a k)).2⟩‖ * (Real.sqrt 2 * (mesh ε M : ℝ)) := by
                      apply mul_le_mul_of_nonneg_left err h_nonneg
                  _ ≤ (Real.sqrt 2 * (mesh ε M : ℝ)) * (Real.sqrt 2 * (mesh ε M : ℝ)) := by
                      apply mul_le_mul_of_nonneg_right err
                      apply mul_nonneg (Real.sqrt_nonneg _) (le_of_lt (mesh_pos (by exact_mod_cast hε) hM_ne))
                  _ = (Real.sqrt 2 * (mesh ε M : ℝ))^2 := (sq _).symm
            _ = 2 * ((mesh ε M : ℝ))^2 := by
                rw [mul_pow, Real.sq_sqrt (by norm_num)]
      _ = (IndexSet M).card * (2 * ((mesh ε M : ℝ))^2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (2 * M : ℝ) * (2 * ((mesh ε M : ℝ))^2) := by
          congr 1
          exact_mod_cast card_IndexSet M
      _ ≤ ((ε : ℝ) / 2)^2 := rounding_bound_mesh ε M hM_ne

  -- OUTSIDE BOUND: Tail error on F_out ≤ (ε/2)²
  have outside_bound : Finset.sum F_out (fun k => ‖x.a k - c.a k‖^2) ≤ ((ε : ℝ)/2)^2 := by
    -- Further split F_out into k=0 and tail (|k| > M, k ≠ 0)
    let F_zero := F_out.filter (fun k => k = 0)
    let F_tail := F_out.filter (fun k => k ≠ 0)

    have partition_out : F_out = F_zero ∪ F_tail := by
      ext k
      simp [F_zero, F_tail, Finset.mem_filter, Finset.mem_union]
      tauto

    have disj_out : Disjoint F_zero F_tail := by
      rw [Finset.disjoint_filter]
      intro k _ h1 h2
      exact h2 h1

    have sum_split_out :
        Finset.sum F_out (fun k => ‖x.a k - c.a k‖^2)
        = Finset.sum F_zero (fun k => ‖x.a k - c.a k‖^2)
        + Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2) := by
      rw [partition_out]
      exact Finset.sum_union disj_out

    -- Zero mode contributes 0
    have zero_contrib : Finset.sum F_zero (fun k => ‖x.a k - c.a k‖^2) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp [F_zero, Finset.mem_filter] at hk
      have : k = 0 := hk.2
      subst this
      have hx0 : x.a 0 = 0 := hx_mean
      have hc0 : c.a 0 = 0 := center_zero 0 (by simp [IndexSet])
      simp [hx0, hc0]

    -- Tail bound: apply tail_bound_finitary
    have tail_contrib : Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2) ≤ ((ε : ℝ)/2)^2 := by
      -- Centers vanish on tail, so error = ‖x.a k‖²
      have simplify : ∀ k ∈ F_tail, ‖x.a k - c.a k‖^2 = ‖x.a k‖^2 := by
        intro k hk
        simp [F_tail, F_out, Finset.mem_filter] at hk
        have : c.a k = 0 := center_zero k hk.1.2
        simp [this]

      calc Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2)
          = Finset.sum F_tail (fun k => ‖x.a k‖^2) := by
            apply Finset.sum_congr rfl simplify
        _ ≤ ((ε : ℝ) / 2)^2 := by
            -- F_tail consists of k with k ∉ IndexSet M and k ≠ 0
            -- IndexSet M = {k : -M ≤ k ≤ M, k ≠ 0}
            -- So k ∉ IndexSet M and k ≠ 0 means |k| > M
            have tail_pred : ∀ k ∈ F_tail, (M : ℝ) < |(k : ℝ)| := by
              intro k hk
              simp only [F_tail, F_out, Finset.mem_filter] at hk
              have hk_out : k ∉ IndexSet M := hk.1.2
              have hk_ne : k ≠ 0 := hk.2
              rw [not_mem_IndexSet_iff] at hk_out
              cases hk_out with
              | inl h0 => exact absurd h0 hk_ne
              | inr h =>
                cases h with
                | inl hlt => -- k < -(M : ℤ)
                  have : (k : ℝ) < -(M : ℝ) := by exact_mod_cast hlt
                  have : |(k : ℝ)| = -(k : ℝ) := abs_of_neg (by linarith : (k : ℝ) < 0)
                  linarith
                | inr hgt => -- (M : ℤ) < k
                  have h1 : (M : ℝ) < (k : ℝ) := by exact_mod_cast hgt
                  have h2 : 0 ≤ (k : ℝ) := le_of_lt (by linarith : 0 < (k : ℝ))
                  rw [abs_of_nonneg h2]
                  exact h1

            -- Convert to subtype sum
            -- Use tail_bound_finitary directly
            have subtype_bound : Finset.sum (F_tail.subtype (fun (k : ℤ) => (M : ℝ) < |(k : ℝ)|)) (fun k => ‖x.a k.val‖^2)
                ≤ (R : ℝ)^2 / ((2 * Real.pi * (M : ℝ))^2) := tail_bound_finitary M hR hx_H1 hM _

            calc Finset.sum F_tail (fun k => ‖x.a k‖^2)
              _ = Finset.sum (F_tail.filter (fun (k : ℤ) => (M : ℝ) < |(k : ℝ)|)) (fun k => ‖x.a k‖^2) := by
                  congr 1
                  ext k
                  simp only [Finset.mem_filter]
                  exact ⟨fun h => And.intro h (tail_pred k h), fun h => h.1⟩
              _ = Finset.sum (F_tail.subtype (fun (k : ℤ) => (M : ℝ) < |(k : ℝ)|)) (fun k => ‖x.a k.val‖^2) := by
                  classical
                  exact sum_filter_toSubtype F_tail (fun k => (M : ℝ) < |(k : ℝ)|) (fun k => ‖x.a k‖^2)
              _ ≤ (R : ℝ)^2 / ((2 * Real.pi * (M : ℝ))^2) := subtype_bound
              _ ≤ ((ε : ℝ) / 2)^2 := tail_bound_M_of hε hR

    calc Finset.sum F_out (fun k => ‖x.a k - c.a k‖^2)
        = Finset.sum F_zero (fun k => ‖x.a k - c.a k‖^2)
        + Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2) := sum_split_out
      _ = 0 + Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2) := by rw [zero_contrib]
      _ ≤ ((ε : ℝ) / 2)^2 := by linarith [tail_contrib]

  -- COMBINE: inside + outside ≤ (ε/2)² + (ε/2)² < ε²
  calc Finset.sum F (fun k => ‖x.a k - c.a k‖^2)
      = Finset.sum F_in (fun k => ‖x.a k - c.a k‖^2)
      + Finset.sum F_out (fun k => ‖x.a k - c.a k‖^2) := sum_split
    _ ≤ ((ε : ℝ) / 2)^2 + ((ε : ℝ) / 2)^2 := by linarith [inside_bound, outside_bound]
    _ = (ε : ℝ)^2 / 2 := by ring
    _ < (ε : ℝ)^2 := by linarith [sq_pos_of_pos hε]

/-- **PRIMARY CONSTRUCTIVE THEOREM** - Witness is grid data (fully extractable).

    The witness `G : Finset (GridPoint ε R (M_of ε R))` contains only ℚ, ℤ, Finset data.
    Evaluation to ℓ2Z via `gridToSeq` happens in the proof, not the witness. -/
theorem totallyBounded_data (ε R : ℚ) (hε : 0 < (ε : ℝ)) (hR : 0 < (R : ℝ)) :
    ∃ (G : Finset (GridPoint ε R (M_of ε R))),
      ∀ (x : ℓ2Z), x.meanZero → x.InH1Ball (R : ℝ) →
        ∃ g ∈ G, ∀ F : Finset ℤ,
          Finset.sum F (fun k => ‖x.a k - (gridToSeq ε R (M_of ε R) g).a k‖^2) < (ε : ℝ)^2 := by
  classical
  refine ⟨gridFinset ε R (M_of ε R), ?_⟩
  intro x hx_mean hx_H1
  simpa using gridFinset_sound ε R hε hR x hx_mean hx_H1

/-- **COROLLARY**: ℓ2Z centers version (derived from data-level theorem).

    This is a convenience wrapper. The primary constructive content is in
    `totallyBounded_data` which returns grid data, not ℓ2Z sequences. -/
theorem totallyBounded (ε R : ℚ) (hε : 0 < (ε : ℝ)) (hR : 0 < (R : ℝ)) :
    ∃ (centers : Finset ℓ2Z),
      ∀ (x : ℓ2Z), x.meanZero → x.InH1Ball (R : ℝ) →
        ∃ c ∈ centers, ∀ (F : Finset ℤ),
          Finset.sum F (fun k => ‖x.a k - c.a k‖^2) < (ε : ℝ)^2 := by
  classical  -- OK here, this is a derived convenience lemma
  obtain ⟨G, hG⟩ := totallyBounded_data ε R hε hR
  let M := M_of ε R
  use G.image (gridToSeq ε R M)
  intro x hx_mean hx_H1
  obtain ⟨g, g_in, hg⟩ := hG x hx_mean hx_H1
  use gridToSeq ε R M g
  constructor
  · exact Finset.mem_image.mpr ⟨g, g_in, rfl⟩
  · exact hg

end ℓ2Z

/-- **SOUNDNESS**: The package provides valid ε-approximation.

    Note: This is definitionally equal to `totallyBounded_data P.ε P.R hε hR`
    since P.M = M_of P.ε P.R, P.grid = gridFinset P.ε P.R P.M, and
    P.eval = gridToSeq P.ε P.R P.M by definition. The `sorry` here is purely
    a formalization detail about Lean's definitional equality checking. -/
theorem ℓ2Z.WitnessPkg.sound (P : ℓ2Z.WitnessPkg) (hε : 0 < (P.ε : ℝ)) (hR : 0 < (P.R : ℝ)) :
    ∀ x : ℓ2Z, x.meanZero → x.InH1Ball (P.R : ℝ) →
      ∃ g ∈ P.grid, ∀ F : Finset ℤ,
        Finset.sum F (fun k => ‖x.a k - (P.eval g).a k‖^2) < (P.ε : ℝ)^2 := by
  classical
  have := gridFinset_sound P.ε P.R hε hR
  simpa [WitnessPkg.M, WitnessPkg.grid, WitnessPkg.eval] using this

end RellichKondrachov1D.Seq
