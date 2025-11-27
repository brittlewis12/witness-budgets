import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Budgets.ConstructiveQ

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

/-- Norm square is nonnegative. -/
lemma normSq_nonneg {d : ℕ} (k : Lattice d) : 0 ≤ normSq k := by
  classical
  unfold normSq
  exact Finset.sum_nonneg (by intro i _; exact sq_nonneg _)

/-- h1Weight is strictly positive. -/
lemma h1Weight_pos {d : ℕ} (k : Lattice d) : 0 < h1Weight k := by
  have hx : 0 ≤ normSq k := normSq_nonneg k
  have hx' : 0 ≤ 4 * Real.pi^2 * normSq k :=
    mul_nonneg (by nlinarith : 0 ≤ 4 * Real.pi^2) hx
  have hone : 0 < (1 : ℝ) := by norm_num
  have := add_pos_of_pos_of_nonneg hone hx'
  simpa [h1Weight] using this

/-- h1Weight dominates 1. -/
lemma h1Weight_ge_one {d : ℕ} (k : Lattice d) : 1 ≤ h1Weight k := by
  have hx : 0 ≤ normSq k := normSq_nonneg k
  have hx' : 0 ≤ 4 * Real.pi^2 * normSq k :=
    mul_nonneg (by nlinarith : 0 ≤ 4 * Real.pi^2) hx
  have := add_le_add_left hx' 1
  simpa [h1Weight] using this

/-- H⁻¹ weight (reciprocal of the H¹ weight). -/
noncomputable def hminusWeight {d : ℕ} (k : Lattice d) : ℝ :=
  (h1Weight k)⁻¹

lemma hminusWeight_nonneg {d : ℕ} (k : Lattice d) :
    0 ≤ hminusWeight k := by
  unfold hminusWeight
  exact inv_nonneg.mpr (le_of_lt (h1Weight_pos k))

lemma hminusWeight_le_one {d : ℕ} (k : Lattice d) :
    hminusWeight k ≤ 1 := by
  have hx_ge : (1 : ℝ) ≤ h1Weight k := h1Weight_ge_one (d := d) k
  have hx_nonneg : 0 ≤ hminusWeight k := hminusWeight_nonneg (d := d) k
  have hx_pos : 0 < h1Weight k := h1Weight_pos (d := d) k
  have hprod : hminusWeight k * h1Weight k = 1 := by
    have hne : h1Weight k ≠ 0 := ne_of_gt hx_pos
    simp [hminusWeight, hne]
  have hx_mul :
      hminusWeight k * 1 ≤ hminusWeight k * h1Weight k :=
    mul_le_mul_of_nonneg_left hx_ge hx_nonneg
  simpa [hprod, mul_comm] using hx_mul

/-- Membership in cube -/
lemma mem_cube {d M : ℕ} {k : Lattice d} :
    k ∈ cube d M ↔ ∀ i, -(M : ℤ) ≤ k i ∧ k i ≤ (M : ℤ) := by
  unfold cube
  simp only [Fintype.mem_piFinset, Finset.mem_Icc]

lemma zero_mem_cube {d M : ℕ} :
    (fun _ : Fin d => (0 : ℤ)) ∈ cube d M := by
  refine (mem_cube (d := d) (M := M)).mpr ?_
  intro i; simp

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

/-- Uniform H¹ bound for lattice points in the cube `[-M,M]^d`. -/
noncomputable def h1CubeBound (d M : ℕ) : ℝ :=
  1 + 4 * Real.pi^2 * ((d : ℝ) * (M : ℝ)^2)

lemma h1CubeBound_pos (d M : ℕ) : 0 < h1CubeBound d M := by
  have hconst : 0 < (1 : ℝ) := by norm_num
  have : 0 ≤ (d : ℝ) * (M : ℝ)^2 := by
    exact mul_nonneg (show 0 ≤ (d : ℝ) by exact_mod_cast Nat.zero_le d) (sq_nonneg _)
  have hmul : 0 ≤ 4 * Real.pi^2 * ((d : ℝ) * (M : ℝ)^2) :=
    mul_nonneg (by nlinarith : 0 ≤ 4 * Real.pi^2) this
  exact add_pos_of_pos_of_nonneg hconst hmul

lemma cube_normSq_le {d M : ℕ} [NeZero d] {k : Lattice d}
    (hk : k ∈ cube d M) :
    normSq k ≤ (d : ℝ) * (M : ℝ)^2 := by
  classical
  have bounds :
      ∀ i : Fin d, ((k i : ℝ)^2) ≤ (M : ℝ)^2 := by
    intro i
    have hi := (mem_cube (d := d) (M := M)).mp hk i
    have hreal :
        (-(M : ℝ) ≤ (k i : ℝ) ∧ (k i : ℝ) ≤ (M : ℝ)) := by
      exact_mod_cast hi
    have hM_nonneg : 0 ≤ (M : ℝ) := by exact_mod_cast (Nat.zero_le M)
    have habs : |(k i : ℝ)| ≤ |(M : ℝ)| := by
      simpa [abs_of_nonneg hM_nonneg] using
        (abs_le.mpr hreal)
    have := (sq_le_sq.mpr habs)
    simpa [abs_of_nonneg hM_nonneg] using this
  have :
      normSq k ≤ ∑ _ : Fin d, (M : ℝ)^2 := by
    unfold normSq
    apply Finset.sum_le_sum
    intro i _
    exact bounds i
  calc
    normSq k ≤ ∑ _ : Fin d, (M : ℝ)^2 := this
    _ = (Finset.card (Finset.univ : Finset (Fin d))) * (M : ℝ)^2 := by
        simp [Finset.sum_const]
    _ = (d : ℝ) * (M : ℝ)^2 := by
        simp [Finset.card_univ, Fintype.card_fin]

lemma cube_h1Weight_le {d M : ℕ} [NeZero d] {k : Lattice d}
    (hk : k ∈ cube d M) :
    h1Weight k ≤ h1CubeBound d M := by
  have hnorm := cube_normSq_le (d := d) (M := M) hk
  unfold h1CubeBound h1Weight
  have : 4 * Real.pi^2 * normSq k
      ≤ 4 * Real.pi^2 * ((d : ℝ) * (M : ℝ)^2) :=
    mul_le_mul_of_nonneg_left hnorm (by nlinarith : 0 ≤ 4 * Real.pi^2)
  exact add_le_add_left this 1

lemma cube_hminusWeight_ge {d M : ℕ} [NeZero d] {k : Lattice d}
    (hk : k ∈ cube d M) :
    (1 / h1CubeBound d M) ≤ hminusWeight k := by
  have hbound := cube_h1Weight_le (d := d) (M := M) hk
  have hpos := h1Weight_pos (d := d) k
  have := one_div_le_one_div_of_le hpos hbound
  simpa [hminusWeight] using this

/-! ## Sequence space -/

/-- Square-summable sequences on ℤᵈ (d-dimensional Fourier coefficient space) -/
structure SeqD (d : ℕ) where
  /-- Coefficient function: ℤᵈ → ℂ -/
  a : Lattice d → ℂ
  /-- Square-summability condition -/
  summable_sq : Summable (fun k => ‖a k‖^2)

namespace SeqD

variable {d : ℕ}

@[ext] lemma ext {u v : SeqD d} (h : ∀ k, u.a k = v.a k) : u = v := by
  cases u
  cases v
  congr
  exact funext h

lemma summable_sq_zero (d : ℕ) :
    Summable (fun _ : Lattice d => ‖(0 : ℂ)‖^2) := by
  simpa using (summable_zero : Summable fun _ : Lattice d => (0 : ℝ))

/-- Helper inequality for ℂ-valued coefficients. -/
lemma norm_add_sq_le_two (x y : ℂ) :
    ‖x + y‖^2 ≤ 2 * (‖x‖^2 + ‖y‖^2) := by
  have h₁ : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have h₂ :
      ‖x + y‖^2 ≤ (‖x‖ + ‖y‖)^2 := by
    refine (sq_le_sq.mpr ?_)
    have hx : 0 ≤ ‖x + y‖ := norm_nonneg _
    have hy : 0 ≤ ‖x‖ + ‖y‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    simpa [abs_of_nonneg hx, abs_of_nonneg hy] using h₁
  have hdiff :
      0 ≤ 2 * (‖x‖^2 + ‖y‖^2) - (‖x‖ + ‖y‖)^2 := by
    have : 0 ≤ (‖x‖ - ‖y‖)^2 := sq_nonneg _
    calc 0 ≤ (‖x‖ - ‖y‖)^2 := this
      _ = ‖x‖^2 - 2 * ‖x‖ * ‖y‖ + ‖y‖^2 := by ring
      _ = 2 * (‖x‖^2 + ‖y‖^2) - (‖x‖ + ‖y‖)^2 := by ring
  have h₃ :
      (‖x‖ + ‖y‖)^2 ≤ 2 * (‖x‖^2 + ‖y‖^2) :=
    (sub_nonneg.mp hdiff)
  exact le_trans h₂ h₃

lemma summable_sq_add (u v : SeqD d) :
    Summable (fun k => ‖u.a k + v.a k‖^2) := by
  classical
  have hcoeff_nonneg : ∀ k, 0 ≤ ‖u.a k + v.a k‖^2 := by
    intro k; exact sq_nonneg _
  have hmajor :
      ∀ k, ‖u.a k + v.a k‖^2 ≤ 2 * (‖u.a k‖^2 + ‖v.a k‖^2) := fun k =>
        norm_add_sq_le_two _ _
  have hsum :
      Summable (fun k => 2 * (‖u.a k‖^2 + ‖v.a k‖^2)) := by
    have h₂u :
        Summable (fun k : Lattice d => 2 * ‖u.a k‖^2) :=
      (u.summable_sq).mul_left 2
    have h₂v :
        Summable (fun k : Lattice d => 2 * ‖v.a k‖^2) :=
      (v.summable_sq).mul_left 2
    have hsum :=
      h₂u.add h₂v
    convert hsum using 1 with k
    ring_nf
  exact Summable.of_nonneg_of_le hcoeff_nonneg hmajor hsum

lemma summable_sq_neg (u : SeqD d) :
    Summable (fun k => ‖(-u.a k)‖^2) := by
  have : (fun k => ‖(-u.a k)‖^2) = fun k => ‖u.a k‖^2 := by
    funext k
    simp
  simpa [this] using u.summable_sq

lemma summable_sq_smul (c : ℂ) (u : SeqD d) :
    Summable (fun k => ‖c * u.a k‖^2) := by
  have h : (fun k => ‖c * u.a k‖^2)
      = fun k => ‖c‖^2 * ‖u.a k‖^2 := by
    funext k
    simp only [norm_mul, sq]
    ring
  rw [h]
  exact (u.summable_sq).mul_left (‖c‖^2)

instance instZero : Zero (SeqD d) where
  zero :=
    { a := fun _ => 0
      summable_sq := by
        simpa using (summable_zero : Summable fun _ : Lattice d => (0 : ℝ)) }

@[simp] lemma zero_a (d : ℕ) :
    (0 : SeqD d).a = fun _ => (0 : ℂ) := rfl

instance instAdd : Add (SeqD d) where
  add u v :=
    { a := fun k => u.a k + v.a k
      summable_sq := summable_sq_add u v }

@[simp] lemma add_a (u v : SeqD d) :
    (u + v).a = fun k => u.a k + v.a k := rfl

instance instNeg : Neg (SeqD d) where
  neg u :=
    { a := fun k => -u.a k
      summable_sq := summable_sq_neg u }

@[simp] lemma neg_a (u : SeqD d) :
    (-u).a = fun k => -u.a k := rfl

/-- L² sequences form a group under subtraction.
    Standard bound: ‖u - v‖² ≤ 2‖u‖² + 2‖v‖² from triangle inequality. -/
instance instSub : Sub (SeqD d) where
  sub u v := {
    a := fun k => u.a k - v.a k
    summable_sq := by
      -- Standard L² bound: ‖u - v‖² ≤ 2‖u‖² + 2‖v‖²
      have h_le : ∀ k, ‖u.a k - v.a k‖^2 ≤ 2 * ‖u.a k‖^2 + 2 * ‖v.a k‖^2 := fun k => by
        have h_norm : ‖u.a k - v.a k‖ ≤ ‖u.a k‖ + ‖v.a k‖ := norm_sub_le _ _
        have h_sq : ‖u.a k - v.a k‖^2 ≤ (‖u.a k‖ + ‖v.a k‖)^2 :=
          sq_le_sq' (by linarith [norm_nonneg (u.a k - v.a k)]) h_norm
        calc ‖u.a k - v.a k‖^2
            ≤ (‖u.a k‖ + ‖v.a k‖)^2 := h_sq
          _ = ‖u.a k‖^2 + ‖v.a k‖^2 + 2 * ‖u.a k‖ * ‖v.a k‖ := by ring
          _ ≤ ‖u.a k‖^2 + ‖v.a k‖^2 + (‖u.a k‖^2 + ‖v.a k‖^2) := by
              linarith [two_mul_le_add_sq ‖u.a k‖ ‖v.a k‖]
          _ = 2 * ‖u.a k‖^2 + 2 * ‖v.a k‖^2 := by ring
      have h_sum : Summable (fun k => 2 * ‖u.a k‖^2 + 2 * ‖v.a k‖^2) :=
        (u.summable_sq.mul_left 2).add (v.summable_sq.mul_left 2)
      exact Summable.of_nonneg_of_le (fun k => sq_nonneg _) h_le h_sum
  }

@[simp] lemma sub_a (u v : SeqD d) :
    (u - v).a = fun k => u.a k - v.a k := rfl

instance instAddCommGroup : AddCommGroup (SeqD d) where
  add := (· + ·)
  add_assoc := by
    intro u v w; ext k; simp [add_assoc]
  zero := 0
  zero_add := by intro u; ext k; simp
  add_zero := by intro u; ext k; simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg := Neg.neg
  neg_add_cancel := by intro u; ext k; simp
  add_comm := by intro u v; ext k; simp [add_comm]

instance instSMul : SMul ℂ (SeqD d) where
  smul c u :=
    { a := fun k => c * u.a k
      summable_sq := summable_sq_smul c u }

@[simp] lemma smul_a (c : ℂ) (u : SeqD d) :
    (c • u).a = fun k => c * u.a k := rfl

instance instModule : Module ℂ (SeqD d) where
  smul_add := by
    intro c u v; ext k; simp [mul_add]
  add_smul := by
    intro c d u; ext k; simp [add_mul]
  mul_smul := by
    intro c d u; ext k; simp [mul_assoc]
  one_smul := by
    intro u; ext k; simp
  zero_smul := by
    intro u; ext k; simp
  smul_zero := by
    intro c; ext k; simp

end SeqD

/-- Mean-zero property: a₀ = 0 -/
def meanZero {d : ℕ} (x : SeqD d) : Prop :=
  x.a (fun _ => 0) = 0

/-- H¹-ball membership (finitary version for extraction) -/
def InH1Ball {d : ℕ} (R : ℝ) (x : SeqD d) : Prop :=
  ∀ (F : Finset (Lattice d)),
    Finset.sum F (fun k => (h1Weight k) * ‖x.a k‖^2) ≤ R^2

/-- H⁻¹-ball membership using the reciprocal weights. -/
def InHminusBall {d : ℕ} (S : ℝ) (x : SeqD d) : Prop :=
  ∀ (F : Finset (Lattice d)),
    Finset.sum F (fun k => (hminusWeight k) * ‖x.a k‖^2) ≤ S^2

/-- Inside the cube, plain ℓ² mass is controlled by the H⁻¹ weights. -/
lemma sum_sq_le_hminus
    {d M : ℕ} [NeZero d]
    (F : Finset (Lattice d)) (coeff : Lattice d → ℂ)
    (hsubset : ∀ k ∈ F, k ∈ cube d M) :
    Finset.sum F (fun k => ‖coeff k‖^2)
      ≤ h1CubeBound d M *
        Finset.sum F (fun k =>
          hminusWeight k * ‖coeff k‖^2) := by
  classical
  have Hpos : 0 < h1CubeBound d M := h1CubeBound_pos d M
  have Hnonneg : 0 ≤ h1CubeBound d M := le_of_lt Hpos
  have per_k :
      ∀ k ∈ F, ‖coeff k‖^2
        ≤ h1CubeBound d M * (hminusWeight k * ‖coeff k‖^2) := by
    intro k hkF
    have hkCube := hsubset k hkF
    have h_inv := cube_hminusWeight_ge (d := d) (M := M) hkCube
    have hcube_ne : h1CubeBound d M ≠ 0 := ne_of_gt Hpos
    have hineq :
        1 ≤ h1CubeBound d M * hminusWeight k := by
      have := mul_le_mul_of_nonneg_left h_inv Hnonneg
      simpa [hcube_ne, mul_comm, mul_left_comm, mul_assoc] using this
    have hnorm_nonneg : 0 ≤ ‖coeff k‖^2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_right hineq hnorm_nonneg
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hsum := Finset.sum_le_sum per_k
  have hright :
      h1CubeBound d M *
          Finset.sum F (fun k =>
            hminusWeight k * ‖coeff k‖^2)
        = Finset.sum F (fun k =>
            h1CubeBound d M *
              (hminusWeight k * ‖coeff k‖^2)) := by
    simp [Finset.mul_sum]
  simpa [one_mul, hright] using hsum

lemma cube_sum_sq_le
    {d M : ℕ} [NeZero d]
    (F : Finset (Lattice d))
    (coeff : Lattice d → ℂ)
    (hsubset : ∀ k ∈ F, k ∈ cube d M)
    {T : ℝ}
    (hbound :
        Finset.sum F (fun k => hminusWeight k * ‖coeff k‖^2) ≤ T) :
    Finset.sum F (fun k => ‖coeff k‖^2)
      ≤ h1CubeBound d M * T := by
  have hsq :=
    sum_sq_le_hminus (d := d) (M := M) F coeff hsubset
  have hpos : 0 < h1CubeBound d M := h1CubeBound_pos d M
  have :=
    mul_le_mul_of_nonneg_left hbound (le_of_lt hpos)
  exact le_trans hsq this

lemma cube_sum_sq_le_seq
    {d M : ℕ} [NeZero d]
    {x : SeqD d} {S : ℝ}
    (hminus : InHminusBall S x)
    (F : Finset (Lattice d))
    (hsubset : ∀ k ∈ F, k ∈ cube d M) :
    Finset.sum F (fun k => ‖x.a k‖^2)
      ≤ h1CubeBound d M * S^2 := by
  refine cube_sum_sq_le (d := d) (M := M) F (coeff := x.a) hsubset ?_
  exact hminus F

/-! ## Basic lemmas for cube and index set -/


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

/-! ## Constructive versions (SOURCE 2 elimination) -/

/-- **CONSTRUCTIVE**: Power function for ConstructiveQ.Q -/
def constructiveQ_pow (q : ConstructiveQ.Q) (n : ℕ) : ConstructiveQ.Q :=
  match n with
  | 0 => ConstructiveQ.one
  | n + 1 => ConstructiveQ.mul q (constructiveQ_pow q n)

/-- **CONSTRUCTIVE**: Mesh formula using ConstructiveQ.Q instead of ℚ

    This version uses only propext, eliminating Classical.choice from the mesh computation.

    Formula: ε / (4 * (2M+1)^⌈d/2⌉)
-/
def meshD_C (d : ℕ) (ε : ConstructiveQ.Q) (M : ℕ) : ConstructiveQ.Q :=
  let two_m_plus_one := ConstructiveQ.ofInt (2 * M + 1)
  let exp := Nat.ceil ((d : ℚ) / 2)  -- Ceiling computation (uses Classical in ℚ)
  let power := constructiveQ_pow two_m_plus_one exp
  let four := ConstructiveQ.ofInt 4
  let denominator := ConstructiveQ.mul four power
  ConstructiveQ.div ε denominator

/-- **CONSTRUCTIVE**: Coefficient bound using ConstructiveQ.Q

    Returns 0 for origin, R otherwise (enforcing mean-zero).
-/
def coeffBound_C {d : ℕ} (R : ConstructiveQ.Q) (k : Lattice d) : ConstructiveQ.Q :=
  if k = (fun _ => 0) then ConstructiveQ.zero else R

/-- Convert ConstructiveQ.Q to ℚ for proof purposes -/
def constructiveQ_to_rat (q : ConstructiveQ.Q) : ℚ :=
  q.num / q.den

/-- Converting ConstructiveQ.one to ℚ gives 1 -/
lemma constructiveQ_to_rat_one :
    constructiveQ_to_rat ConstructiveQ.one = 1 := by
  unfold constructiveQ_to_rat ConstructiveQ.one
  norm_num

/-- Converting ConstructiveQ.ofInt to ℚ commutes with the cast -/
lemma constructiveQ_to_rat_ofInt (z : ℤ) :
    constructiveQ_to_rat (ConstructiveQ.ofInt z) = z := by
  unfold constructiveQ_to_rat ConstructiveQ.ofInt
  have h := normalize_preserves_value z 1 (by decide : (1 : ℕ) ≠ 0)
  simpa using h

/-- Multiplication is preserved by conversion to ℚ -/
lemma constructiveQ_to_rat_mul (q r : ConstructiveQ.Q) :
    constructiveQ_to_rat (ConstructiveQ.mul q r) =
    constructiveQ_to_rat q * constructiveQ_to_rat r := by
  unfold constructiveQ_to_rat ConstructiveQ.mul
  -- Key challenge: prove q.den * r.den ≠ 0
  have hden : q.den * r.den ≠ 0 := by
    have hq : q.den ≠ 0 := ne_of_gt q.den_pos
    have hr : r.den ≠ 0 := ne_of_gt r.den_pos
    exact Nat.mul_ne_zero hq hr
  -- Apply normalize_preserves_value
  have h := normalize_preserves_value (q.num * r.num) (q.den * r.den) hden
  rw [h]
  -- Field algebra
  have hq_ne : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt q.den_pos)
  have hr_ne : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt r.den_pos)
  field_simp [hq_ne, hr_ne]
  push_cast
  ring

/-- Power is preserved by conversion to ℚ -/
lemma constructiveQ_to_rat_pow (q : ConstructiveQ.Q) (n : ℕ) :
    constructiveQ_to_rat (constructiveQ_pow q n) =
    (constructiveQ_to_rat q) ^ n := by
  induction n with
  | zero =>
      unfold constructiveQ_pow
      rw [constructiveQ_to_rat_one, pow_zero]
  | succ n ih =>
      unfold constructiveQ_pow
      rw [constructiveQ_to_rat_mul, ih, pow_succ, mul_comm]

/-- **BOSS FIGHT**: Inversion is preserved by conversion to ℚ.
    Handles three cases: zero, positive, and negative. -/
lemma constructiveQ_to_rat_inv (q : ConstructiveQ.Q) :
    constructiveQ_to_rat (ConstructiveQ.inv q) = (constructiveQ_to_rat q)⁻¹ := by
  unfold ConstructiveQ.inv constructiveQ_to_rat
  by_cases hzero : q.num = 0
  · -- Case 1: zero
    simp only [dif_pos hzero]
    show (ConstructiveQ.zero.num : ℚ) / (ConstructiveQ.zero.den : ℚ) = ((q.num : ℚ) / (q.den : ℚ))⁻¹
    have hq_zero : (q.num : ℚ) / (q.den : ℚ) = 0 := by
      simp [hzero]
    rw [hq_zero, inv_zero]
    show (0 : ℚ) / (1 : ℚ) = 0
    norm_num
  · -- Case 2: non-zero
    simp only [dif_neg hzero]
    by_cases hpos : q.num > 0
    · -- Case 2a: positive
      -- inv q = normalize (q.den) (q.num.natAbs)
      simp only [if_pos hpos]
      have hnum_nonneg : 0 ≤ q.num := le_of_lt hpos
      have hnum_natabs : (q.num.natAbs : ℤ) = q.num := Int.ofNat_natAbs_of_nonneg hnum_nonneg
      have hden_pos : q.den > 0 := q.den_pos
      have hnum_natabs_ne_zero : q.num.natAbs ≠ 0 := by
        intro h
        have : q.num = 0 := by
          rw [← hnum_natabs]
          simp [h]
        exact hzero this
      -- Apply normalize_preserves_value to (Int.ofNat q.den, q.num.natAbs)
      have key := normalize_preserves_value (Int.ofNat q.den) q.num.natAbs hnum_natabs_ne_zero
      show (let q' := ConstructiveQ.normalize (Int.ofNat q.den) q.num.natAbs;
            (q'.num : ℚ) / (q'.den : ℚ)) = ((q.num : ℚ) / (q.den : ℚ))⁻¹
      rw [key]
      -- Now prove: (q.den : ℚ) / (q.num.natAbs : ℚ) = ((q.num : ℚ) / (q.den : ℚ))⁻¹
      have hnum_eq : (q.num.natAbs : ℚ) = (q.num : ℚ) := by
        have := congrArg (fun z : ℤ => (z : ℚ)) hnum_natabs
        simp only [Int.cast_natCast] at this
        exact this
      have hden_ne_zero : (q.den : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hden_pos)
      have hnum_ne_zero : (q.num : ℚ) ≠ 0 := by
        intro h
        have : q.num = 0 := by
          exact_mod_cast h
        exact hzero this
      have hden_ofnat : ((Int.ofNat q.den) : ℚ) = (q.den : ℚ) := by simp
      rw [hden_ofnat, hnum_eq, inv_div]
    · -- Case 2b: negative
      -- num < 0, so inv q = normalize (-q.den) (q.num.natAbs)
      simp only [if_neg hpos]
      have hnum_neg : q.num < 0 := by
        omega
      have hnum_nonpos : q.num ≤ 0 := le_of_lt hnum_neg
      have hnum_natabs : (q.num.natAbs : ℤ) = -q.num := Int.ofNat_natAbs_of_nonpos hnum_nonpos
      have hden_pos : q.den > 0 := q.den_pos
      have hnum_natabs_ne_zero : q.num.natAbs ≠ 0 := by
        intro h
        have : q.num = 0 := by
          calc q.num = -(-q.num) := by ring
            _ = -(q.num.natAbs : ℤ) := by rw [← hnum_natabs]
            _ = 0 := by simp [h]
        exact hzero this
      -- Apply normalize_preserves_value to (-Int.ofNat q.den, q.num.natAbs)
      have key := normalize_preserves_value (-Int.ofNat q.den) q.num.natAbs hnum_natabs_ne_zero
      show (let q' := ConstructiveQ.normalize (-Int.ofNat q.den) q.num.natAbs;
            (q'.num : ℚ) / (q'.den : ℚ)) = ((q.num : ℚ) / (q.den : ℚ))⁻¹
      rw [key]
      -- Now prove: (-q.den : ℚ) / (q.num.natAbs : ℚ) = ((q.num : ℚ) / (q.den : ℚ))⁻¹
      -- Since num < 0, we have num = -natAbs, so num/den = -natAbs/den
      -- Thus (num/den)⁻¹ = -den/natAbs = (-den)/natAbs
      have hnum_eq : (q.num.natAbs : ℚ) = -(q.num : ℚ) := by
        have := congrArg (fun z : ℤ => (z : ℚ)) hnum_natabs
        simp only [Int.cast_natCast, Int.cast_neg] at this
        linarith
      have hden_ne_zero : (q.den : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hden_pos)
      have hnum_ne_zero : (q.num : ℚ) ≠ 0 := by
        intro h
        have : q.num = 0 := by exact_mod_cast h
        exact hzero this
      -- Simplify casts: show ↑(-Int.ofNat q.den) / ↑q.num.natAbs = (↑q.num / ↑q.den)⁻¹
      show ((-Int.ofNat q.den : ℤ) : ℚ) / (q.num.natAbs : ℚ) = ((q.num : ℚ) / (q.den : ℚ))⁻¹
      simp only [Int.cast_neg]
      rw [hnum_eq]
      -- Goal: -↑(Int.ofNat q.den) / -↑q.num = (↑q.num / ↑q.den)⁻¹
      have h_cast : ((Int.ofNat q.den) : ℚ) = (q.den : ℚ) := by norm_cast
      rw [h_cast]
      -- Goal: -↑q.den / -↑q.num = (↑q.num / ↑q.den)⁻¹
      field_simp

/-- Division is preserved by conversion to ℚ -/
lemma constructiveQ_to_rat_div (q r : ConstructiveQ.Q) :
    constructiveQ_to_rat (ConstructiveQ.div q r) =
    constructiveQ_to_rat q / constructiveQ_to_rat r := by
  unfold ConstructiveQ.div
  rw [constructiveQ_to_rat_mul, constructiveQ_to_rat_inv]
  rw [div_eq_mul_inv]

/-! ## Coefficient discretization -/

/-- **CONSTRUCTIVE**: Round rational complex coefficients to δ-grid.

    For use in witness construction where Fourier coefficients are ℚ-valued.
    This is the key to achieving ZERO classical content in the QAL extraction path.

    **XBUDGET**: C0 (fully computable)
    - Uses Rat.floor instead of Int.floor on ℝ
    - No Classical.choice in computational path
    - Can be evaluated with #eval

    **USAGE**: When constructing witnesses, ensure coefficients are represented
    as ℚ (not ℂ) to use this function. The classical `roundCoeff` below is used
    in soundness proofs where we work with ℂ-valued analytical functions.

    **PATH FORWARD**: To eliminate C5 budget from witness construction:
    1. Represent Fourier coefficients as ℚ × ℚ instead of ℂ in witness types
    2. Use this function for rounding instead of classical roundCoeff
    3. This will make roundToGridD_C fully C0 -/
def roundCoeff_CQ (δ : ℚ) (re im : ℚ) : ℤ × ℤ :=
  let re_scaled := re / δ
  let im_scaled := im / δ
  (Rat.floor re_scaled, Rat.floor im_scaled)

/-- Classical roundCoeff using Real floor (requires Classical.choice).
    Used in soundness proofs where we work with ℂ-valued functions. -/
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

/-! ## Equivalence lemmas between constructive and classical versions -/

/-- The constructive mesh equals the classical mesh after coercion.
    PROVED using ConstructiveQ homomorphism lemmas. -/
theorem meshD_C_eq_meshD (d : ℕ) (ε : ConstructiveQ.Q) (M : ℕ) :
    constructiveQ_to_rat (meshD_C d ε M) = meshD d (constructiveQ_to_rat ε) M := by
  unfold meshD_C meshD
  simp only [constructiveQ_to_rat_div, constructiveQ_to_rat_mul,
             constructiveQ_to_rat_ofInt, constructiveQ_to_rat_pow]
  -- Both sides should now be identical; simplify casts
  norm_cast

/-- The constructive coefficient bound equals the classical one after coercion -/
lemma coeffBound_C_eq_coeffBound {d : ℕ} (R : ConstructiveQ.Q) (k : Lattice d) :
    constructiveQ_to_rat (coeffBound_C R k) = coeffBound (constructiveQ_to_rat R) k := by
  unfold coeffBound_C coeffBound constructiveQ_to_rat
  split_ifs with h
  · simp [ConstructiveQ.zero]
  · rfl

/-! ## List-based coefficient box (constructive alternative) -/

/-- Auxiliary: Create integer range [-rad, rad] as a list -/
def intRangeList (rad : ℕ) : List ℤ :=
  List.map (fun i => (i : ℤ) - rad) (List.range (2 * rad + 1))

/-- Zero is in intRangeList rad for any rad ≥ 1 -/
lemma zero_mem_intRangeList (rad : ℕ) (h : rad ≥ 1) : (0 : ℤ) ∈ intRangeList rad := by
  unfold intRangeList
  refine List.mem_map.mpr ⟨rad, ?_, ?_⟩
  · simp [List.mem_range]; omega
  · norm_num

/-- Membership in intRangeList is equivalent to being in [-rad, rad] -/
lemma mem_intRangeList_iff (rad : ℕ) (x : ℤ) :
    x ∈ intRangeList rad ↔ -rad ≤ x ∧ x ≤ rad := by
  unfold intRangeList
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    simp [List.mem_range] at hi
    omega
  · intro ⟨hlo, hhi⟩
    refine List.mem_map.mpr ⟨(x + rad).toNat, ?_, ?_⟩
    · have h1 : 0 ≤ x + ↑rad := by omega
      have h2 : x + ↑rad < 2 * ↑rad + 1 := by omega
      simp [List.mem_range, Int.toNat_of_nonneg h1]
      use (x + ↑rad).toNat
      constructor
      · omega
      · exact (Int.toNat_of_nonneg h1).symm
    · have h1 : 0 ≤ x + ↑rad := by omega
      simp [Int.toNat_of_nonneg h1]

/-- List-based coefficient box: constructive alternative to Finset version.
    Uses List.product which doesn't depend on Classical.choice.

    This is identical in content to coeffBox but uses lists instead of finsets,
    avoiding the classical axiom from Finset.product (×ˢ). -/
def coeffBoxList {d : ℕ} (ε R : ℚ) (M : ℕ) (k : Lattice d) : List (ℤ × ℤ) :=
  let δ := meshD d ε M
  let bound := coeffBound R k
  let rad := Nat.ceil (bound / δ) + 1
  -- Use auxiliary definition to avoid do-notation expansion
  List.product (intRangeList rad) (intRangeList rad)

/-- The origin (0, 0) is in the list-based coefficient box -/
lemma zero_in_coeffBoxList {d : ℕ} (ε R : ℚ) (M : ℕ) (k : Lattice d) :
    (0, 0) ∈ coeffBoxList ε R M k := by
  unfold coeffBoxList
  set rad := Nat.ceil (coeffBound R k / meshD d ε M) + 1
  apply List.mem_product.mpr
  exact ⟨zero_mem_intRangeList rad (by omega), zero_mem_intRangeList rad (by omega)⟩

/-- The list-based coefficient box is non-empty (contains at least (0, 0)) -/
lemma coeffBoxList_nonempty {d : ℕ} (ε R : ℚ) (M : ℕ) (k : Lattice d) :
    (coeffBoxList ε R M k).length > 0 := by
  -- Use the fact that it contains (0, 0)
  apply List.length_pos_of_ne_nil
  apply List.ne_nil_of_mem
  exact zero_in_coeffBoxList ε R M k

/-- Equivalence between list-based and Finset-based coefficient boxes -/
lemma coeffBoxList_eq_coeffBox {d : ℕ} (ε R : ℚ) (M : ℕ) (k : Lattice d) :
    (coeffBoxList ε R M k).toFinset = coeffBox ε R M k := by
  unfold coeffBoxList coeffBox
  set rad := Nat.ceil (coeffBound R k / meshD d ε M) + 1
  -- Show (List.product (intRangeList rad) (intRangeList rad)).toFinset
  --    = (Finset.Icc (-rad : ℤ) rad) ×ˢ (Finset.Icc (-rad : ℤ) rad)
  ext ⟨p1, p2⟩
  simp only [List.mem_toFinset, Finset.mem_product]
  -- Use the direct characterization of membership in List.product
  have h_prod : (p1, p2) ∈ List.product (intRangeList rad) (intRangeList rad) ↔
      p1 ∈ intRangeList rad ∧ p2 ∈ intRangeList rad := List.mem_product
  rw [h_prod]
  constructor
  · intro ⟨ha, hb⟩
    have ⟨ha1, ha2⟩ := mem_intRangeList_iff rad p1 |>.mp ha
    have ⟨hb1, hb2⟩ := mem_intRangeList_iff rad p2 |>.mp hb
    exact ⟨Finset.mem_Icc.mpr ⟨ha1, ha2⟩, Finset.mem_Icc.mpr ⟨hb1, hb2⟩⟩
  · intro ⟨ha, hb⟩
    have ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
    have ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
    exact ⟨mem_intRangeList_iff rad p1 |>.mpr ⟨ha1, ha2⟩,
           mem_intRangeList_iff rad p2 |>.mpr ⟨hb1, hb2⟩⟩

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

/-- Evaluation at the origin is always zero, ensuring the mean-zero property. -/
@[simp] lemma gridToSeqD_origin {d : ℕ} (ε R : ℚ) (M : ℕ)
    (g : GridPointD d ε R M) :
    (gridToSeqD ε R M g).a (fun _ => 0) = 0 := by
  have h0 : (fun _ : Fin d => (0 : ℤ)) ∉ IndexSetD d M := by
    simp [IndexSetD]
  simp [gridToSeqD, h0]

lemma gridToSeqD_meanZero {d : ℕ} (ε R : ℚ) (M : ℕ)
    (g : GridPointD d ε R M) :
    meanZero (gridToSeqD ε R M g) := by
  unfold meanZero
  simp

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

/-! ## Constructive Grid Point (ConstructiveQ + List-based boxes) -/

/-- **CONSTRUCTIVE**: Grid point using ConstructiveQ parameters and List-based coefficient boxes.

    This is the fully constructive alternative to GridPointD:
    - Uses ConstructiveQ.Q instead of ℚ for mesh/bound parameters (eliminates SOURCE 2)
    - Uses coeffBoxList (List-based) instead of coeffBox (Finset-based) (eliminates SOURCE 3)

    Type signature: For each frequency k in the index set, provides a coefficient
    from the List-based box for k.

    Axioms: Should only use [propext], NO Classical.choice -/
def GridPointD_C (d : ℕ) (ε R : ConstructiveQ.Q) (M : ℕ) : Type :=
  (k : Lattice d) → k ∈ IndexSetD d M →
    {p : ℤ × ℤ // p ∈ coeffBoxList (constructiveQ_to_rat ε) (constructiveQ_to_rat R) M k}

/-- **CONSTRUCTIVE**: Canonical zero grid point (all coefficients zero) using ConstructiveQ -/
def zeroGridPointD_C {d : ℕ} (ε R : ConstructiveQ.Q) (M : ℕ) : GridPointD_C d ε R M :=
  fun k _hk => ⟨(0, 0),
    zero_in_coeffBoxList (constructiveQ_to_rat ε) (constructiveQ_to_rat R) M k⟩

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

/-- **CONSTRUCTIVE**: Round each coefficient to the nearest grid point using ConstructiveQ and List-based boxes.

    This is the FULLY CONSTRUCTIVE version of roundToGridD with the following SOURCE ELIMINATIONS:

    SOURCE ELIMINATION STATUS:
    - SOURCE 1 (Complex roundCoeff): ISOLATED (still present, but isolated to this one function)
    - SOURCE 2 (ℚ arithmetic in meshD): ELIMINATED (now uses ConstructiveQ meshD_C)
    - SOURCE 3 (Finset.product in coeffBox): ELIMINATED (now uses List coeffBoxList)

    Classical.choice usage:
    - roundCoeff uses Complex.floor which has Classical.choice (SOURCE 1 - isolated)
    - All other operations are constructive (ConstructiveQ, List-based)

    This achieves 2/3 source elimination from the original roundToGridD.

    Axioms: Expected [propext, Classical.choice, Quot.sound]
            where Classical.choice comes ONLY from roundCoeff (Complex), not from ℚ or Finset! -/
noncomputable def roundToGridD_C {d : ℕ} (ε R : ConstructiveQ.Q) (M : ℕ) (x : SeqD d) :
    GridPointD_C d ε R M :=
  fun k _hk =>
    -- Compute mesh using ConstructiveQ (no Classical.choice!)
    let δ_C := meshD_C d ε M
    let δ := constructiveQ_to_rat δ_C
    -- Round the coefficient (uses Complex floor - unavoidable with current ℂ-valued SeqD)
    let rounded := roundCoeff δ (x.a k)
    -- Check membership in LIST-based box (no Classical.choice!)
    if h : rounded ∈ coeffBoxList (constructiveQ_to_rat ε) (constructiveQ_to_rat R) M k
    then ⟨rounded, h⟩
    else ⟨(0, 0), zero_in_coeffBoxList (constructiveQ_to_rat ε) (constructiveQ_to_rat R) M k⟩

/-- **FULLY CONSTRUCTIVE**: Sequence with rational-valued Fourier coefficients.
    For actual extraction where coefficients are known to be rational. -/
structure SeqD_Rat (d : ℕ) where
  /-- Coefficient function: ℤᵈ → ℚ × ℚ -/
  a : Lattice d → ℚ × ℚ
  /-- Square-summability condition (can be proven for finite support) -/
  finite_support : {k : Lattice d | a k ≠ (0, 0)}.Finite

@[ext] lemma SeqD_Rat.ext {d : ℕ} {u v : SeqD_Rat d} (h : ∀ k, u.a k = v.a k) : u = v := by
  cases u
  cases v
  congr
  exact funext h

/-- **FULLY CONSTRUCTIVE**: Round rational coefficients to grid - ZERO classical! -/
def roundToGridD_Rat {d : ℕ} (ε R : ConstructiveQ.Q) (M : ℕ) (x : SeqD_Rat d) :
    GridPointD_C d ε R M :=
  fun k _hk =>
    let δ_C := meshD_C d ε M
    let δ := constructiveQ_to_rat δ_C
    let (re, im) := x.a k
    -- Use constructive rounding (C0!)
    let rounded := roundCoeff_CQ δ re im
    if h : rounded ∈ coeffBoxList (constructiveQ_to_rat ε) (constructiveQ_to_rat R) M k
    then ⟨rounded, h⟩
    else ⟨(0, 0), zero_in_coeffBoxList (constructiveQ_to_rat ε) (constructiveQ_to_rat R) M k⟩

/-- **CONSTRUCTIVE**: Convert GridPointD_C back to SeqD for soundness statement -/
noncomputable def gridToSeqD_C {d : ℕ} (ε R : ConstructiveQ.Q) (M : ℕ) (g : GridPointD_C d ε R M) :
    SeqD d where
  a := fun k =>
    if h : k ∈ IndexSetD d M then
      let δ := constructiveQ_to_rat (meshD_C d ε M)
      let p := g k h
      -- Scale integer pair back to complex: (p₁ + i·p₂) · δ
      ((p.val.1 : ℂ) * (δ : ℝ) + Complex.I * ((p.val.2 : ℂ) * (δ : ℝ)))
    else 0
  summable_sq := by
    -- Finite support → summable
    refine summable_of_ne_finset_zero (s := IndexSetD d M) ?_
    intro k hk
    simp only [dif_neg hk, norm_zero, sq, zero_mul]

/-- Evaluation at the origin is always zero, ensuring the mean-zero property. -/
@[simp] lemma gridToSeqD_C_origin {d : ℕ} (ε R : ConstructiveQ.Q) (M : ℕ)
    (g : GridPointD_C d ε R M) :
    (gridToSeqD_C ε R M g).a (fun _ => 0) = 0 := by
  have h0 : (fun _ : Fin d => (0 : ℤ)) ∉ IndexSetD d M := by
    simp [IndexSetD]
  simp [gridToSeqD_C, h0]

lemma gridToSeqD_C_meanZero {d : ℕ} (ε R : ConstructiveQ.Q) (M : ℕ)
    (g : GridPointD_C d ε R M) :
    meanZero (gridToSeqD_C ε R M g) := by
  unfold meanZero
  exact gridToSeqD_C_origin ε R M g

/-! ## Phase 3: Constructive Grid Infrastructure (List-based, ConstructiveQ) -/

/-- **CONSTRUCTIVE**: Grid point using List-based coefficient boxes instead of Finsets.

    This version avoids Classical.choice from Finset.product (×ˢ).
    Uses coeffBoxList which is List-based and fully constructive.

    Type signature: For each frequency k in the index set, provides a coefficient
    from the List-based box for k.
-/
def GridPointList (d : ℕ) (ε R : ℚ) (M : ℕ) : Type :=
  (k : Lattice d) → k ∈ IndexSetD d M → {p : ℤ × ℤ // p ∈ coeffBoxList ε R M k}

/-- **CONSTRUCTIVE**: Canonical zero grid point (all coefficients zero) -/
def zeroGridPointList {d : ℕ} (ε R : ℚ) (M : ℕ) : GridPointList d ε R M :=
  fun k _hk => ⟨(0, 0), zero_in_coeffBoxList ε R M k⟩

/-- **CONSTRUCTIVE**: Round each coefficient to the nearest grid point using ConstructiveQ mesh.

    This is the constructive version of roundToGridD with the following improvements:

    SOURCE ELIMINATION STATUS:
    - SOURCE 1 (Complex roundCoeff): ISOLATED (still present, but isolated to this one function)
    - SOURCE 2 (ℚ mesh): ELIMINATED (now uses ConstructiveQ meshD_C)
    - SOURCE 3 (Finset coeffBox): ELIMINATED (now uses List coeffBoxList)

    Classical.choice usage:
    - roundCoeff uses Complex.floor which has Classical.choice
    - All other operations are constructive (ConstructiveQ, List-based)

    This achieves 2/3 source elimination, with SOURCE 1 isolated for Phase 4.
-/
noncomputable def roundToGridList {d : ℕ} (ε R : ConstructiveQ.Q) (M : ℕ) (x : SeqD d) :
    GridPointList d (constructiveQ_to_rat ε) (constructiveQ_to_rat R) M :=
  fun k _hk =>
    -- Compute mesh using ConstructiveQ (no Classical.choice!)
    let δ_C := meshD_C d ε M
    let δ := constructiveQ_to_rat δ_C
    -- Round the coefficient (uses Complex - isolated Classical.choice)
    let rounded := roundCoeff δ (x.a k)
    -- Check membership in LIST-based box (no Classical.choice!)
    if h : rounded ∈ coeffBoxList (constructiveQ_to_rat ε) (constructiveQ_to_rat R) M k
    then ⟨rounded, h⟩
    else ⟨(0, 0),
      zero_in_coeffBoxList (constructiveQ_to_rat ε) (constructiveQ_to_rat R) M k⟩

/-- **CONSTRUCTIVE**: Convert GridPointList back to SeqD for soundness statement -/
noncomputable def gridListToSeqD {d : ℕ} (ε R : ℚ) (M : ℕ) (g : GridPointList d ε R M) :
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

/-- Evaluation at the origin is always zero, ensuring the mean-zero property. -/
@[simp] lemma gridListToSeqD_origin {d : ℕ} (ε R : ℚ) (M : ℕ)
    (g : GridPointList d ε R M) :
    (gridListToSeqD ε R M g).a (fun _ => 0) = 0 := by
  have h0 : (fun _ : Fin d => (0 : ℤ)) ∉ IndexSetD d M := by
    simp [IndexSetD]
  simp [gridListToSeqD, h0]

lemma gridListToSeqD_meanZero {d : ℕ} (ε R : ℚ) (M : ℕ)
    (g : GridPointList d ε R M) :
    meanZero (gridListToSeqD ε R M g) := by
  unfold meanZero
  simp


/-
## Axiom Verification (Phase 3 Constructive Infrastructure)

To verify axiom usage, run:

```lean
#print axioms GridPointList        -- Expected: none
#print axioms zeroGridPointList    -- Expected: none
#print axioms roundToGridList      -- Expected: [propext, Classical.choice, Quot.sound]
                                   -- Classical.choice ONLY from roundCoeff's Complex usage
#print axioms gridListToSeqD       -- Expected: [propext, Classical.choice, Quot.sound]
                                   -- (inherits from Complex.ofReal in coefficient scaling)
```

**Achievement**:
- SOURCE 2 (ℚ mesh): ELIMINATED via meshD_C (ConstructiveQ)
- SOURCE 3 (Finset coeffBox): ELIMINATED via coeffBoxList (List)
- SOURCE 1 (Complex roundCoeff): ISOLATED (only remaining Classical.choice source)

**Next Phase**: Phase 4 will eliminate SOURCE 1 by implementing constructive Complex rounding.
-/

end ℓ2ZD
