import Budgets.RellichKondrachovD.Soundness
import Mathlib.Data.String.Defs

/-!
# QRK-D Demo: Dimension-Generic Rellich-Kondrachov Demonstration

This file demonstrates the dimension-generic Rellich-Kondrachov theorem
by instantiating it for various dimensions d ∈ {1, 2, 3, 4, 5}.

## Structure

1. **Test sequences** - Explicit finite-support sequences for each dimension
2. **Witness extraction** - Apply gridFinset_sound_d to get witnesses
3. **Metadata collection** - Extract witness budgets (C0-C2 layer)
4. **Performance benchmarks** - Measure compilation and extraction times

## Implementation notes

- Uses explicit coefficient assignments (no measure theory)
- All sequences have finite support (summability trivial)
- Mean-zero and H¹ bounds proven explicitly
- Witness construction is fully computable (C0 layer)

-/

open scoped BigOperators ComplexConjugate Real

namespace QRKDDemo

open Std

open ℓ2ZD

/-! ## Type class instances -/

instance : NeZero (1 : ℕ) := ⟨by norm_num⟩
instance : NeZero (2 : ℕ) := ⟨by norm_num⟩
instance : NeZero (3 : ℕ) := ⟨by norm_num⟩
instance : NeZero (4 : ℕ) := ⟨by norm_num⟩
instance : NeZero (5 : ℕ) := ⟨by norm_num⟩

/-! ## Helper lemma for H¹ bound calculations -/

lemma sum_on_finset_le_card_mul {α : Type*} {s : Finset α} {f : α → ℝ} {bound : ℝ}
    (h : ∀ x ∈ s, f x ≤ bound) :
    ∑ x ∈ s, f x ≤ (s.card : ℝ) * bound := by
  calc ∑ x ∈ s, f x
      ≤ ∑ x ∈ s, bound := Finset.sum_le_sum h
    _ = (s.card : ℝ) * bound := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Test sequences for various dimensions -/

/-- Test sequence for dimension 1 (singleton spike at k=1) -/
noncomputable def testSeq1D : SeqD 1 where
  a := fun k =>
    if k = (fun _ => (1 : ℤ)) then (1 : ℂ)
    else if k = (fun _ => (-1 : ℤ)) then (1 : ℂ)
    else 0
  summable_sq := by
    apply summable_of_ne_finset_zero
      (s := {(fun _ => (1 : ℤ)), (fun _ => (-1 : ℤ))})
    intro k hk
    simp [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

/-- testSeq1D is mean-zero -/
lemma testSeq1D_meanZero : meanZero testSeq1D := by
  rfl

/-- testSeq1D is in H¹ ball of radius 10 -/
lemma testSeq1D_inH1 : InH1Ball (10 : ℝ) testSeq1D := by
  intro F
  -- Direct upper bound on the weighted sum
  let support := ({(fun _ => (1 : ℤ)), (fun _ => (-1 : ℤ))} : Finset (Lattice 1))

  have h_energy : ∀ k ∈ support, h1Weight k * ‖testSeq1D.a k‖^2 ≤ (1 + 4 * Real.pi^2) * 1 := by
    intro k hk
    -- Each mode has normSq = 1, coeff magnitude = 1
    simp only [support, Finset.mem_insert, Finset.mem_singleton] at hk
    cases hk with
    | inl h =>
      rw [h]
      unfold h1Weight normSq testSeq1D
      simp only [if_true]
      norm_num
    | inr h =>
      rw [h]
      unfold h1Weight normSq testSeq1D
      simp only [if_true]
      norm_num

  -- Key: testSeq1D.a k = 0 for k ∉ support
  have h_support : ∀ k, k ∉ support → testSeq1D.a k = 0 := by
    intro k hk
    unfold testSeq1D
    simp only [support, Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

  have h_eq : F.sum (fun k => h1Weight k * ‖testSeq1D.a k‖^2) =
                (F ∩ support).sum (fun k => h1Weight k * ‖testSeq1D.a k‖^2) := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro k hk hnotin
    simp only [Finset.mem_inter] at hnotin
    push_neg at hnotin
    rw [h_support k (hnotin hk)]
    simp

  show ∑ k ∈ F, h1Weight k * ‖testSeq1D.a k‖^2 ≤ (10 : ℝ)^2
  calc ∑ k ∈ F, h1Weight k * ‖testSeq1D.a k‖^2
      = ∑ k ∈ F ∩ support, h1Weight k * ‖testSeq1D.a k‖^2 := h_eq
      _ ≤ ∑ k ∈ support, h1Weight k * ‖testSeq1D.a k‖^2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro k _ _
        apply mul_nonneg
        · unfold h1Weight normSq
          apply add_nonneg
          · norm_num
          · apply mul_nonneg
            · apply mul_nonneg; norm_num; exact sq_nonneg _
            · apply Finset.sum_nonneg; intros; exact sq_nonneg _
        · exact sq_nonneg _
      _ ≤ ∑ k ∈ support, ((1 + 4 * Real.pi^2) * 1) := by
        apply Finset.sum_le_sum
        intro k hk
        exact h_energy k hk
      _ = support.card * ((1 + 4 * Real.pi^2) * 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = 2 * ((1 + 4 * Real.pi^2) * 1) := by
        have h_card : support.card = 2 := by
          show ({(fun _ => (1 : ℤ)), (fun _ => (-1 : ℤ))} : Finset (Lattice 1)).card = 2
          rw [Finset.card_insert_of_notMem]
          · rw [Finset.card_singleton]
          · decide
        rw [h_card]
        rfl
      _ ≤ (10 : ℝ)^2 := by
        have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
        have hpi_sq : Real.pi^2 < 3.1416^2 := by
          have : (0 : ℝ) < Real.pi := Real.pi_pos
          nlinarith [sq_nonneg Real.pi, this, hpi]
        have h1 : 2 * ((1 + 4 * Real.pi^2) * 1) = 2 + 8 * Real.pi^2 := by ring
        have h2 : 8 * Real.pi^2 < 8 * 9.87 := by nlinarith [hpi_sq]
        have h3 : (2 : ℝ) + 8 * 9.87 < 100 := by norm_num
        have : 2 * ((1 + 4 * Real.pi^2) * 1) < 100 := by
          calc 2 * ((1 + 4 * Real.pi^2) * 1)
              = 2 + 8 * Real.pi^2 := h1
              _ < 2 + 8 * 9.87 := by linarith [h2]
              _ < 100 := h3
        linarith [this]

/-- Test sequence for dimension 2 -/
noncomputable def testSeq2D : SeqD 2 where
  a := fun k =>
    if k = (fun i => if i = 0 then 1 else 0) then (1 : ℂ)
    else if k = (fun i => if i = 0 then 0 else 1) then (1 : ℂ)
    else 0
  summable_sq := by
    apply summable_of_ne_finset_zero
      (s := {(fun i => if i = 0 then 1 else 0), (fun i => if i = 0 then 0 else 1)})
    intro k hk
    simp [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

/-- testSeq2D is mean-zero -/
lemma testSeq2D_meanZero : meanZero testSeq2D := by
  rfl

/-- testSeq2D is in H¹ ball of radius 10 -/
lemma testSeq2D_inH1 : InH1Ball (10 : ℝ) testSeq2D := by
  intro F
  -- Direct upper bound on the weighted sum
  let support := ({(fun i => if i = 0 then 1 else 0), (fun i => if i = 0 then 0 else 1)} : Finset (Lattice 2))

  have h_energy : ∀ k ∈ support, h1Weight k * ‖testSeq2D.a k‖^2 ≤ (1 + 4 * Real.pi^2) * 1 := by
    intro k hk
    -- Each mode has normSq = 1, coeff magnitude = 1
    simp only [support, Finset.mem_insert, Finset.mem_singleton] at hk
    cases hk with
    | inl h =>
      rw [h]
      unfold h1Weight normSq testSeq2D
      simp only [if_true, Finset.sum_fin_eq_sum_range,
                 Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp
    | inr h =>
      rw [h]
      unfold h1Weight normSq testSeq2D
      simp only [if_true, Finset.sum_fin_eq_sum_range,
                 Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp

  -- Key: testSeq2D.a k = 0 for k ∉ support
  have h_support : ∀ k, k ∉ support → testSeq2D.a k = 0 := by
    intro k hk
    unfold testSeq2D
    simp only [support, Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

  have h_eq : F.sum (fun k => h1Weight k * ‖testSeq2D.a k‖^2) =
                (F ∩ support).sum (fun k => h1Weight k * ‖testSeq2D.a k‖^2) := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro k hk hnotin
    simp only [Finset.mem_inter] at hnotin
    push_neg at hnotin
    rw [h_support k (hnotin hk)]
    simp

  show ∑ k ∈ F, h1Weight k * ‖testSeq2D.a k‖^2 ≤ (10 : ℝ)^2
  calc ∑ k ∈ F, h1Weight k * ‖testSeq2D.a k‖^2
      = ∑ k ∈ F ∩ support, h1Weight k * ‖testSeq2D.a k‖^2 := h_eq
      _ ≤ ∑ k ∈ support, h1Weight k * ‖testSeq2D.a k‖^2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro k _ _
        apply mul_nonneg
        · unfold h1Weight normSq
          apply add_nonneg
          · norm_num
          · apply mul_nonneg
            · apply mul_nonneg; norm_num; exact sq_nonneg _
            · apply Finset.sum_nonneg; intros; exact sq_nonneg _
        · exact sq_nonneg _
      _ ≤ ∑ k ∈ support, ((1 + 4 * Real.pi^2) * 1) := by
        apply Finset.sum_le_sum
        intro k hk
        exact h_energy k hk
      _ = support.card * ((1 + 4 * Real.pi^2) * 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = 2 * ((1 + 4 * Real.pi^2) * 1) := by
        have h_card : support.card = 2 := by
          show ({(fun i => if i = 0 then 1 else 0),
                 (fun i => if i = 0 then 0 else 1)} : Finset (Lattice 2)).card = 2
          rw [Finset.card_insert_of_notMem]
          · rw [Finset.card_singleton]
          · decide
        rw [h_card]
        rfl
      _ ≤ (10 : ℝ)^2 := by
        have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
        have hpi_sq : Real.pi^2 < 3.1416^2 := by
          have : (0 : ℝ) < Real.pi := Real.pi_pos
          nlinarith [sq_nonneg Real.pi, this, hpi]
        have h1 : 2 * ((1 + 4 * Real.pi^2) * 1) = 2 + 8 * Real.pi^2 := by ring
        have h2 : 8 * Real.pi^2 < 8 * 9.87 := by nlinarith [hpi_sq]
        have h3 : (2 : ℝ) + 8 * 9.87 < 100 := by norm_num
        have : 2 * ((1 + 4 * Real.pi^2) * 1) < 100 := by
          calc 2 * ((1 + 4 * Real.pi^2) * 1)
              = 2 + 8 * Real.pi^2 := h1
              _ < 2 + 8 * 9.87 := by linarith [h2]
              _ < 100 := h3
        linarith [this]

/-- Test sequence for dimension 3 -/
noncomputable def testSeq3D : SeqD 3 where
  a := fun k =>
    if k = (fun i => if i = 0 then 1 else 0) then (1 : ℂ)
    else if k = (fun i => if i = 1 then 1 else 0) then (1 : ℂ)
    else if k = (fun i => if i = 2 then 1 else 0) then (1 : ℂ)
    else 0
  summable_sq := by
    apply summable_of_ne_finset_zero
      (s := {(fun i => if i = 0 then 1 else 0),
             (fun i => if i = 1 then 1 else 0),
             (fun i => if i = 2 then 1 else 0)})
    intro k hk
    simp [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

/-- testSeq3D is mean-zero -/
lemma testSeq3D_meanZero : meanZero testSeq3D := by
  rfl

/-- testSeq3D is in H¹ ball of radius 13 -/
lemma testSeq3D_inH1 : InH1Ball (13 : ℝ) testSeq3D := by
  intro F
  -- Direct upper bound on the weighted sum
  let support := ({(fun i => if i = 0 then 1 else 0),
                    (fun i => if i = 1 then 1 else 0),
                    (fun i => if i = 2 then 1 else 0)} : Finset (Lattice 3))

  have h_energy : ∀ k ∈ support, h1Weight k * ‖testSeq3D.a k‖^2 ≤ (1 + 4 * Real.pi^2) * 1 := by
    intro k hk
    -- Each mode has normSq = 1, coeff magnitude = 1
    simp only [support, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with h | h | h
    · rw [h]
      unfold h1Weight normSq testSeq3D
      simp only [if_true, Finset.sum_fin_eq_sum_range,
                 Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp
    · rw [h]
      unfold h1Weight normSq testSeq3D
      simp only [if_true, Finset.sum_fin_eq_sum_range,
                 Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp
    · rw [h]
      unfold h1Weight normSq testSeq3D
      simp only [if_true, Finset.sum_fin_eq_sum_range,
                 Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp

  -- Key: testSeq3D.a k = 0 for k ∉ support
  have h_support : ∀ k, k ∉ support → testSeq3D.a k = 0 := by
    intro k hk
    unfold testSeq3D
    simp only [support, Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

  have h_eq : F.sum (fun k => h1Weight k * ‖testSeq3D.a k‖^2) =
                (F ∩ support).sum (fun k => h1Weight k * ‖testSeq3D.a k‖^2) := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro k hk hnotin
    simp only [Finset.mem_inter] at hnotin
    push_neg at hnotin
    rw [h_support k (hnotin hk)]
    simp

  show ∑ k ∈ F, h1Weight k * ‖testSeq3D.a k‖^2 ≤ (13 : ℝ)^2
  calc ∑ k ∈ F, h1Weight k * ‖testSeq3D.a k‖^2
      = ∑ k ∈ F ∩ support, h1Weight k * ‖testSeq3D.a k‖^2 := h_eq
      _ ≤ ∑ k ∈ support, h1Weight k * ‖testSeq3D.a k‖^2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro k _ _
        apply mul_nonneg
        · unfold h1Weight normSq
          apply add_nonneg
          · norm_num
          · apply mul_nonneg
            · apply mul_nonneg; norm_num; exact sq_nonneg _
            · apply Finset.sum_nonneg; intros; exact sq_nonneg _
        · exact sq_nonneg _
      _ ≤ ∑ k ∈ support, ((1 + 4 * Real.pi^2) * 1) := by
        apply Finset.sum_le_sum
        intro k hk
        exact h_energy k hk
      _ = support.card * ((1 + 4 * Real.pi^2) * 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = 3 * ((1 + 4 * Real.pi^2) * 1) := by
        have h_card : support.card = 3 := by
          show ({(fun i => if i = 0 then 1 else 0),
                 (fun i => if i = 1 then 1 else 0),
                 (fun i => if i = 2 then 1 else 0)} : Finset (Lattice 3)).card = 3
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
          · rw [Finset.card_singleton]
          · decide
          · decide
        rw [h_card]
        rfl
      _ ≤ (13 : ℝ)^2 := by
        have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
        have hpi_sq : Real.pi^2 < 3.1416^2 := by
          have : (0 : ℝ) < Real.pi := Real.pi_pos
          nlinarith [sq_nonneg Real.pi, this, hpi]
        have h1 : 3 * ((1 + 4 * Real.pi^2) * 1) = 3 + 12 * Real.pi^2 := by ring
        have h2 : 12 * Real.pi^2 < 12 * 9.87 := by nlinarith [hpi_sq]
        have h3 : (3 : ℝ) + 12 * 9.87 < 169 := by norm_num
        have : 3 * ((1 + 4 * Real.pi^2) * 1) < 169 := by
          calc 3 * ((1 + 4 * Real.pi^2) * 1)
              = 3 + 12 * Real.pi^2 := h1
              _ < 3 + 12 * 9.87 := by linarith [h2]
              _ < 169 := h3
        linarith [this]

/-- Test sequence for dimension 4 -/
noncomputable def testSeq4D : SeqD 4 where
  a := fun k =>
    if k = (fun i => if i = 0 then 1 else 0) then (1 : ℂ)
    else if k = (fun i => if i = 1 then 1 else 0) then (1 : ℂ)
    else if k = (fun i => if i = 2 then 1 else 0) then (1 : ℂ)
    else if k = (fun i => if i = 3 then 1 else 0) then (1 : ℂ)
    else 0
  summable_sq := by
    apply summable_of_ne_finset_zero
      (s := {(fun i => if i = 0 then 1 else 0),
             (fun i => if i = 1 then 1 else 0),
             (fun i => if i = 2 then 1 else 0),
             (fun i => if i = 3 then 1 else 0)})
    intro k hk
    simp [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

/-- testSeq4D is mean-zero -/
lemma testSeq4D_meanZero : meanZero testSeq4D := by
  rfl

/-- testSeq4D is in H¹ ball of radius 14 -/
lemma testSeq4D_inH1 : InH1Ball (14 : ℝ) testSeq4D := by
  intro F
  -- Direct upper bound on the weighted sum
  let support := ({(fun i => if i = 0 then 1 else 0),
                    (fun i => if i = 1 then 1 else 0),
                    (fun i => if i = 2 then 1 else 0),
                    (fun i => if i = 3 then 1 else 0)} : Finset (Lattice 4))

  have h_energy : ∀ k ∈ support, h1Weight k * ‖testSeq4D.a k‖^2 ≤ (1 + 4 * Real.pi^2) * 1 := by
    intro k hk
    -- Each mode has normSq = 1, coeff magnitude = 1
    simp only [support, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with h | h | h | h
    · rw [h]
      unfold h1Weight normSq testSeq4D
      simp only [if_true, Finset.sum_fin_eq_sum_range,
                 Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp
    · rw [h]
      unfold h1Weight normSq testSeq4D
      simp only [if_true, Finset.sum_fin_eq_sum_range,
                 Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp
    · rw [h]
      unfold h1Weight normSq testSeq4D
      simp only [if_true, Finset.sum_fin_eq_sum_range,
                 Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp
    · rw [h]
      unfold h1Weight normSq testSeq4D
      simp only [if_true, Finset.sum_fin_eq_sum_range,
                 Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp

  -- Key: testSeq4D.a k = 0 for k ∉ support
  have h_support : ∀ k, k ∉ support → testSeq4D.a k = 0 := by
    intro k hk
    unfold testSeq4D
    simp only [support, Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

  have h_eq : F.sum (fun k => h1Weight k * ‖testSeq4D.a k‖^2) =
                (F ∩ support).sum (fun k => h1Weight k * ‖testSeq4D.a k‖^2) := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro k hk hnotin
    simp only [Finset.mem_inter] at hnotin
    push_neg at hnotin
    rw [h_support k (hnotin hk)]
    simp

  show ∑ k ∈ F, h1Weight k * ‖testSeq4D.a k‖^2 ≤ (14 : ℝ)^2
  calc ∑ k ∈ F, h1Weight k * ‖testSeq4D.a k‖^2
      = ∑ k ∈ F ∩ support, h1Weight k * ‖testSeq4D.a k‖^2 := h_eq
      _ ≤ ∑ k ∈ support, h1Weight k * ‖testSeq4D.a k‖^2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro k _ _
        apply mul_nonneg
        · unfold h1Weight normSq
          apply add_nonneg
          · norm_num
          · apply mul_nonneg
            · apply mul_nonneg; norm_num; exact sq_nonneg _
            · apply Finset.sum_nonneg; intros; exact sq_nonneg _
        · exact sq_nonneg _
      _ ≤ ∑ k ∈ support, ((1 + 4 * Real.pi^2) * 1) := by
        apply Finset.sum_le_sum
        intro k hk
        exact h_energy k hk
      _ = support.card * ((1 + 4 * Real.pi^2) * 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = 4 * ((1 + 4 * Real.pi^2) * 1) := by
        have h_card : support.card = 4 := by
          show ({(fun i => if i = 0 then 1 else 0),
                 (fun i => if i = 1 then 1 else 0),
                 (fun i => if i = 2 then 1 else 0),
                 (fun i => if i = 3 then 1 else 0)} : Finset (Lattice 4)).card = 4
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
          · rw [Finset.card_singleton]
          · decide
          · decide
          · decide
        rw [h_card]
        rfl
      _ ≤ (14 : ℝ)^2 := by
        have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
        have hpi_sq : Real.pi^2 < 3.1416^2 := by
          have : (0 : ℝ) < Real.pi := Real.pi_pos
          nlinarith [sq_nonneg Real.pi, this, hpi]
        have h1 : 4 * ((1 + 4 * Real.pi^2) * 1) = 4 + 16 * Real.pi^2 := by ring
        have h2 : 16 * Real.pi^2 < 16 * 9.87 := by nlinarith [hpi_sq]
        have h3 : (4 : ℝ) + 16 * 9.87 < 196 := by norm_num
        have : 4 * ((1 + 4 * Real.pi^2) * 1) < 196 := by
          calc 4 * ((1 + 4 * Real.pi^2) * 1)
              = 4 + 16 * Real.pi^2 := h1
              _ < 4 + 16 * 9.87 := by linarith [h2]
              _ < 196 := h3
        linarith [this]

/-- Test sequence for dimension 5 -/
noncomputable def testSeq5D : SeqD 5 where
  a := fun k =>
    if k = (fun i => if i = 0 then 1 else 0) then (1 : ℂ)
    else if k = (fun i => if i = 1 then 1 else 0) then (1 : ℂ)
    else if k = (fun i => if i = 2 then 1 else 0) then (1 : ℂ)
    else if k = (fun i => if i = 3 then 1 else 0) then (1 : ℂ)
    else if k = (fun i => if i = 4 then 1 else 0) then (1 : ℂ)
    else 0
  summable_sq := by
    apply summable_of_ne_finset_zero
      (s := {(fun i => if i = 0 then 1 else 0),
             (fun i => if i = 1 then 1 else 0),
             (fun i => if i = 2 then 1 else 0),
             (fun i => if i = 3 then 1 else 0),
             (fun i => if i = 4 then 1 else 0)})
    intro k hk
    simp [Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

/-- testSeq5D is mean-zero -/
lemma testSeq5D_meanZero : meanZero testSeq5D := by
  rfl

/-- testSeq5D is in H¹ ball of radius 16 -/
lemma testSeq5D_inH1 : InH1Ball (16 : ℝ) testSeq5D := by
  intro F
  -- Direct upper bound on the weighted sum
  let support := ({(fun i => if i = 0 then 1 else 0),
                    (fun i => if i = 1 then 1 else 0),
                    (fun i => if i = 2 then 1 else 0),
                    (fun i => if i = 3 then 1 else 0),
                    (fun i => if i = 4 then 1 else 0)} : Finset (Lattice 5))

  have h_energy : ∀ k ∈ support, h1Weight k * ‖testSeq5D.a k‖^2 ≤ (1 + 4 * Real.pi^2) * 1 := by
    intro k hk
    -- Each mode has normSq = 1, coeff magnitude = 1
    simp only [support, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with h | h | h | h | h
    · rw [h]
      unfold h1Weight normSq testSeq5D
      simp only [if_true, Finset.sum_fin_eq_sum_range,
                 Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp
    · rw [h]
      unfold h1Weight normSq testSeq5D
      simp only [if_true, Finset.sum_fin_eq_sum_range,
                 Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp
    · rw [h]
      unfold h1Weight normSq testSeq5D
      simp only [if_true, Finset.sum_fin_eq_sum_range,
                 Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp
    · rw [h]
      unfold h1Weight normSq testSeq5D
      simp only [if_true, Finset.sum_fin_eq_sum_range,
                 Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp
    · rw [h]
      unfold h1Weight normSq testSeq5D
      simp only [if_true, Finset.sum_fin_eq_sum_range,
                 Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp

  -- Key: testSeq5D.a k = 0 for k ∉ support
  have h_support : ∀ k, k ∉ support → testSeq5D.a k = 0 := by
    intro k hk
    unfold testSeq5D
    simp only [support, Finset.mem_insert, Finset.mem_singleton] at hk
    push_neg at hk
    simp [hk]

  have h_eq : F.sum (fun k => h1Weight k * ‖testSeq5D.a k‖^2) =
                (F ∩ support).sum (fun k => h1Weight k * ‖testSeq5D.a k‖^2) := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro k hk hnotin
    simp only [Finset.mem_inter] at hnotin
    push_neg at hnotin
    rw [h_support k (hnotin hk)]
    simp

  show ∑ k ∈ F, h1Weight k * ‖testSeq5D.a k‖^2 ≤ (16 : ℝ)^2
  calc ∑ k ∈ F, h1Weight k * ‖testSeq5D.a k‖^2
      = ∑ k ∈ F ∩ support, h1Weight k * ‖testSeq5D.a k‖^2 := h_eq
      _ ≤ ∑ k ∈ support, h1Weight k * ‖testSeq5D.a k‖^2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro k _ _
        apply mul_nonneg
        · unfold h1Weight normSq
          apply add_nonneg
          · norm_num
          · apply mul_nonneg
            · apply mul_nonneg; norm_num; exact sq_nonneg _
            · apply Finset.sum_nonneg; intros; exact sq_nonneg _
        · exact sq_nonneg _
      _ ≤ ∑ k ∈ support, ((1 + 4 * Real.pi^2) * 1) := by
        apply Finset.sum_le_sum
        intro k hk
        exact h_energy k hk
      _ = support.card * ((1 + 4 * Real.pi^2) * 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = 5 * ((1 + 4 * Real.pi^2) * 1) := by
        have h_card : support.card = 5 := by
          show ({(fun i => if i = 0 then 1 else 0),
                 (fun i => if i = 1 then 1 else 0),
                 (fun i => if i = 2 then 1 else 0),
                 (fun i => if i = 3 then 1 else 0),
                 (fun i => if i = 4 then 1 else 0)} : Finset (Lattice 5)).card = 5
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
          · rw [Finset.card_singleton]
          · decide
          · decide
          · decide
          · decide
        rw [h_card]
        rfl
      _ ≤ (16 : ℝ)^2 := by
        have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
        have hpi_sq : Real.pi^2 < 3.1416^2 := by
          have : (0 : ℝ) < Real.pi := Real.pi_pos
          nlinarith [sq_nonneg Real.pi, this, hpi]
        have h1 : 5 * ((1 + 4 * Real.pi^2) * 1) = 5 + 20 * Real.pi^2 := by ring
        have h2 : 20 * Real.pi^2 < 20 * 9.87 := by nlinarith [hpi_sq]
        have h3 : (5 : ℝ) + 20 * 9.87 < 256 := by norm_num
        have : 5 * ((1 + 4 * Real.pi^2) * 1) < 256 := by
          calc 5 * ((1 + 4 * Real.pi^2) * 1)
              = 5 + 20 * Real.pi^2 := h1
              _ < 5 + 20 * 9.87 := by linarith [h2]
              _ < 256 := h3
        linarith [this]

/-! ## Witness extraction theorems -/

/-- Dimension 1 witness extraction -/
theorem witness_1D : ∃ (g : GridPointD 1 (1/10) 10 (M_of (1/10) 10)),
    ∀ F : Finset (Lattice 1),
      Finset.sum F (fun k => ‖testSeq1D.a k - (gridToSeqD (1/10) 10 (M_of (1/10) 10) g).a k‖^2)
        < ((1/10 : ℚ) : ℝ)^2 := by
  apply gridFinset_sound_d_proof
  · norm_num
  · norm_num
  · exact testSeq1D_meanZero
  · exact testSeq1D_inH1

/-- Dimension 2 witness extraction -/
theorem witness_2D : ∃ (g : GridPointD 2 (1/10) 10 (M_of (1/10) 10)),
    ∀ F : Finset (Lattice 2),
      Finset.sum F (fun k => ‖testSeq2D.a k - (gridToSeqD (1/10) 10 (M_of (1/10) 10) g).a k‖^2)
        < ((1/10 : ℚ) : ℝ)^2 := by
  apply gridFinset_sound_d_proof
  · norm_num
  · norm_num
  · exact testSeq2D_meanZero
  · exact testSeq2D_inH1

/-- Dimension 3 witness extraction -/
theorem witness_3D : ∃ (g : GridPointD 3 (1/10) 13 (M_of (1/10) 13)),
    ∀ F : Finset (Lattice 3),
      Finset.sum F (fun k => ‖testSeq3D.a k - (gridToSeqD (1/10) 13 (M_of (1/10) 13) g).a k‖^2)
        < ((1/10 : ℚ) : ℝ)^2 := by
  apply gridFinset_sound_d_proof
  · norm_num
  · norm_num
  · exact testSeq3D_meanZero
  · exact testSeq3D_inH1

/-- Dimension 4 witness extraction -/
theorem witness_4D : ∃ (g : GridPointD 4 (1/10) 14 (M_of (1/10) 14)),
    ∀ F : Finset (Lattice 4),
      Finset.sum F (fun k => ‖testSeq4D.a k - (gridToSeqD (1/10) 14 (M_of (1/10) 14) g).a k‖^2)
        < ((1/10 : ℚ) : ℝ)^2 := by
  apply gridFinset_sound_d_proof
  · norm_num
  · norm_num
  · exact testSeq4D_meanZero
  · exact testSeq4D_inH1

/-- Dimension 5 witness extraction -/
theorem witness_5D : ∃ (g : GridPointD 5 (1/10) 16 (M_of (1/10) 16)),
    ∀ F : Finset (Lattice 5),
      Finset.sum F (fun k => ‖testSeq5D.a k - (gridToSeqD (1/10) 16 (M_of (1/10) 16) g).a k‖^2)
        < ((1/10 : ℚ) : ℝ)^2 := by
  apply gridFinset_sound_d_proof
  · norm_num
  · norm_num
  · exact testSeq5D_meanZero
  · exact testSeq5D_inH1

/-! ## Metadata extraction (C0-C2 witness budgets) -/

/-- Extract witness package for dimension d -/
noncomputable def extractWitnessPkg (d : ℕ) (ε R : ℚ) : WitnessPkgD d :=
  { dim := d
    ε := ε
    R := R
    dim_eq := rfl }

/-- Dimension 1 witness package -/
noncomputable def witnessPkg1D : WitnessPkgD 1 :=
  extractWitnessPkg 1 (1/10) 10

/-- Dimension 2 witness package -/
noncomputable def witnessPkg2D : WitnessPkgD 2 :=
  extractWitnessPkg 2 (1/10) 10

/-- Dimension 3 witness package -/
noncomputable def witnessPkg3D : WitnessPkgD 3 :=
  extractWitnessPkg 3 (1/10) 13

/-- Dimension 4 witness package -/
noncomputable def witnessPkg4D : WitnessPkgD 4 :=
  extractWitnessPkg 4 (1/10) 14

/-- Dimension 5 witness package -/
noncomputable def witnessPkg5D : WitnessPkgD 5 :=
  extractWitnessPkg 5 (1/10) 16

/-! ## Computable Extraction Layer -/

/-- Conservative rational lower bound for π (computable) -/
def pi_rat_lb_extract : ℚ := 3

/-- Computable approximation of M_of using rational π bound -/
def M_of_computable (ε R : ℚ) : ℕ :=
  Nat.ceil (R / (pi_rat_lb_extract * ε)) + 1

/-- Computable mesh formula -/
def meshD_computable (d : ℕ) (ε : ℚ) (M : ℕ) : ℚ :=
  ε / (4 * (2 * M + 1)^(Nat.ceil (d / 2)))

/-- Metadata structure for dimension d -/
structure WitnessMetadataD (d : ℕ) where
  dimension : ℕ := d
  epsilon : ℚ
  radius : ℚ
  M : ℕ
  delta : ℚ
  gridSize : ℕ

/-- Compute witness metadata for given parameters -/
def computeMetadataD (d : ℕ) (ε R : ℚ) : WitnessMetadataD d :=
  let M := M_of_computable ε R
  let δ := meshD_computable d ε M
  let gridCard := (2 * M + 1)^d - 1
  { dimension := d
    epsilon := ε
    radius := R
    M := M
    delta := δ
    gridSize := gridCard }

/-- Format metadata for display -/
def formatMetadataD {d : ℕ} (m : WitnessMetadataD d) : String :=
  s!"Dimension d = {m.dimension}" ++ "\n" ++
  s!"Approximation accuracy ε = {m.epsilon}" ++ "\n" ++
  s!"H¹ ball radius R = {m.radius}" ++ "\n" ++
  s!"Frequency cutoff M = {m.M}" ++ "\n" ++
  s!"Grid spacing δ = {m.delta}" ++ "\n" ++
  s!"Index set size = {m.gridSize}"

/-! ## Performance benchmarks -/

/-- Print dimension-specific parameters -/
def printParams (d : ℕ) (ε R : ℚ) : String :=
  let M := M_of_computable ε R
  let δ := meshD_computable d ε M
  let cardCube := (2 * M + 1)^d
  s!"d={d}, M={M}, δ={δ}, |cube|={cardCube}"

namespace CLI

structure ParseState where
  dim? : Option Nat := none
  eps? : Option ℚ := none
  radius? : Option ℚ := none

structure Config where
  cases : List (Nat × ℚ × ℚ)
  defaultMode : Bool

def usage : String :=
  "Usage: qrkd_demo [--dim <nat> --eps <rat> --radius <rat>]\n" ++
  "  Provide a dimension and rational ε,R (e.g. 1/10) to see metadata for that case.\n" ++
  "  With no arguments, the demo prints the canonical dimensions 1–5."

private def parseNat (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => Except.ok n
  | none => Except.error s!"Invalid natural number: {s}"

private def parseInt (s : String) : Except String Int :=
  match s.toInt? with
  | some z => Except.ok z
  | none => Except.error s!"Invalid integer: {s}"

private def parseRat (s : String) : Except String ℚ :=
  let trimmed := s.trim
  if trimmed.contains '/' then
    match trimmed.splitOn "/" with
    | [numStr, denStr] =>
        do
          let num ← parseInt numStr.trim
          let den ← parseInt denStr.trim
          if den = 0 then
            Except.error s!"Denominator must be nonzero in rational: {s}"
          else
            Except.ok ((num : ℚ) / den)
    | _ => Except.error s!"Invalid rational format (expected a/b): {s}"
  else
    do
      let z ← parseInt trimmed
      Except.ok (z : ℚ)

partial def parseLoop : List String → ParseState → Except String ParseState
  | [], st => Except.ok st
  | "--dim" :: [], _ => Except.error "Missing value for --dim."
  | "--dim" :: val :: rest, st => do
      let d ← parseNat val
      parseLoop rest { st with dim? := some d }
  | "--eps" :: [], _ => Except.error "Missing value for --eps."
  | "--eps" :: val :: rest, st => do
      let ε ← parseRat val
      parseLoop rest { st with eps? := some ε }
  | "--radius" :: [], _ => Except.error "Missing value for --radius."
  | "--radius" :: val :: rest, st => do
      let R ← parseRat val
      parseLoop rest { st with radius? := some R }
  | "--help" :: _, _ => Except.error usage
  | flag :: _, _ => Except.error s!"Unknown option: {flag}\n\n{usage}"

def defaultCases : List (Nat × ℚ × ℚ) :=
  [ (1, 1/10, 10)
  , (2, 1/10, 10)
  , (3, 1/10, 13)
  , (4, 1/10, 14)
  , (5, 1/10, 16)
  ]

def buildConfig (st : ParseState) : Except String Config :=
  match st.dim?, st.eps?, st.radius? with
  | none, none, none =>
      Except.ok { cases := defaultCases, defaultMode := true }
  | some d, some ε, some R =>
      Except.ok { cases := [(d, ε, R)], defaultMode := false }
  | _, _, _ =>
      Except.error "Please supply --dim, --eps, and --radius together (or none)."

def parse (args : List String) : Except String Config := do
  let st ← parseLoop args {}
  buildConfig st

end CLI

end QRKDDemo

def printDefaultSummary : IO Unit := do
  IO.println "Computing witness parameters for dimensions 1-5..."
  IO.println ""
  IO.println s!"D=1: {QRKDDemo.printParams 1 (1/10) 10}"
  IO.println s!"D=2: {QRKDDemo.printParams 2 (1/10) 10}"
  IO.println s!"D=3: {QRKDDemo.printParams 3 (1/10) 13}"
  IO.println s!"D=4: {QRKDDemo.printParams 4 (1/10) 14}"
  IO.println s!"D=5: {QRKDDemo.printParams 5 (1/10) 16}"
  IO.println ""
  IO.println "Witness extraction theorems:"
  IO.println "  ✓ witness_1D: certified for ε=1/10, R=10"
  IO.println "  ✓ witness_2D: certified for ε=1/10, R=10"
  IO.println "  ✓ witness_3D: certified for ε=1/10, R=13"
  IO.println "  ✓ witness_4D: certified for ε=1/10, R=14"
  IO.println "  ✓ witness_5D: certified for ε=1/10, R=16"

def printCustomCase (d : Nat) (ε R : ℚ) : IO Unit := do
  IO.println s!"Custom parameters: d = {d}, ε = {ε}, R = {R}"
  let summary := QRKDDemo.computeMetadataD d ε R
  IO.println (QRKDDemo.formatMetadataD summary)
  IO.println ""

def main (args : List String) : IO Unit := do
  -- Debug: print CLI arguments (comment out once verified).
  -- IO.println s!"[qrkd_demo] args = {args}"
  match QRKDDemo.CLI.parse args with
  | Except.error msg =>
      IO.eprintln s!"qrkd_demo: {msg}"
  | Except.ok cfg => do
      IO.println "=== QRK-D Demo: Dimension-Generic Rellich-Kondrachov ==="
      IO.println ""
      if cfg.defaultMode then
        printDefaultSummary
      else
        for (d, ε, R) in cfg.cases do
          printCustomCase d ε R
