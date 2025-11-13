import Budgets.RellichKondrachovD.Core
import Budgets.RellichKondrachovD.TailBound
import Budgets.RellichKondrachovD.Rounding

/-
! Rellich–Kondrachov in arbitrary dimension: soundness

This file proves the constructive compactness statement for arbitrary `d`.  It
combines the tail and rounding estimates to show that every mean-zero element
of the H¹ ball admits an ε-close factored witness.

## Main result
* `gridFinset_sound_d` : the grid returned by `roundToGridD` covers the H¹ ball.

The proof repeats the familiar pattern: pick `M := M_of ε R`, split an arbitrary
finite sum into “outside” and “inside” parts, and apply the bounds supplied by
`TailBound` and `Rounding`.
-/

open scoped BigOperators ComplexConjugate Real

namespace ℓ2ZD

open ℓ2ZD

/-! ## Helper lemmas for soundness theorem -/

/-- Helper: Convert a filtered finset to subtype finset for tail bound application -/
lemma tail_finset_convert {d : ℕ} [NeZero d] {x : SeqD d} (F : Finset (Lattice d)) (M : ℝ)
    (h : ∀ k ∈ F, tailR M k) :
    ∃ (G : Finset {k : Lattice d // tailR M k}),
      Finset.sum G (fun g => ‖x.a g.val‖^2) = Finset.sum F (fun k => ‖x.a k‖^2) := by
  -- Use F.attach and map to subtype
  use F.attach.map ⟨fun ⟨k, hk⟩ => ⟨k, h k hk⟩, by
    intro ⟨k1, hk1⟩ ⟨k2, hk2⟩ heq
    simp only [Subtype.mk.injEq] at heq
    exact Subtype.ext heq⟩
  -- Prove sum equality
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  conv_rhs => rw [← Finset.sum_attach]

/-! ## Main Soundness Theorem -/

/-- **Main soundness theorem for dimension d**: Every mean-zero H¹-bounded sequence
    has an ε-close grid point (constructively proven via rounding).

    This is the dimension-generic version of gridFinset_sound_1D/2D/3D.

    PROOF STRATEGY (same structure as 1D/2D/3D):
    1. Choose M := M_of ε R to control tail error (dimension-free formula)
    2. Define witness g := roundToGridD ε R M x (computable via rounding)
    3. Split error into tail + inside:
       - Tail (k ∉ cube [-M,M]ᵈ): ≤ (ε/2)² using dimension-free tail_bound_finitary_d
       - Inside (k ∈ cube): ≤ (ε/2)² using rounding_bound_mesh_d with meshD formula
    4. Total: (ε/2)² + (ε/2)² = ε²/2 < ε²

    WITNESS STRUCTURE:
    - gridToSeqD g is the C0 witness function
    - GridPointD d is a function type (computable, not enumerated)
    - The witness comes from roundToGridD (computable function)
    - No axioms in extraction layer (C0-C2 witness budgets)

    KEY DIMENSION-GENERIC FEATURES:
    - M_of formula: dimension-free (same as 1D/2D/3D)
    - Tail bound: dimension-free (elementary spectral estimate)
    - meshD formula: dimension-parametric ε/(4(2M+1)^⌈d/2⌉)
    - All lemmas polymorphic over d with [NeZero d] constraint
-/
-- Provide the proof for the axiom declared in Core.lean
theorem gridFinset_sound_d_proof {d : ℕ} [NeZero d] (ε R : ℚ)
    (hε : 0 < (ε : ℝ)) (hR : 0 < (R : ℝ))
    (x : SeqD d) (hmean : meanZero x) (hH1 : InH1Ball (R : ℝ) x) :
    ∃ (g : GridPointD d ε R (M_of ε R)),
      ∀ F : Finset (Lattice d),
        Finset.sum F (fun k => ‖x.a k - (gridToSeqD ε R (M_of ε R) g).a k‖^2)
          < (ε : ℝ)^2 := by
  -- Step 1: Choose M using M_of to control tail error
  set M := M_of ε R with hMdef

  have hM : 0 < (M : ℝ) := by
    simpa [hMdef] using (Nat.cast_pos.mpr (M_of_pos ε R (Rat.cast_pos.mp hε) (Rat.cast_pos.mp hR)))

  have hM_ne : M ≠ 0 := by
    simpa [hMdef] using (Nat.pos_iff_ne_zero.mp (M_of_pos ε R (Rat.cast_pos.mp hε) (Rat.cast_pos.mp hR)))

  -- Step 2: Construct witness via rounding
  let g := roundToGridD ε R M x

  use g

  -- Step 3: Prove distance bound for any finite set F
  intro F

  -- Define center from grid point
  let c := gridToSeqD ε R M g

  -- Center evaluation lemmas
  have center_zero : ∀ k, k ∉ IndexSetD d M → c.a k = 0 := by
    intro k hk
    simp [c, gridToSeqD, hk]

  -- Split F into inside (IndexSetD d M) and outside
  let F_in := F.filter (fun k => k ∈ IndexSetD d M)
  let F_out := F.filter (fun k => k ∉ IndexSetD d M)

  -- Partition: F = F_in ∪ F_out
  have partition : F = F_in ∪ F_out := by
    ext k
    simp [F_in, F_out, Finset.mem_filter, Finset.mem_union]
    tauto

  have disj : Disjoint F_in F_out := by
    rw [Finset.disjoint_filter]
    intro k _ h1 h2
    exact h2 h1

  -- Split sum
  have sum_split :
      Finset.sum F (fun k => ‖x.a k - c.a k‖^2)
      = Finset.sum F_in (fun k => ‖x.a k - c.a k‖^2)
      + Finset.sum F_out (fun k => ‖x.a k - c.a k‖^2) := by
    rw [partition]
    exact Finset.sum_union disj

  -- INSIDE BOUND: Rounding error ≤ (ε/2)²
  have inside_bound :
      Finset.sum F_in (fun k => ‖x.a k - c.a k‖^2)
      ≤ ((ε : ℝ) / 2)^2 := by
    set δ := meshD d ε M
    have hδ : 0 < (δ : ℝ) := meshD_pos d ε M (by exact_mod_cast Rat.cast_pos.mp hε)

    -- Bound each coefficient's rounding error by 2·δ²
    have per_coeff_bound : ∀ k ∈ F_in, ‖x.a k - c.a k‖^2 ≤ 2 * (δ : ℝ)^2 := by
      intro k hk
      simp [F_in, Finset.mem_filter] at hk
      have hk_in : k ∈ IndexSetD d M := hk.2

      -- k ∈ IndexSetD M means k ≠ 0
      have hk_ne_zero : k ≠ (fun _ => 0) := by
        intro h_eq
        subst h_eq
        simp [IndexSetD] at hk_in

      -- Get H¹ bound on coefficient
      have h_coeff_bound := coeff_bound_from_H1_d hR hH1 k hk_ne_zero

      -- Apply rounded_in_box_d to show roundCoeff is in the box
      have h_in_box : roundCoeff δ (x.a k) ∈ coeffBox ε R M k :=
        rounded_in_box_d hε hR hk_ne_zero h_coeff_bound

      -- Therefore g stores the rounded coefficient (not the fallback)
      have g_eq : (g k hk_in).val = roundCoeff δ (x.a k) := by
        simp only [g, roundToGridD]
        rw [dif_pos h_in_box]

      -- Set up abbreviation for the rounded coefficient
      set p := roundCoeff δ (x.a k)

      -- Apply round_error_d to get the key bound
      have round_err := round_error_d (d := d) δ hδ (x.a k)

      -- Show that c.a k equals the scaled rounded coefficient
      have c_is_scaled_p : c.a k =
          (⟨(δ : ℝ) * p.1, (δ : ℝ) * p.2⟩ : ℂ) := by
        simp only [c, gridToSeqD, dif_pos hk_in, δ]
        have : (g k hk_in).val = p := g_eq
        rw [this]
        apply Complex.ext <;> simp [mul_comm]

      rw [c_is_scaled_p]

      calc ‖x.a k - (⟨(δ : ℝ) * p.1, (δ : ℝ) * p.2⟩ : ℂ)‖^2
          ≤ (Real.sqrt 2 * (δ : ℝ))^2 := by
            have h_nonneg : 0 ≤ Real.sqrt 2 * (δ : ℝ) := by positivity
            have h_norm_nonneg : 0 ≤ ‖x.a k - (⟨(δ : ℝ) * p.1, (δ : ℝ) * p.2⟩ : ℂ)‖ := norm_nonneg _
            apply sq_le_sq' (by linarith [h_norm_nonneg, h_nonneg]) round_err
        _ = 2 * (δ : ℝ)^2 := by
            rw [mul_pow, Real.sq_sqrt (by norm_num)]

    -- Sum the per-coefficient bounds
    calc Finset.sum F_in (fun k => ‖x.a k - c.a k‖^2)
        ≤ Finset.sum F_in (fun k => 2 * (δ : ℝ)^2) := by
          apply Finset.sum_le_sum
          intro k hk
          exact per_coeff_bound k hk
      _ = F_in.card * (2 * (δ : ℝ)^2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (IndexSetD d M).card * (2 * (δ : ℝ)^2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : F_in ⊆ IndexSetD d M := by
            intro k hk
            simp [F_in, Finset.mem_filter] at hk
            exact hk.2
          exact_mod_cast Finset.card_le_card this
      _ ≤ (2 * M + 1)^d * (2 * (δ : ℝ)^2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast card_IndexSetD_le
      _ ≤ ((ε : ℝ) / 2)^2 := rounding_bound_mesh_d ε M hM_ne

  -- OUTSIDE BOUND: Tail error ≤ (ε/2)²
  have outside_bound :
      Finset.sum F_out (fun k => ‖x.a k - c.a k‖^2)
      ≤ ((ε : ℝ) / 2)^2 := by
    -- Further split F_out into k=0 and tail
    let F_zero := F_out.filter (fun k => k = (fun _ => 0))
    let F_tail := F_out.filter (fun k => k ≠ (fun _ => 0))

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

    -- Zero mode contributes 0 (mean-zero condition)
    have zero_contrib : Finset.sum F_zero (fun k => ‖x.a k - c.a k‖^2) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp [F_zero, Finset.mem_filter] at hk
      have : k = (fun _ => 0) := hk.2
      subst this
      have hx0 : x.a (fun _ => 0) = 0 := hmean
      have hc0 : c.a (fun _ => 0) = 0 := center_zero (fun _ => 0) (by simp [IndexSetD])
      simp [hx0, hc0]

    -- Tail bound: k ∉ IndexSetD M and k ≠ 0 means k is in tail
    have tail_outside : ∀ k ∈ F_tail, tailR (M : ℝ) k := by
      intro k hk
      simp [F_tail, F_out, Finset.mem_filter] at hk
      have hk_notin : k ∉ IndexSetD d M := hk.1.2
      have hk_ne : k ≠ (fun _ => 0) := hk.2

      -- k ∉ IndexSetD M means k ∉ cube M or k = 0
      rw [mem_IndexSetD] at hk_notin
      push_neg at hk_notin

      -- Since k ≠ 0, we must have k ∉ cube M
      have k_not_in_cube : k ∉ cube d M := by
        intro h_in
        have h_zero := hk_notin h_in
        exact hk_ne h_zero

      -- k ∉ cube means ∃i, |kᵢ| > M
      rw [mem_cube] at k_not_in_cube
      simp only [not_forall, not_and] at k_not_in_cube
      obtain ⟨i, hi⟩ := k_not_in_cube

      -- This means (kᵢ)² > M², hence normSq k > M²
      unfold tailR normSq
      have : (M : ℝ)^2 < (k i : ℝ)^2 := by
        by_cases h_left : -(M : ℤ) ≤ k i
        · -- Left bound holds, so right bound fails: k i > M
          have h_right : ¬(k i ≤ (M : ℤ)) := hi h_left
          push_neg at h_right
          have : (M : ℝ) < (k i : ℝ) := by exact_mod_cast h_right
          nlinarith [sq_nonneg (M : ℝ), sq_nonneg (k i : ℝ), this]
        · -- Left bound fails: k i < -M
          push_neg at h_left
          have : (M : ℝ) < -(k i : ℝ) := by
            have : (k i : ℝ) < (-(M : ℤ) : ℝ) := by exact_mod_cast h_left
            have : (-(M : ℤ) : ℝ) = -(M : ℝ) := by norm_cast
            linarith
          nlinarith [sq_nonneg (M : ℝ), sq_nonneg (k i : ℝ)]
      calc (M : ℝ)^2 < (k i : ℝ)^2 := this
        _ ≤ ∑ j : Fin d, (k j : ℝ)^2 := by
            apply @Finset.single_le_sum (Fin d) ℝ _ _ (fun j => (k j : ℝ)^2) Finset.univ _
            · intro j _; exact sq_nonneg _
            · exact Finset.mem_univ i

    -- Tail bound: apply tail_bound_finitary_d
    have tail_contrib :
        Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2)
        ≤ ((ε : ℝ) / 2)^2 := by
      -- Centers vanish on tail, so error = ‖x.a k‖²
      have simplify : ∀ k ∈ F_tail, ‖x.a k - c.a k‖^2 = ‖x.a k‖^2 := by
        intro k hk
        simp [F_tail, F_out, Finset.mem_filter] at hk
        have : c.a k = 0 := center_zero k hk.1.2
        simp [this]

      -- Apply helper to convert F_tail to subtype finset
      obtain ⟨F_sub, h_sum⟩ := tail_finset_convert F_tail (M : ℝ) tail_outside
      -- Apply tail bound
      have tail_bound := tail_bound_finitary_d hH1 hM F_sub
      -- Use sum equality and bound
      calc Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2)
          = Finset.sum F_tail (fun k => ‖x.a k‖^2) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact simplify k hk
        _ = Finset.sum F_sub (fun g => ‖x.a g.val‖^2) := h_sum.symm
        _ ≤ (R : ℝ)^2 / (4 * Real.pi^2 * (M : ℝ)^2) := tail_bound
        _ ≤ ((ε : ℝ) / 2)^2 := @tail_bound_M_of_d d _ ε R hε hR

    calc Finset.sum F_out (fun k => ‖x.a k - c.a k‖^2)
        = Finset.sum F_zero (fun k => ‖x.a k - c.a k‖^2)
        + Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2) := sum_split_out
      _ = 0 + Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2) := by rw [zero_contrib]
      _ = Finset.sum F_tail (fun k => ‖x.a k - c.a k‖^2) := by ring
      _ ≤ ((ε : ℝ) / 2)^2 := tail_contrib

  -- COMBINE: inside + outside < ε²
  calc Finset.sum F (fun k => ‖x.a k - c.a k‖^2)
      = Finset.sum F_in (fun k => ‖x.a k - c.a k‖^2)
      + Finset.sum F_out (fun k => ‖x.a k - c.a k‖^2) := sum_split
    _ ≤ ((ε : ℝ) / 2)^2 + ((ε : ℝ) / 2)^2 := by linarith [inside_bound, outside_bound]
    _ = (ε : ℝ)^2 / 2 := by ring
    _ < (ε : ℝ)^2 := by linarith [sq_pos_of_pos hε]

end ℓ2ZD
