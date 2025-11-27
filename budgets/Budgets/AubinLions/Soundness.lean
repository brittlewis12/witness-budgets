import Budgets.AubinLions.TimeModulus
import Budgets.AubinLions.Integration
import Budgets.AubinLions.Witness
import Budgets.AubinLions.IntegrationHelpers
import Budgets.RellichKondrachovD.Soundness
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Quantitative Aubin–Lions: witness bookkeeping

The actual quantitative compactness theorem will live in this file.  While the
heavy analysis is still under construction, we include a few helper lemmas that
connect the core witness structures with the intended semantics (e.g. the
zero witness really evaluates to the zero sequence slice-by-slice).
-/

open scoped BigOperators

namespace AubinLions

open ℓ2ZD MeasureTheory Set IntegrationHelpers

/-- The constant factor in the integrated time-modulus bound.
This accounts for:
- Factor of 2 from triangle inequality ‖a+b‖² ≤ 2‖a‖² + 2‖b‖²
- The h1CubeBound factor from converting weighted H^{-1} norms to unweighted L² norms on the cube
For a generic dimension d and cube size M, this depends on the problem parameters.
Improving this would require additional structure relating time-modulus and
node-rounding errors (e.g., orthogonality). -/
noncomputable def timeModulusIntegralConstant {d : ℕ} [NeZero d] (M : ℕ) : ℝ :=
  ℓ2ZD.h1CubeBound d M

@[simp] lemma zeroWitness_slice {d : ℕ} {ε R : ℚ} {M : ℕ} {tg : TimeGrid}
    (i : Fin tg.segments) :
    SpaceTimeGridPoint.slice (zeroWitness d ε R M tg) i
      = evalSpaceSlice ε R M (ℓ2ZD.zeroGridPointD (d := d) ε R M) := by
  rfl

@[simp] lemma WitnessPkg.zero_point {d : ℕ} {ε R : ℚ}
    (tg : TimeGrid) (M : ℕ) :
    (zeroWitness d ε R M tg).coeffs = fun _ => ℓ2ZD.zeroGridPointD (d := d) ε R M := rfl

variable {d : ℕ}

section TimeQuantitative

variable [NeZero d]

lemma time_slice_error (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    {i j : Fin tg.segments} (hij : i ≤ j) :
    Finset.sum (ℓ2ZD.cube d (ℓ2ZD.M_of P.ε P.R))
        (fun k =>
          ‖(A.sampleAtNodes tg hcompat j).a k
              - (A.sampleAtNodes tg hcompat i).a k‖^2)
      ≤ ℓ2ZD.h1CubeBound d (ℓ2ZD.M_of P.ε P.R) *
        (P.S : ℝ)^2 *
          (((tg.node j : ℚ) : ℝ) - ((tg.node i : ℚ) : ℝ)) := by
  simpa using
    Admissible.sample_cube_diff_bound
      (d := d) (P := P) (A := A) tg hcompat hij
      (ℓ2ZD.M_of P.ε P.R)

end TimeQuantitative

section Phase4Soundness

variable [NeZero d]

/-- The boundary of a closed interval has measure zero (it's just two points). -/
lemma measure_frontier_Icc_eq_zero {a b : ℝ} :
    volume (frontier (Icc a b)) = 0 := by
  -- The frontier is {a, b} which has measure zero
  by_cases h : a ≤ b
  · rw [frontier_Icc h]
    exact measure_union_null (measure_singleton a) (measure_singleton b)
  · -- If a > b, then Icc a b is empty, so its frontier is empty
    have hab : b < a := not_le.mp h
    have : Icc a b = ∅ := Set.Icc_eq_empty (by simp [hab])
    simp [this, frontier_empty]

/-- Interior version: the triangle bound holds on the interior of slabs. -/
lemma pointwise_L2_error_triangle_interior
    {d : ℕ} [NeZero d] (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    (i : Fin tg.segments) (t : ℝ) (ht : t ∈ interior (TimeGrid.slabReal tg i))
    (F : Finset (ℓ2ZD.Lattice d)) :
    Finset.sum F (fun k =>
      ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2)
      ≤ 2 * Finset.sum F (fun k =>
          ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)
        + 2 * Finset.sum F (fun k =>
            ‖(A.sampleAtNodes tg hcompat i).a k -
              (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) := by
  -- On interior: witness(t) = grid(i), so bound is exact via triangle inequality
  have h_tri : ∀ k ∈ F,
      ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2
        ≤ 2 * ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2
          + 2 * ‖(A.sampleAtNodes tg hcompat i).a k -
                (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                  ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2 := by
    intro k _
    have hw : witnessAtTime' P A tg hcompat t =
        evalSpaceSlice P.ε P.R (ℓ2ZD.M_of P.ε P.R)
          ((nodeWitness P A tg hcompat).coeffs i) :=
      witnessAtTime'_eq_at_slab_interior P A tg hcompat i ht
    rw [hw]
    simp only [evalSpaceSlice, ℓ2ZD.gridToSeqD]
    exact @norm_sq_le_quad ℂ _
      ((curveExtended P A t).a k)
      ((A.sampleAtNodes tg hcompat i).a k)
      ((ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
        ((nodeWitness P A tg hcompat).coeffs i)).a k)
  -- Sum over F
  calc Finset.sum F (fun k =>
        ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2)
      ≤ Finset.sum F (fun k =>
          2 * ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2
            + 2 * ‖(A.sampleAtNodes tg hcompat i).a k -
                  (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                    ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) := by
        exact Finset.sum_le_sum h_tri
    _ = 2 * Finset.sum F (fun k =>
          ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)
        + 2 * Finset.sum F (fun k =>
            ‖(A.sampleAtNodes tg hcompat i).a k -
              (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib]

/-- A.E. version: the triangle bound holds almost everywhere on each slab. -/
lemma pointwise_L2_error_triangle_ae
    {d : ℕ} [NeZero d] (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    (i : Fin tg.segments)
    (F : Finset (ℓ2ZD.Lattice d)) :
    ∀ᵐ t ∂(volume.restrict (TimeGrid.slabReal tg i)),
      Finset.sum F (fun k =>
        ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2)
        ≤ 2 * Finset.sum F (fun k =>
            ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)
          + 2 * Finset.sum F (fun k =>
              ‖(A.sampleAtNodes tg hcompat i).a k -
                (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                  ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) := by
  -- Use a.e. equality: witness = grid a.e. on the slab
  have h_witness_eq := witnessAtTime'_ae_eq_on_slab P A tg hcompat i
  -- Rewrite witness to grid using a.e. equality
  filter_upwards [h_witness_eq] with t ht_eq
  -- Now witness = evalSpaceSlice ... = gridToSeqD ... (since evalSpaceSlice is defined as gridToSeqD)
  have witness_eq_grid : witnessAtTime' P A tg hcompat t =
      ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
        ((nodeWitness P A tg hcompat).coeffs i) := by
    simpa [evalSpaceSlice] using ht_eq
  -- Apply triangle inequality coefficient-wise
  calc Finset.sum F (fun k =>
        ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2)
      = Finset.sum F (fun k =>
          ‖(curveExtended P A t).a k -
            (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
              ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) := by
        congr 1; ext k; congr 1; rw [witness_eq_grid]
    _ ≤ 2 * Finset.sum F (fun k =>
          ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)
        + 2 * Finset.sum F (fun k =>
            ‖(A.sampleAtNodes tg hcompat i).a k -
              (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) := by
      -- Triangle inequality on each coefficient
      have h_tri : ∀ k ∈ F,
          ‖(curveExtended P A t).a k -
            (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
              ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2
            ≤ 2 * ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2
              + 2 * ‖(A.sampleAtNodes tg hcompat i).a k -
                    (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                      ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2 := by
        intro k _
        exact @norm_sq_le_quad ℂ _ _ _ _
      calc Finset.sum F (fun k =>
              ‖(curveExtended P A t).a k -
                (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                  ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2)
          ≤ Finset.sum F (fun k =>
              2 * ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2
                + 2 * ‖(A.sampleAtNodes tg hcompat i).a k -
                      (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                        ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) := by
            exact Finset.sum_le_sum h_tri
        _ = 2 * Finset.sum F (fun k =>
              ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)
            + 2 * Finset.sum F (fun k =>
                ‖(A.sampleAtNodes tg hcompat i).a k -
                  (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                    ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) := by
          simp only [← Finset.mul_sum, Finset.sum_add_distrib]

/-- Integrating the pointwise triangle inequality over slab i gives:
    ∫_{slab i} ‖u(t) - w(t)‖² ≤ S²·mesh²/2 + 2·mesh·‖u(t_i) - grid_i‖² -/
lemma slab_L2_error_bound
    {d : ℕ} [NeZero d] (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    (i : Fin tg.segments)
    (F : Finset (ℓ2ZD.Lattice d))
    (hsubset :
      ∀ k ∈ F, k ∈ ℓ2ZD.cube d (ℓ2ZD.M_of P.ε P.R)) :
    (∫ t in TimeGrid.slabReal tg i,
      Finset.sum F (fun k =>
        ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2) : ℝ)
      ≤ (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) * (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2
        + 2 * ((tg.mesh : ℚ) : ℝ) *
          Finset.sum F (fun k =>
            ‖(A.sampleAtNodes tg hcompat i).a k -
              (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) := by
  -- Define integrands
  let f := fun t : ℝ =>
    Finset.sum F (fun k =>
      ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2)
  let g := fun t : ℝ =>
    Finset.sum F (fun k =>
      ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)
  let c : ℝ :=
    Finset.sum F (fun k =>
      ‖(A.sampleAtNodes tg hcompat i).a k -
        (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
          ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2)

  -- A.E. triangle inequality
  have h_ae_bound : ∀ᵐ t ∂(volume.restrict (TimeGrid.slabReal tg i)),
      f t ≤ 2 * g t + 2 * c := by
    have := pointwise_L2_error_triangle_ae P A tg hcompat i F
    filter_upwards [this] with t ht
    exact ht

  -- Integrability
  have hf_int : IntegrableOn f (TimeGrid.slabReal tg i) volume := by
    -- f is bounded by triangle inequality using witness and curve bounds
    have hf_bound : ∃ C : ℝ, ∀ t ∈ TimeGrid.slabReal tg i, |f t| ≤ C := by
      -- By triangle inequality: ‖a - b‖² ≤ 2‖a‖² + 2‖b‖²
      -- So f(t) = ∑ ‖curve(t) - witness(t)‖² ≤ 2∑‖curve(t)‖² + 2∑‖witness(t)‖²
      -- Curve is bounded by R (from InH1Ball), witness is bounded by 2(R² + ε²)
      use 2 * ((P.R : ℝ)^2) + 2 * (2 * ((P.R : ℝ)^2 + (P.ε : ℝ)^2))
      intro t ht
      have hf_nonneg : 0 ≤ f t := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      rw [abs_of_nonneg hf_nonneg]
      -- Bound each term by triangle inequality
      calc f t
          = Finset.sum F (fun k =>
              ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2) := rfl
        _ ≤ Finset.sum F (fun k =>
              2 * ‖(curveExtended P A t).a k‖^2 + 2 * ‖(witnessAtTime' P A tg hcompat t).a k‖^2) := by
            apply Finset.sum_le_sum
            intro k hk
            exact norm_sq_diff_le ((curveExtended P A t).a k) ((witnessAtTime' P A tg hcompat t).a k)
        _ = 2 * Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2)
            + 2 * Finset.sum F (fun k => ‖(witnessAtTime' P A tg hcompat t).a k‖^2) := by
            simp only [← Finset.mul_sum, Finset.sum_add_distrib]
        _ ≤ 2 * (P.R : ℝ)^2 + 2 * (2 * ((P.R : ℝ)^2 + (P.ε : ℝ)^2)) := by
            -- Bound curve using InH1Ball
            have h_curve_bound : Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2) ≤ (P.R : ℝ)^2 := by
              have h_slab_in_icc := slab_mem_interval tg hcompat i t ht
              have h_curve := A.inH1_curve ⟨t, h_slab_in_icc⟩
              have h_h1 := h_curve F
              unfold InH1Ball at h_h1
              have h_le : Finset.sum F (fun k => ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2) ≤
                  Finset.sum F (fun k => h1Weight k * ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2) := by
                apply Finset.sum_le_sum
                intro k _
                have h_h1_ge : 1 ≤ h1Weight k := h1Weight_ge_one k
                calc ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2
                    = 1 * ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2 := by ring
                  _ ≤ h1Weight k * ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2 := by
                      apply mul_le_mul_of_nonneg_right h_h1_ge (sq_nonneg _)
              calc Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2)
                  = Finset.sum F (fun k => ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2) := by
                    congr 1; ext k
                    simp [curveExtended, h_slab_in_icc]
                _ ≤ Finset.sum F (fun k => h1Weight k * ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2) := h_le
                _ ≤ (P.R : ℝ)^2 := h_h1
            -- Bound witness using direct bound lemma (avoids existential extraction)
            have h_witness_bound := witnessAtTime'_sum_bound P A tg hcompat F t
            linarith [h_curve_bound, h_witness_bound]
    -- Use integrability helper
    have hf_aemeas : AEStronglyMeasurable f (volume.restrict (TimeGrid.slabReal tg i)) := by
      -- f is a finite sum of AE measurable functions
      -- Build measurability from each summand
      have h_each : ∀ k ∈ F, AEStronglyMeasurable (fun t =>
        ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2) volume := by
        intro k _
        have hc := curveExtended_coeff_aestronglyMeasurable P A k
        have hw := witnessAtTime'_coeff_aestronglyMeasurable P A tg hcompat k
        exact ((hc.sub hw).norm.pow 2)
      -- Sum of AE measurable functions is AE measurable
      have h_sum_full : AEStronglyMeasurable f volume := by
        show AEStronglyMeasurable (fun t => ∑ k ∈ F,
          ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2) volume
        have := Finset.aestronglyMeasurable_sum F h_each
        convert this using 1
        · funext x; simp
      -- Then restrict to slab
      exact h_sum_full.mono_measure (Measure.restrict_le_self)
    have h_finite_measure : volume (TimeGrid.slabReal tg i) < ⊤ := by
      unfold TimeGrid.slabReal
      exact measure_Icc_lt_top
    have h_meas : MeasurableSet (TimeGrid.slabReal tg i) := by
      unfold TimeGrid.slabReal
      exact measurableSet_Icc
    exact integrable_of_aestronglyMeasurable_bounded hf_aemeas h_meas hf_bound h_finite_measure

  have hg_int_base : IntegrableOn g (TimeGrid.slabReal tg i) volume := by
    -- same argument as for f, but simpler
    have hg_bound : ∃ C : ℝ, ∀ t ∈ TimeGrid.slabReal tg i, |g t| ≤ C := by
      use 2 * (P.R : ℝ)^2 + 2 * (P.R : ℝ)^2
      intro t ht
      have hg_nonneg : 0 ≤ g t := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      rw [abs_of_nonneg hg_nonneg]
      calc g t
          = Finset.sum F (fun k =>
              ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) := rfl
        _ ≤ Finset.sum F (fun k =>
              2 * ‖(curveExtended P A t).a k‖^2 +
                2 * ‖(A.sampleAtNodes tg hcompat i).a k‖^2) := by
            apply Finset.sum_le_sum
            intro k _
            exact norm_sq_diff_le ((curveExtended P A t).a k) ((A.sampleAtNodes tg hcompat i).a k)
        _ = 2 * Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2)
            + 2 * Finset.sum F (fun k => ‖(A.sampleAtNodes tg hcompat i).a k‖^2) := by
            simp only [← Finset.mul_sum, Finset.sum_add_distrib]
        _ ≤ 2 * (P.R : ℝ)^2 + 2 * (P.R : ℝ)^2 := by
            have h_curve : Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2) ≤ (P.R : ℝ)^2 := by
              have h_slab_in_icc := slab_mem_interval tg hcompat i t ht
              have h_curve := A.inH1_curve ⟨t, h_slab_in_icc⟩ F
              unfold InH1Ball at h_curve
              have h_le : Finset.sum F (fun k => ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2) ≤
                  Finset.sum F (fun k => h1Weight k * ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2) := by
                apply Finset.sum_le_sum
                intro k _
                have h_ge : 1 ≤ h1Weight k := h1Weight_ge_one k
                calc ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2
                    = 1 * ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2 := by ring
                  _ ≤ h1Weight k * ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2 := by
                        apply mul_le_mul_of_nonneg_right h_ge (sq_nonneg _)
              have : Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2)
                  = Finset.sum F (fun k => ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2) := by
                congr 1; ext k; simp [curveExtended, h_slab_in_icc]
              simpa [this] using le_trans h_le h_curve
            have h_sample :
                Finset.sum F (fun k => ‖(A.sampleAtNodes tg hcompat i).a k‖^2) ≤ (P.R : ℝ)^2 := by
              have := A.sampleAtNodes_inH1 tg hcompat i F
              unfold InH1Ball at this
              have h_le : Finset.sum F (fun k => ‖(A.sampleAtNodes tg hcompat i).a k‖^2) ≤
                  Finset.sum F (fun k => h1Weight k * ‖(A.sampleAtNodes tg hcompat i).a k‖^2) := by
                apply Finset.sum_le_sum
                intro k _
                have h_ge : 1 ≤ h1Weight k := h1Weight_ge_one k
                calc ‖(A.sampleAtNodes tg hcompat i).a k‖^2
                    = 1 * ‖(A.sampleAtNodes tg hcompat i).a k‖^2 := by ring
                  _ ≤ h1Weight k * ‖(A.sampleAtNodes tg hcompat i).a k‖^2 := by
                        apply mul_le_mul_of_nonneg_right h_ge (sq_nonneg _)
              exact le_trans h_le this
            linarith [h_curve, h_sample]
    have hg_aemeas : AEStronglyMeasurable g (volume.restrict (TimeGrid.slabReal tg i)) := by
      have h_each : ∀ k ∈ F, AEStronglyMeasurable (fun t =>
        ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) volume := by
        intro k _
        have hc := curveExtended_coeff_aestronglyMeasurable P A k
        have hs := (aestronglyMeasurable_const :
          AEStronglyMeasurable (fun _ : ℝ => (A.sampleAtNodes tg hcompat i).a k) volume)
        exact ((hc.sub hs).norm.pow 2)
      have h_sum : AEStronglyMeasurable g volume := by
        show AEStronglyMeasurable (fun t => ∑ k ∈ F,
          ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) volume
        have := Finset.aestronglyMeasurable_sum F h_each
        convert this using 1
        funext t
        simp
      exact h_sum.mono_measure (Measure.restrict_le_self)
    have hfinite : volume (TimeGrid.slabReal tg i) < ⊤ := by
      unfold TimeGrid.slabReal; exact measure_Icc_lt_top
    have hmeas : MeasurableSet (TimeGrid.slabReal tg i) := by
      unfold TimeGrid.slabReal; exact measurableSet_Icc
    exact integrable_of_aestronglyMeasurable_bounded hg_aemeas hmeas hg_bound hfinite

  have hg_bound_int : IntegrableOn (fun t => 2 * g t + 2 * c) (TimeGrid.slabReal tg i) volume := by
    -- Constant is integrable
    have hc_int : IntegrableOn (fun _ => 2 * c) (TimeGrid.slabReal tg i) volume := by
      unfold TimeGrid.slabReal
      exact integrableOn_const (measure_Icc_lt_top.ne)
    -- g is bounded and measurable, hence integrable
    have hg_int : IntegrableOn (fun t => 2 * g t) (TimeGrid.slabReal tg i) volume := by
      have hg_bound : ∃ C : ℝ, ∀ t ∈ TimeGrid.slabReal tg i, |g t| ≤ C := by
        -- g(t) = ∑ ‖curve(t) - sample_i‖² ≤ 2∑‖curve(t)‖² + 2∑‖sample_i‖²
        use 2 * ((P.R : ℝ)^2) + 2 * ((P.R : ℝ)^2)
        intro t ht
        have hg_nonneg : 0 ≤ g t := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        rw [abs_of_nonneg hg_nonneg]
        calc g t
            = Finset.sum F (fun k =>
                ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) := rfl
          _ ≤ Finset.sum F (fun k =>
                2 * ‖(curveExtended P A t).a k‖^2 + 2 * ‖(A.sampleAtNodes tg hcompat i).a k‖^2) := by
              apply Finset.sum_le_sum
              intro k _
              exact norm_sq_diff_le ((curveExtended P A t).a k) ((A.sampleAtNodes tg hcompat i).a k)
          _ = 2 * Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2)
              + 2 * Finset.sum F (fun k => ‖(A.sampleAtNodes tg hcompat i).a k‖^2) := by
              simp only [← Finset.mul_sum, Finset.sum_add_distrib]
          _ ≤ 2 * (P.R : ℝ)^2 + 2 * (P.R : ℝ)^2 := by
              have h_curve : Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2) ≤ (P.R : ℝ)^2 := by
                have h_slab_in_icc := slab_mem_interval tg hcompat i t ht
                have h_h1 := A.inH1_curve ⟨t, h_slab_in_icc⟩ F
                unfold InH1Ball at h_h1
                have h_le : Finset.sum F (fun k => ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2) ≤
                    Finset.sum F (fun k => h1Weight k * ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2) := by
                  apply Finset.sum_le_sum
                  intro k _
                  have h_ge : 1 ≤ h1Weight k := h1Weight_ge_one k
                  calc ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2
                      = 1 * ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2 := by ring
                    _ ≤ h1Weight k * ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2 := by
                        apply mul_le_mul_of_nonneg_right h_ge (sq_nonneg _)
                calc Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2)
                    = Finset.sum F (fun k => ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2) := by
                      congr 1; ext k; simp [curveExtended, h_slab_in_icc]
                  _ ≤ Finset.sum F (fun k => h1Weight k * ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2) := h_le
                  _ ≤ (P.R : ℝ)^2 := h_h1
              have h_sample : Finset.sum F (fun k => ‖(A.sampleAtNodes tg hcompat i).a k‖^2) ≤ (P.R : ℝ)^2 := by
                have h_h1 := A.sampleAtNodes_inH1 tg hcompat i F
                unfold InH1Ball at h_h1
                have h_le : Finset.sum F (fun k => ‖(A.sampleAtNodes tg hcompat i).a k‖^2) ≤
                    Finset.sum F (fun k => h1Weight k * ‖(A.sampleAtNodes tg hcompat i).a k‖^2) := by
                  apply Finset.sum_le_sum
                  intro k _
                  have h_ge : 1 ≤ h1Weight k := h1Weight_ge_one k
                  calc ‖(A.sampleAtNodes tg hcompat i).a k‖^2
                      = 1 * ‖(A.sampleAtNodes tg hcompat i).a k‖^2 := by ring
                    _ ≤ h1Weight k * ‖(A.sampleAtNodes tg hcompat i).a k‖^2 := by
                        apply mul_le_mul_of_nonneg_right h_ge (sq_nonneg _)
                linarith [h_le, h_h1]
              linarith [h_curve, h_sample]
      have hg_meas : AEStronglyMeasurable g (volume.restrict (TimeGrid.slabReal tg i)) := by
        -- g is a finite sum where each term is ‖curve(k) - sample(k)‖²
        -- Build measurability from each summand
        have h_each : ∀ k ∈ F, AEStronglyMeasurable (fun t =>
          ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) volume := by
          intro k _
          have hc := curveExtended_coeff_aestronglyMeasurable P A k
          -- sample is constant, so it's trivially AE measurable
          have hsample := (aestronglyMeasurable_const : AEStronglyMeasurable
            (fun _ : ℝ => (A.sampleAtNodes tg hcompat i).a k) volume)
          exact ((hc.sub hsample).norm.pow 2)
        -- Sum of AE measurable functions is AE measurable
        have h_sum_full : AEStronglyMeasurable g volume := by
          show AEStronglyMeasurable (fun t => ∑ k ∈ F,
            ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) volume
          have := Finset.aestronglyMeasurable_sum F h_each
          convert this using 1
          · funext x; simp
        exact h_sum_full.mono_measure (Measure.restrict_le_self)
      have h_finite : volume (TimeGrid.slabReal tg i) < ⊤ := by
        unfold TimeGrid.slabReal; exact measure_Icc_lt_top
      have h_meas_slab : MeasurableSet (TimeGrid.slabReal tg i) := by
        unfold TimeGrid.slabReal; exact measurableSet_Icc
      have hg_int0 := integrable_of_aestronglyMeasurable_bounded hg_meas h_meas_slab hg_bound h_finite
      exact hg_int0.const_mul 2
    -- Sum of integrable functions is integrable
    exact hg_int.add hc_int

  -- Apply monotone integration
  have h_integral_bound : ∫ t in TimeGrid.slabReal tg i, f t
      ≤ ∫ t in TimeGrid.slabReal tg i, (2 * g t + 2 * c) := by
    -- We have: f ≤ 2g + 2c a.e. on the slab (h_ae_bound)
    -- We need: ∫ f ≤ ∫ (2g + 2c) on the slab
    -- Standard: monotone integration with a.e. bounds
    have h_meas : MeasurableSet (TimeGrid.slabReal tg i) := by
      unfold TimeGrid.slabReal; exact measurableSet_Icc
    have h_ae_bound' : ∀ᵐ t ∂volume, t ∈ TimeGrid.slabReal tg i → f t ≤ 2 * g t + 2 * c := by
      exact ae_restrict_iff' h_meas |>.mp h_ae_bound
    exact setIntegral_mono_on_ae hf_int hg_bound_int h_meas h_ae_bound'

  -- Expand and simplify the RHS
  have h_const_bound : ∫ _ in TimeGrid.slabReal tg i, c = ((tg.mesh : ℚ) : ℝ) * c := by
    exact integral_const_slab tg i c

  have h_weighted_bound := slab_integral_time_modulus_bound P A tg hcompat i F

  calc ∫ t in TimeGrid.slabReal tg i, f t
      ≤ ∫ t in TimeGrid.slabReal tg i, (2 * g t + 2 * c) := h_integral_bound
    _ = (∫ t in TimeGrid.slabReal tg i, (2 * g t)) + (∫ t in TimeGrid.slabReal tg i, (2 * c)) := by
        -- Split integral of sum into sum of integrals
        have hg_int2 : IntegrableOn (fun t => 2 * g t) (TimeGrid.slabReal tg i) volume := by
          have hg_bound : ∃ C : ℝ, ∀ t ∈ TimeGrid.slabReal tg i, |g t| ≤ C := by
            use 2 * ((P.R : ℝ)^2) + 2 * ((P.R : ℝ)^2)
            intro t ht
            have hg_nonneg : 0 ≤ g t := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
            rw [abs_of_nonneg hg_nonneg]
            calc g t
                = Finset.sum F (fun k =>
                    ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) := rfl
              _ ≤ 2 * Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2)
                  + 2 * Finset.sum F (fun k => ‖(A.sampleAtNodes tg hcompat i).a k‖^2) := by
                  calc Finset.sum F (fun k =>
                        ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)
                      ≤ Finset.sum F (fun k =>
                          2 * ‖(curveExtended P A t).a k‖^2 + 2 * ‖(A.sampleAtNodes tg hcompat i).a k‖^2) := by
                        apply Finset.sum_le_sum
                        intro k _
                        exact norm_sq_diff_le ((curveExtended P A t).a k) ((A.sampleAtNodes tg hcompat i).a k)
                    _ = 2 * Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2)
                        + 2 * Finset.sum F (fun k => ‖(A.sampleAtNodes tg hcompat i).a k‖^2) := by
                        simp only [← Finset.mul_sum, Finset.sum_add_distrib]
              _ ≤ 2 * (P.R : ℝ)^2 + 2 * (P.R : ℝ)^2 := by
                  have h_curve : Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2) ≤ (P.R : ℝ)^2 := by
                    have h_slab_in_icc := slab_mem_interval tg hcompat i t ht
                    have h_h1 := A.inH1_curve ⟨t, h_slab_in_icc⟩ F
                    unfold InH1Ball at h_h1
                    have h_le : Finset.sum F (fun k => ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2) ≤
                        Finset.sum F (fun k => h1Weight k * ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2) := by
                      apply Finset.sum_le_sum
                      intro k _
                      have h_ge : 1 ≤ h1Weight k := h1Weight_ge_one k
                      calc ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2
                          = 1 * ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2 := by ring
                        _ ≤ h1Weight k * ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2 := by
                            apply mul_le_mul_of_nonneg_right h_ge (sq_nonneg _)
                    calc Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2)
                        = Finset.sum F (fun k => ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2) := by
                          congr 1; ext k; simp [curveExtended, h_slab_in_icc]
                      _ ≤ Finset.sum F (fun k => h1Weight k * ‖(A.curve ⟨t, h_slab_in_icc⟩).a k‖^2) := h_le
                      _ ≤ (P.R : ℝ)^2 := h_h1
                  have h_sample : Finset.sum F (fun k => ‖(A.sampleAtNodes tg hcompat i).a k‖^2) ≤ (P.R : ℝ)^2 := by
                    have h_h1 := A.sampleAtNodes_inH1 tg hcompat i F
                    unfold InH1Ball at h_h1
                    have h_le : Finset.sum F (fun k => ‖(A.sampleAtNodes tg hcompat i).a k‖^2) ≤
                        Finset.sum F (fun k => h1Weight k * ‖(A.sampleAtNodes tg hcompat i).a k‖^2) := by
                      apply Finset.sum_le_sum
                      intro k _
                      have h_ge : 1 ≤ h1Weight k := h1Weight_ge_one k
                      calc ‖(A.sampleAtNodes tg hcompat i).a k‖^2
                          = 1 * ‖(A.sampleAtNodes tg hcompat i).a k‖^2 := by ring
                        _ ≤ h1Weight k * ‖(A.sampleAtNodes tg hcompat i).a k‖^2 := by
                            apply mul_le_mul_of_nonneg_right h_ge (sq_nonneg _)
                    linarith [h_le, h_h1]
                  linarith [h_curve, h_sample]
          have hg_meas : AEStronglyMeasurable g (volume.restrict (TimeGrid.slabReal tg i)) := by
            -- g is a finite sum where each term is ‖curve(k) - sample(k)‖²
            -- Build measurability from each summand
            have h_each : ∀ k ∈ F, AEStronglyMeasurable (fun t =>
              ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) volume := by
              intro k _
              have hc := curveExtended_coeff_aestronglyMeasurable P A k
              -- sample is constant, so it's trivially AE measurable
              have hsample := (aestronglyMeasurable_const : AEStronglyMeasurable
                (fun _ : ℝ => (A.sampleAtNodes tg hcompat i).a k) volume)
              exact ((hc.sub hsample).norm.pow 2)
            -- Sum of AE measurable functions is AE measurable
            have h_sum_full : AEStronglyMeasurable g volume := by
              show AEStronglyMeasurable (fun t => ∑ k ∈ F,
                ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) volume
              have := Finset.aestronglyMeasurable_sum F h_each
              convert this using 1
              · funext x; simp
            exact h_sum_full.mono_measure (Measure.restrict_le_self)
          have h_finite : volume (TimeGrid.slabReal tg i) < ⊤ := by
            unfold TimeGrid.slabReal; exact measure_Icc_lt_top
          have h_meas_slab2 : MeasurableSet (TimeGrid.slabReal tg i) := by
            unfold TimeGrid.slabReal; exact measurableSet_Icc
          have hg_int0 := integrable_of_aestronglyMeasurable_bounded hg_meas h_meas_slab2 hg_bound h_finite
          exact hg_int0.const_mul 2
        have hc_int2 : IntegrableOn (fun _ => 2 * c) (TimeGrid.slabReal tg i) volume := by
          unfold TimeGrid.slabReal
          exact integrableOn_const (measure_Icc_lt_top.ne)
        -- Split ∫(2g + 2c) = ∫2g + ∫2c using integral_add
        -- Then pull out constants to get 2 * ∫g + 2*mesh*c
        have h_int_two :
            ∫ t in TimeGrid.slabReal tg i, (2 * g t)
              = 2 * ∫ t in TimeGrid.slabReal tg i, g t := by
          have := integral_const_mul (μ := volume.restrict (TimeGrid.slabReal tg i))
            (r := (2 : ℝ)) (fun t => g t)
          simpa using this
        have h_int_const :
            ∫ _ in TimeGrid.slabReal tg i, (2 * c)
              = 2 * ((tg.mesh : ℚ) : ℝ) * c := by
          have h_base := integral_const_slab tg i (2 * c)
          calc ∫ _ in TimeGrid.slabReal tg i, (2 * c)
              = ((tg.mesh : ℚ) : ℝ) * (2 * c) := h_base
            _ = 2 * ((tg.mesh : ℚ) : ℝ) * c := by ring
        rw [integral_add hg_int2 hc_int2, h_int_two, h_int_const]
    _ ≤ 2 * ((timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) * (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2 / 2)
        + 2 * ((tg.mesh : ℚ) : ℝ) * c := by
        -- Bound the integral of g using the weighted time-modulus bound
        -- First: convert unweighted sum to weighted sum using cube_sum_sq_le
        have h_pointwise_convert :
            ∀ t : ℝ,
              g t ≤ (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) *
                Finset.sum F (fun k =>
                  ℓ2ZD.hminusWeight k *
                    ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) := by
          intro t
          have := ℓ2ZD.sum_sq_le_hminus (d := d)
            (M := ℓ2ZD.M_of P.ε P.R) F
            (fun k =>
              (curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k) hsubset
          simpa [timeModulusIntegralConstant, g]
            using this
        have h_ae_convert :
            ∀ᵐ t ∂(volume.restrict (TimeGrid.slabReal tg i)),
              g t ≤ (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) *
                Finset.sum F (fun k =>
                  ℓ2ZD.hminusWeight k *
                    ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) := by
          -- No filtering needed since h_pointwise_convert holds for all t
          filter_upwards with t
          exact h_pointwise_convert t
        have h_meas_slab : MeasurableSet (TimeGrid.slabReal tg i) := by
          unfold TimeGrid.slabReal; exact measurableSet_Icc
        have hg_le_bound :
            ∫ t in TimeGrid.slabReal tg i, g t
              ≤ (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) *
                ∫ t in TimeGrid.slabReal tg i,
                  Finset.sum F (fun k =>
                    ℓ2ZD.hminusWeight k *
                      ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) := by
          have h_rhs_int :
              IntegrableOn
                (fun t =>
                  Finset.sum F (fun k =>
                    ℓ2ZD.hminusWeight k *
                      ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2))
                (TimeGrid.slabReal tg i) volume := by
            have hf_meas :
                AEStronglyMeasurable
                  (fun t =>
                    Finset.sum F (fun k =>
                      ℓ2ZD.hminusWeight k *
                        ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2))
                  (volume.restrict (TimeGrid.slabReal tg i)) := by
              have h_each : ∀ k ∈ F,
                  AEStronglyMeasurable
                    (fun t =>
                      ℓ2ZD.hminusWeight k *
                        ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)
                    volume := by
                intro k hk
                have hc := curveExtended_coeff_aestronglyMeasurable P A k
                have hs :=
                  (aestronglyMeasurable_const :
                    AEStronglyMeasurable
                      (fun _ : ℝ => (A.sampleAtNodes tg hcompat i).a k) volume)
                exact ((hc.sub hs).norm.pow 2).const_mul _
              have h_sum_full : AEStronglyMeasurable
                  (fun t => Finset.sum F (fun k =>
                    ℓ2ZD.hminusWeight k *
                      ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2))
                  volume := by
                have := Finset.aestronglyMeasurable_sum F h_each
                convert this using 1
                funext t
                simp
              exact h_sum_full.mono_measure (Measure.restrict_le_self)
            have h_fin : volume (TimeGrid.slabReal tg i) < ⊤ := by
              unfold TimeGrid.slabReal; exact measure_Icc_lt_top
            have h_bound :
                ∃ C, ∀ t ∈ TimeGrid.slabReal tg i,
                    |Finset.sum F (fun k =>
                      ℓ2ZD.hminusWeight k *
                        ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)| ≤ C := by
              use (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)
              intro t ht
              have h_nonneg :
                  0 ≤ Finset.sum F (fun k =>
                    ℓ2ZD.hminusWeight k *
                      ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) :=
                Finset.sum_nonneg (fun k _ =>
                  mul_nonneg (ℓ2ZD.hminusWeight_nonneg k) (sq_nonneg _))
              rw [abs_of_nonneg h_nonneg]
              have h_time_bound := pointwise_time_modulus_bound P A tg hcompat i t ht F
              have h_mesh_le := time_diff_le_mesh tg i t ht
              calc Finset.sum F (fun k =>
                    ℓ2ZD.hminusWeight k *
                      ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)
                  ≤ (P.S : ℝ)^2 * |t - ((tg.node i : ℚ) : ℝ)| := by
                    have := h_time_bound
                    simpa [curveExtended_coeff_eq_on_slab P A tg hcompat i t ht] using this
                _ ≤ (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ) := by
                    apply mul_le_mul_of_nonneg_left h_mesh_le (sq_nonneg _)
            exact integrable_of_aestronglyMeasurable_bounded hf_meas h_meas_slab
              h_bound h_fin
          -- Now pull out the constant using integral_const_mul
          have hconst_nonneg :
              0 ≤ (timeModulusIntegralConstant (d := d)
                (ℓ2ZD.M_of P.ε P.R) : ℝ) := by
            exact le_of_lt (ℓ2ZD.h1CubeBound_pos _ _)
          have h_ae' :
              ∀ᵐ t ∂(volume.restrict (TimeGrid.slabReal tg i)),
                  g t ≤ (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) *
                    Finset.sum F (fun k =>
                      ℓ2ZD.hminusWeight k *
                        ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) := by
            filter_upwards with t
            exact h_pointwise_convert t
          have h_rhs_int' :
              IntegrableOn
                (fun t =>
                  (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) *
                    Finset.sum F (fun k =>
                      ℓ2ZD.hminusWeight k *
                        ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2))
                (TimeGrid.slabReal tg i) volume :=
            (h_rhs_int.const_mul (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R)))
          have h_int_mono := setIntegral_mono_on_ae hg_int_base h_rhs_int' h_meas_slab
            (by filter_upwards with t ht; exact h_pointwise_convert t)
          -- Pull constant out
          have h_pull_const :
              ∫ t in TimeGrid.slabReal tg i,
                (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) *
                  Finset.sum F (fun k =>
                    ℓ2ZD.hminusWeight k *
                      ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)
              = (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) *
                  ∫ t in TimeGrid.slabReal tg i,
                    Finset.sum F (fun k =>
                      ℓ2ZD.hminusWeight k *
                        ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) := by
            have := integral_const_mul (μ := volume.restrict (TimeGrid.slabReal tg i))
              (r := (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ))
              (fun t => Finset.sum F (fun k =>
                ℓ2ZD.hminusWeight k *
                  ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2))
            simpa using this
          calc ∫ t in TimeGrid.slabReal tg i, g t
              ≤ ∫ t in TimeGrid.slabReal tg i,
                  (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) *
                    Finset.sum F (fun k =>
                      ℓ2ZD.hminusWeight k *
                        ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) :=
                h_int_mono
            _ = (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) *
                  ∫ t in TimeGrid.slabReal tg i,
                    Finset.sum F (fun k =>
                      ℓ2ZD.hminusWeight k *
                        ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2) :=
              h_pull_const
        have h_weighted := slab_integral_time_modulus_bound P A tg hcompat i F
        -- h_weighted : ∫(weighted sum) ≤ S² * mesh² / 2

        have hconst_nonneg : 0 ≤ (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) := by
          unfold timeModulusIntegralConstant
          exact le_of_lt (ℓ2ZD.h1CubeBound_pos d (ℓ2ZD.M_of P.ε P.R))

        have hfinal : (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) * ∫ t in TimeGrid.slabReal tg i,
            Finset.sum F (fun k => ℓ2ZD.hminusWeight k *
              ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)
          ≤ (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) * ((P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2 / 2) := by
          exact mul_le_mul_of_nonneg_left h_weighted hconst_nonneg

        have hconst :
            (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) *
              ((P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2 / 2)
            = (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) *
                (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2 / 2 := by
          ring

        have h_bound_2g : 2 * ∫ t in TimeGrid.slabReal tg i, g t
            ≤ (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) * (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2 := by
          calc 2 * ∫ t in TimeGrid.slabReal tg i, g t
              ≤ 2 * ((timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) *
                      ∫ t in TimeGrid.slabReal tg i,
                        Finset.sum F (fun k =>
                          ℓ2ZD.hminusWeight k *
                            ‖(curveExtended P A t).a k - (A.sampleAtNodes tg hcompat i).a k‖^2)) := by
                apply mul_le_mul_of_nonneg_left hg_le_bound
                norm_num
            _ ≤ 2 * ((timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) *
                      ((P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2 / 2)) := by
                apply mul_le_mul_of_nonneg_left
                · exact mul_le_mul_of_nonneg_left h_weighted hconst_nonneg
                · norm_num
            _ = (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) * (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2 := by
                ring

        have h_int_const_2c : ∫ t in TimeGrid.slabReal tg i, 2 * c = 2 * ((tg.mesh : ℚ) : ℝ) * c := by
          calc ∫ t in TimeGrid.slabReal tg i, 2 * c
              = 2 * ∫ t in TimeGrid.slabReal tg i, c := by
                have := integral_const_mul (μ := volume.restrict (TimeGrid.slabReal tg i)) (r := (2 : ℝ)) (fun _ => c)
                simpa using this
            _ = 2 * (((tg.mesh : ℚ) : ℝ) * c) := by rw [h_const_bound]
            _ = 2 * ((tg.mesh : ℚ) : ℝ) * c := by ring

        have h_int_2g : ∫ t in TimeGrid.slabReal tg i, 2 * g t = 2 * ∫ t in TimeGrid.slabReal tg i, g t := by
          have := integral_const_mul (μ := volume.restrict (TimeGrid.slabReal tg i)) (r := (2 : ℝ)) (fun t => g t)
          simpa using this

        linarith
    _ = (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) * (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2
        + 2 * ((tg.mesh : ℚ) : ℝ) * c := by
        ring

/-- Summing over all slabs using the partition property:
    ∫_{0}^{T} ‖u(t) - w(t)‖² = Σ_i ∫_{slab i} ‖u(t) - w(t)‖² -/
lemma total_L2_error_bound
    {d : ℕ} [NeZero d] (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    (F : Finset (ℓ2ZD.Lattice d))
    (hsubset : ∀ k ∈ F, k ∈ ℓ2ZD.cube d (ℓ2ZD.M_of P.ε P.R)) :
    (∫ t in Set.Icc (0 : ℝ) (P.horizon : ℝ),
      Finset.sum F (fun k =>
        ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2) : ℝ)
      ≤ (tg.segments : ℝ) * ((timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) * (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2)
        + 2 * ((tg.mesh : ℚ) : ℝ) *
          Finset.sum (Finset.univ : Finset (Fin tg.segments)) (fun i =>
            Finset.sum F (fun k =>
              ‖(A.sampleAtNodes tg hcompat i).a k -
                (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                  ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2)) := by
  -- Define the integrand
  let integrand := fun t => Finset.sum F (fun k =>
    ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2)

  -- Partition: ∫_{[0,T]} = Σ_i ∫_{slab i}
  have h_partition :
      ∫ t in Set.Icc (0 : ℝ) (P.horizon : ℝ), integrand t
      = Finset.sum (Finset.univ : Finset (Fin tg.segments)) (fun i =>
          ∫ t in TimeGrid.slabReal tg i, integrand t) := by
    -- Slabs partition the time interval [0,T]
    -- Use integral_finset_union with slabs being a.e. disjoint and covering [0,T]
    have h_cover : (⋃ i : Fin tg.segments, TimeGrid.slabReal tg i) =
        Set.Icc (0 : ℝ) ((tg.horizon : ℚ) : ℝ) :=
      TimeGrid.slabsReal_partition tg
    have h_ae_disj := TimeGrid.slabsReal_ae_disjoint tg
    have h_meas : ∀ i, MeasurableSet (TimeGrid.slabReal tg i) :=
      fun i => measurableSet_Icc
    have h_int : ∀ i, IntegrableOn integrand (TimeGrid.slabReal tg i) volume := by
      intro i
      -- Same boundedness argument as in slab lemma
      have hf_bound : ∃ C : ℝ, ∀ t ∈ TimeGrid.slabReal tg i, |integrand t| ≤ C := by
        use 2 * (P.R : ℝ)^2 + 2 * (2 * ((P.R : ℝ)^2 + (P.ε : ℝ)^2))
        intro t ht
        have hnonneg : 0 ≤ integrand t :=
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        rw [abs_of_nonneg hnonneg]
        -- identical bound as before
        calc integrand t
            = Finset.sum F (fun k =>
                ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2) := rfl
          _ ≤ Finset.sum F (fun k =>
                2 * ‖(curveExtended P A t).a k‖^2 +
                  2 * ‖(witnessAtTime' P A tg hcompat t).a k‖^2) := by
                apply Finset.sum_le_sum
                intro k _; exact norm_sq_diff_le _ _
          _ = 2 * Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2)
              + 2 * Finset.sum F (fun k => ‖(witnessAtTime' P A tg hcompat t).a k‖^2) := by
                simp only [← Finset.mul_sum, Finset.sum_add_distrib]
          _ ≤ 2 * (P.R : ℝ)^2 + 2 * (2 * ((P.R : ℝ)^2 + (P.ε : ℝ)^2)) := by
                have h_curve : Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2) ≤ (P.R : ℝ)^2 := by
                  have h_slab := slab_mem_interval tg hcompat i t ht
                  have := A.inH1_curve ⟨t, h_slab⟩ F
                  unfold InH1Ball at this
                  have h_le : Finset.sum F (fun k => ‖(A.curve ⟨t, h_slab⟩).a k‖^2)
                      ≤ Finset.sum F (fun k => h1Weight k * ‖(A.curve ⟨t, h_slab⟩).a k‖^2) := by
                    apply Finset.sum_le_sum
                    intro k _
                    have h_ge : 1 ≤ h1Weight k := h1Weight_ge_one k
                    calc ‖(A.curve ⟨t, h_slab⟩).a k‖^2
                        = 1 * ‖(A.curve ⟨t, h_slab⟩).a k‖^2 := by ring
                      _ ≤ h1Weight k * ‖(A.curve ⟨t, h_slab⟩).a k‖^2 := by
                          apply mul_le_mul_of_nonneg_right h_ge (sq_nonneg _)
                  have h_eq : Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2)
                      = Finset.sum F (fun k => ‖(A.curve ⟨t, h_slab⟩).a k‖^2) := by
                    congr 1; ext k; simp [curveExtended, h_slab]
                  calc Finset.sum F (fun k => ‖(curveExtended P A t).a k‖^2)
                      = Finset.sum F (fun k => ‖(A.curve ⟨t, h_slab⟩).a k‖^2) := h_eq
                    _ ≤ Finset.sum F (fun k => h1Weight k * ‖(A.curve ⟨t, h_slab⟩).a k‖^2) := h_le
                    _ ≤ (P.R : ℝ)^2 := this
                have h_witness := witnessAtTime'_sum_bound P A tg hcompat F t
                linarith [h_curve, h_witness]
      have hf_meas : AEStronglyMeasurable integrand (volume.restrict (TimeGrid.slabReal tg i)) := by
        -- same as before
        have h_each : ∀ k ∈ F, AEStronglyMeasurable (fun t =>
            ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2) volume := by
          intro k _
          have hc := curveExtended_coeff_aestronglyMeasurable P A k
          have hw := witnessAtTime'_coeff_aestronglyMeasurable P A tg hcompat k
          exact ((hc.sub hw).norm.pow 2)
        have h_sum : AEStronglyMeasurable integrand volume := by
          show AEStronglyMeasurable (fun t => ∑ k ∈ F,
            ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2) volume
          have := Finset.aestronglyMeasurable_sum F h_each
          convert this using 1
          · funext t; simp
        exact h_sum.mono_measure (Measure.restrict_le_self)
      have hfinite : volume (TimeGrid.slabReal tg i) < ⊤ := by
        unfold TimeGrid.slabReal; exact measure_Icc_lt_top
      have hmeas : MeasurableSet (TimeGrid.slabReal tg i) := by
        unfold TimeGrid.slabReal; exact measurableSet_Icc
      exact integrable_of_aestronglyMeasurable_bounded hf_meas hmeas hf_bound hfinite
    -- Convert P.horizon to match tg.horizon
    have h_horiz_eq : (P.horizon : ℝ) = ((tg.horizon : ℚ) : ℝ) := by
      simp only [← hcompat]
    rw [h_horiz_eq, ← h_cover, IntegrationHelpers.integral_finset_union h_meas h_ae_disj h_int]

  -- Apply slab_L2_error_bound to each slab
  have h_slab_bounds : ∀ i : Fin tg.segments,
      ∫ t in TimeGrid.slabReal tg i, integrand t
      ≤ (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) * (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2 +
        2 * ((tg.mesh : ℚ) : ℝ) *
          Finset.sum F (fun k =>
            ‖(A.sampleAtNodes tg hcompat i).a k -
              (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2) := by
    intro i
    exact slab_L2_error_bound P A tg hcompat i F hsubset

  -- Sum the bounds
  calc ∫ t in Set.Icc (0 : ℝ) (P.horizon : ℝ), integrand t
      = Finset.sum (Finset.univ : Finset (Fin tg.segments)) (fun i =>
          ∫ t in TimeGrid.slabReal tg i, integrand t) := h_partition
    _ ≤ Finset.sum (Finset.univ : Finset (Fin tg.segments)) (fun i =>
          (timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) * (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2 +
          2 * ((tg.mesh : ℚ) : ℝ) *
            Finset.sum F (fun k =>
              ‖(A.sampleAtNodes tg hcompat i).a k -
                (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                  ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2)) := by
        apply Finset.sum_le_sum
        intro i _
        exact h_slab_bounds i
    _ = (tg.segments : ℝ) * ((timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) * (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2) +
        2 * ((tg.mesh : ℚ) : ℝ) *
          Finset.sum (Finset.univ : Finset (Fin tg.segments)) (fun i =>
            Finset.sum F (fun k =>
              ‖(A.sampleAtNodes tg hcompat i).a k -
                (ℓ2ZD.gridToSeqD P.ε P.R (ℓ2ZD.M_of P.ε P.R)
                  ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.mul_sum]
        have h_card : (Finset.univ : Finset (Fin tg.segments)).card = tg.segments := by
          simp [Fintype.card_fin]
        rw [h_card]
        ring

/-- Main Quantitative Aubin-Lions Theorem: The witness function constructed from
    the given time grid has L² error bounded by ε². -/
theorem quantitative_aubin_lions
    {d : ℕ} [NeZero d] (P : BudgetParams) (A : Admissible d P)
    (tg : TimeGrid) (hcompat : tg.horizon = P.horizon)
    (hsegments : 0 < tg.segments)
    -- Budget constraint: the time-modulus and rounding errors fit within ε²
    (hbudget : (tg.segments : ℝ) * ((timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) * (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2) +
               2 * ((tg.mesh : ℚ) : ℝ) * (tg.segments : ℝ) * (P.ε : ℝ)^2
               ≤ (P.ε : ℝ)^2) :
    (∫ t in Set.Icc (0 : ℝ) (P.horizon : ℝ),
      Finset.sum (ℓ2ZD.cube d (ℓ2ZD.M_of P.ε P.R)) (fun k =>
        ‖(curveExtended P A t).a k -
          (witnessAtTime' P A tg hcompat t).a k‖^2) : ℝ)
      ≤ (P.ε : ℝ)^2 := by
  -- The witness function witnessAtTime' is constructed using nodeWitness
  let M := ℓ2ZD.M_of P.ε P.R
  -- Apply total_L2_error_bound with F = cube d M
  have h_total := total_L2_error_bound (d := d) P A tg hcompat (ℓ2ZD.cube d M)
      (by intro k hk; simpa using hk)

  -- Bound the rounding error term using node_round_error
  have h_round_error_bound :
      Finset.sum (Finset.univ : Finset (Fin tg.segments)) (fun i =>
        Finset.sum (ℓ2ZD.cube d M) (fun k =>
          ‖(A.sampleAtNodes tg hcompat i).a k -
            (ℓ2ZD.gridToSeqD P.ε P.R M
              ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2))
      < (tg.segments : ℝ) * (P.ε : ℝ)^2 := by
    -- Each slab has error < ε² by node_round_error
    -- Summing over K slabs gives < K·ε²
    have h_per_slab : ∀ i : Fin tg.segments,
        Finset.sum (ℓ2ZD.cube d M) (fun k =>
          ‖(A.sampleAtNodes tg hcompat i).a k -
            (ℓ2ZD.gridToSeqD P.ε P.R M
              ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2)
        < (P.ε : ℝ)^2 := by
      intro i
      exact node_round_error P A tg hcompat i (ℓ2ZD.cube d M)
    -- Sum the strict inequalities
    calc Finset.sum (Finset.univ : Finset (Fin tg.segments)) (fun i =>
            Finset.sum (ℓ2ZD.cube d M) (fun k =>
              ‖(A.sampleAtNodes tg hcompat i).a k -
                (ℓ2ZD.gridToSeqD P.ε P.R M
                  ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2))
        < Finset.sum (Finset.univ : Finset (Fin tg.segments)) (fun _ => (P.ε : ℝ)^2) := by
          apply Finset.sum_lt_sum
          · intro i _
            exact le_of_lt (h_per_slab i)
          · -- Show at least one term is strict (segments > 0 ensures nonempty)
            use ⟨0, hsegments⟩
            simp only [Finset.mem_univ, true_and]
            exact h_per_slab ⟨0, hsegments⟩
      _ = (tg.segments : ℝ) * (P.ε : ℝ)^2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring

  -- Combine the bounds using the budget constraint
  have : ∫ t in Set.Icc (0 : ℝ) (P.horizon : ℝ),
          Finset.sum (ℓ2ZD.cube d M) (fun k =>
            ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2)
      < (P.ε : ℝ)^2 := by
    calc ∫ t in Set.Icc (0 : ℝ) (P.horizon : ℝ),
            Finset.sum (ℓ2ZD.cube d M) (fun k =>
              ‖(curveExtended P A t).a k - (witnessAtTime' P A tg hcompat t).a k‖^2)
        ≤ (tg.segments : ℝ) * ((timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) * (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2) +
          2 * ((tg.mesh : ℚ) : ℝ) *
            Finset.sum (Finset.univ : Finset (Fin tg.segments)) (fun i =>
              Finset.sum (ℓ2ZD.cube d M) (fun k =>
                ‖(A.sampleAtNodes tg hcompat i).a k -
                  (ℓ2ZD.gridToSeqD P.ε P.R M
                    ((nodeWitness P A tg hcompat).coeffs i)).a k‖^2)) := h_total
      _ < (tg.segments : ℝ) * ((timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) * (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2) +
          2 * ((tg.mesh : ℚ) : ℝ) * ((tg.segments : ℝ) * (P.ε : ℝ)^2) := by
            have h_mesh_pos : 0 < ((tg.mesh : ℚ) : ℝ) := by
              have := TimeGrid.mesh_pos tg; exact_mod_cast this
            have h_two_mesh_pos : 0 < 2 * ((tg.mesh : ℚ) : ℝ) := by linarith
            have := mul_lt_mul_of_pos_left h_round_error_bound h_two_mesh_pos
            linarith [this]
      _ = (tg.segments : ℝ) * ((timeModulusIntegralConstant (d := d) (ℓ2ZD.M_of P.ε P.R) : ℝ) * (P.S : ℝ)^2 * ((tg.mesh : ℚ) : ℝ)^2) +
          2 * ((tg.mesh : ℚ) : ℝ) * (tg.segments : ℝ) * (P.ε : ℝ)^2 := by ring
      _ ≤ (P.ε : ℝ)^2 := hbudget
  exact this.le

end Phase4Soundness

end AubinLions
