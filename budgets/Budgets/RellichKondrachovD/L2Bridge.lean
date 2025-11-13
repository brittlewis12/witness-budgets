/-
! Rellich–Kondrachov in arbitrary dimension: L² bridge

This file connects the L² formulation on `TD d` with the sequence model `SeqD d`.
It provides the orthonormality and product-integral facts required to transport
H¹ bounds between the two worlds.

## Highlights
* Product characters `prodCharD` / `EkD` form an orthonormal basis.
* `integral_prod_eq_D` (specialised from mathlib) supplies the Fubini step.
* The bridge theorem links L² data to the constructive witness (`gridFinset_sound_d`).
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Budgets.RellichKondrachovD.Core
import Budgets.RellichKondrachovD.TailBound
import Budgets.RellichKondrachovD.Soundness

open MeasureTheory Complex BigOperators AddCircle
open scoped Real FourierTransform ComplexConjugate

namespace RellichKondrachovD
namespace L2Bridge

open ℓ2ZD

noncomputable section

/-! ## Phase 1: Setup & Definitions -/

/-- The 1-dimensional unit torus -/
abbrev T := UnitAddCircle

/-- The d-dimensional torus as a function space -/
abbrev TD (d : ℕ) := Fin d → T

/-- Haar measure on 1D torus -/
abbrev μT : Measure T := haarAddCircle

/-- Haar measure on the circle is σ-finite (probability measure). -/
instance : SigmaFinite μT := by infer_instance

/-- Product measure on d-dimensional torus using Measure.pi -/
abbrev μD (d : ℕ) : Measure (TD d) :=
  Measure.pi (fun _ : Fin d => μT)

/-- L² space on d-dimensional torus -/
abbrev L2_TorusD (d : ℕ) := Lp ℂ 2 (μD d)

/-- Product character: E_k(p) = ∏ᵢ e_{kᵢ}(pᵢ)

    Uses Mathlib's `fourier` from `AddCircle`.
    For `fourier k : UnitAddCircle → ℂ`, we have:
      fourier k t = exp(2πi·k·t)

    The product character multiplies these over all d coordinates. -/
def prodCharD (d : ℕ) (k : Fin d → ℤ) : TD d → ℂ :=
  fun p => ∏ i : Fin d, fourier (k i) (p i)

/-- Product character as an L² element

    This promotes prodCharD to an element of L²(𝕋ᵈ), establishing measurability
    and square-integrability automatically.

    Uses MemLp.toLp from Mathlib with MemLp.of_bound for bounded continuous functions. -/
def EkD (d : ℕ) (k : Fin d → ℤ) : L2_TorusD d :=
  have hcont : Continuous (prodCharD d k) := by
    unfold prodCharD
    apply continuous_finset_prod
    intro i _
    fun_prop
  have hbound : ∀ p, ‖prodCharD d k p‖ ≤ 1 := by
    intro p
    simp only [prodCharD]
    calc ‖∏ i : Fin d, fourier (k i) (p i)‖
        = ∏ i : Fin d, ‖fourier (k i) (p i)‖ := by rw [norm_prod]
      _ = ∏ i : Fin d, (1 : ℝ) := by
          congr 1
          ext i
          exact Circle.norm_coe _
      _ = 1 := by simp
      _ ≤ 1 := by norm_num
  have hmem : MemLp (prodCharD d k) 2 (μD d) :=
    MemLp.of_bound hcont.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound)
  hmem.toLp (prodCharD d k)

/-- d-dimensional Fourier coefficient as inner product

    This is the DEFINITION we use throughout. The integral form is available
    via coeffD_eq_prod_integral.

    Note: We use `inner (EkD d k) f` (not `inner f (EkD d k)`) to match the standard
    Fourier convention: ⟨f, e_k⟩ = ∫ f * conj(e_k). -/
def coeffD (d : ℕ) (f : L2_TorusD d) (k : Fin d → ℤ) : ℂ :=
  inner (𝕜 := ℂ) (EkD d k) f

/-! ## Phase 2: Product Integral Identity -/

/-- Coefficient equals integral against conjugate character

    This bridges the inner product definition to the classical integral form.
    Uses L2.inner_def: inner product in L² equals integral of pointwise inner products. -/
lemma coeffD_eq_prod_integral (d : ℕ) (f : L2_TorusD d) (k : Fin d → ℤ) :
    coeffD d f k = ∫ p, f p * conj (prodCharD d k p) ∂(μD d) := by
  rw [coeffD, L2.inner_def]
  simp only [EkD]
  -- Prepare MemLp instance
  have hcont : Continuous (prodCharD d k) := by
    unfold prodCharD
    apply continuous_finset_prod
    intro i _
    fun_prop
  have hbound : ∀ p, ‖prodCharD d k p‖ ≤ 1 := by
    intro p
    simp only [prodCharD]
    calc ‖∏ i : Fin d, fourier (k i) (p i)‖
        = ∏ i : Fin d, ‖fourier (k i) (p i)‖ := by rw [norm_prod]
      _ = ∏ i : Fin d, (1 : ℝ) := by
          congr 1; ext i; exact Circle.norm_coe _
      _ = 1 := by simp
      _ ≤ 1 := by norm_num
  have hmem : MemLp (prodCharD d k) 2 (μD d) :=
    MemLp.of_bound hcont.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound)
  -- Show toLp equals prodCharD a.e., then apply inner_apply and commute
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hmem] with p hp
  rw [RCLike.inner_apply, hp, mul_comm]

/-! ## Phase 3: Orthonormality -/

/-- 1D Fourier characters are orthonormal

    Uses Mathlib's orthonormal_fourier and converts to integral form. -/
lemma fourier_orthonormal_integral (k j : ℤ) :
    ∫ x, fourier k x * conj (fourier j x) ∂μT = if k = j then 1 else 0 := by
  have h := (orthonormal_iff_ite (v := @fourierLp 1 _ 2 _)).mp orthonormal_fourier j k
  rw [ContinuousMap.inner_toLp] at h
  simp only [eq_comm] at h
  exact h.symm

/-- Product of delta functions equals delta

    Key lemma: (∏ᵢ δ_{kᵢ,jᵢ}) = δ_{k,j}

    This is straightforward: the product is 1 iff all factors are 1 iff k = j. -/
lemma prod_ite_eq_ite (d : ℕ) (k j : Fin d → ℤ) :
    (∏ i : Fin d, if k i = j i then (1 : ℂ) else 0) =
      if k = j then 1 else 0 := by
  by_cases h : k = j
  · simp [h]
  · simp only [if_neg h]
    -- ∃ i where k i ≠ j i, so that factor is 0
    have ⟨i, hi⟩ : ∃ i, k i ≠ j i := by
      contrapose! h
      ext i
      exact h i
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- Product integrals separate (Fubini for `Measure.pi`).

This is exactly `MeasureTheory.integral_fintype_prod_eq_prod` specialized to
`ι := Fin d`, the constant space `T`, and the identical measure `μT`. -/
lemma integral_prod_eq_D (d : ℕ) (f : Fin d → T → ℂ) :
    (∏ i, ∫ x, f i x ∂ μT) =
    ∫ p, ∏ i, f i (p i) ∂ (μD d) := by
  classical
  -- mathlib states the equality in the opposite direction.
  simpa [μD] using
    (MeasureTheory.integral_fintype_prod_eq_prod
      (ι := Fin d)
      (E := fun _ : Fin d => T)
      (μ := fun _ : Fin d => μT)
      (f := f)).symm

/-- Product characters form an orthonormal system (integral form)

    ⟨E_k, E_j⟩ = ∫ E_k(p) · conj(E_j(p)) dp
                = ∫ (∏ᵢ e_{kᵢ}(pᵢ)) · conj(∏ᵢ e_{jᵢ}(pᵢ)) dp
                = ∫ ∏ᵢ (e_{kᵢ}(pᵢ) · conj(e_{jᵢ}(pᵢ))) dp
                = ∏ᵢ ∫ e_{kᵢ}(x) · conj(e_{jᵢ}(x)) dx    (Fubini)
                = ∏ᵢ δ_{kᵢ,jᵢ}                          (1D orthonormality)
                = δ_{k,j}                               (product of deltas)

    Strategy: Apply integral_prod_eq_D to separate, then 1D orthonormality. -/
lemma orthonormal_prodCharD (d : ℕ) :
    ∀ k j : Fin d → ℤ,
      ∫ p, prodCharD d k p * conj (prodCharD d j p) ∂(μD d) =
      if k = j then 1 else 0 := by
  intro k j
  calc ∫ p, prodCharD d k p * conj (prodCharD d j p) ∂(μD d)
      = ∫ p, (∏ i, fourier (k i) (p i)) * conj (∏ i, fourier (j i) (p i)) ∂(μD d) := by
        simp only [prodCharD]
    _ = ∫ p, (∏ i, fourier (k i) (p i)) * (∏ i, conj (fourier (j i) (p i))) ∂(μD d) := by
        congr 1; ext p; simp [map_prod]
    _ = ∫ p, ∏ i, (fourier (k i) (p i) * conj (fourier (j i) (p i))) ∂(μD d) := by
        congr 1; ext p; rw [Finset.prod_mul_distrib]
    _ = ∏ i, ∫ x, fourier (k i) x * conj (fourier (j i) x) ∂μT := by
        let f : Fin d → (T → ℂ) := fun i x => fourier (k i) x * conj (fourier (j i) x)
        exact (integral_prod_eq_D d f).symm
    _ = ∏ i, (if k i = j i then 1 else 0) := by
        congr 1; ext i; exact fourier_orthonormal_integral (k i) (j i)
    _ = if k = j then 1 else 0 := prod_ite_eq_ite d k j

/-- Product characters form an orthonormal family in L²

    This is the key lemma for applying Bessel and other Hilbert space theorems.
    Connects the L² inner product to the integral formula via L2.inner_def. -/
lemma orthonormal_EkD (d : ℕ) : Orthonormal ℂ (fun k : Fin d → ℤ => EkD d k) := by
  rw [orthonormal_iff_ite]
  intro j k
  rw [L2.inner_def]
  -- Prepare MemLp instances
  have hcont_j : Continuous (prodCharD d j) := by
    unfold prodCharD
    apply continuous_finset_prod
    intro i _
    fun_prop
  have hbound_j : ∀ p, ‖prodCharD d j p‖ ≤ 1 := by
    intro p
    simp only [prodCharD]
    calc ‖∏ i : Fin d, fourier (j i) (p i)‖
        = ∏ i : Fin d, ‖fourier (j i) (p i)‖ := by rw [norm_prod]
      _ = ∏ i : Fin d, (1 : ℝ) := by
          congr 1; ext i; exact Circle.norm_coe _
      _ = 1 := by simp
      _ ≤ 1 := by norm_num
  have hmem_j : MemLp (prodCharD d j) 2 (μD d) :=
    MemLp.of_bound hcont_j.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound_j)
  have hcont_k : Continuous (prodCharD d k) := by
    unfold prodCharD
    apply continuous_finset_prod
    intro i _
    fun_prop
  have hbound_k : ∀ p, ‖prodCharD d k p‖ ≤ 1 := by
    intro p
    simp only [prodCharD]
    calc ‖∏ i : Fin d, fourier (k i) (p i)‖
        = ∏ i : Fin d, ‖fourier (k i) (p i)‖ := by rw [norm_prod]
      _ = ∏ i : Fin d, (1 : ℝ) := by
          congr 1; ext i; exact Circle.norm_coe _
      _ = 1 := by simp
      _ ≤ 1 := by norm_num
  have hmem_k : MemLp (prodCharD d k) 2 (μD d) :=
    MemLp.of_bound hcont_k.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound_k)
  -- Unfold EkD and rewrite using coeFn_toLp, then apply orthonormal_prodCharD
  simp only [EkD]
  calc ∫ p, inner ℂ (hmem_j.toLp (prodCharD d j) p) (hmem_k.toLp (prodCharD d k) p) ∂(μD d)
      = ∫ p, inner ℂ (prodCharD d j p) (prodCharD d k p) ∂(μD d) := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp hmem_j, MemLp.coeFn_toLp hmem_k] with p hpj hpk
        rw [hpj, hpk]
    _ = ∫ p, prodCharD d k p * conj (prodCharD d j p) ∂(μD d) := by
        simp only [RCLike.inner_apply]
    _ = if k = j then 1 else 0 := orthonormal_prodCharD d k j
    _ = if j = k then 1 else 0 := by
        by_cases h : j = k <;> simp [h, eq_comm]

/-! ## Phase 4: Bessel Inequality -/

/-- Bessel inequality for finite frequency sets

    For any finite set K of frequencies:
      Σ_{k∈K} |⟨f, E_k⟩|² ≤ ‖f‖²

    This is generic for orthonormal families in Hilbert spaces.
    Direct application of Mathlib's Orthonormal.sum_inner_products_le. -/
lemma bessel_D (d : ℕ) (f : L2_TorusD d) (K : Finset (Fin d → ℤ)) :
    Finset.sum K (fun k => ‖coeffD d f k‖^2) ≤ ‖f‖^2 := by
  convert @Orthonormal.sum_inner_products_le ℂ (L2_TorusD d) _ _ _
    (Fin d → ℤ) f (fun k => EkD d k) K (orthonormal_EkD d) using 3

/-! ## Phase 5: Tail Bound - Delegates to TailBound.lean

The tail bound is already proven in TailBound.lean using the `tailR` predicate.
We don't need to reprove it here - just note that it's available.

The dimension-free formula R²/(4π²M²) is proven in `tail_bound_finitary_d`.
-/

/-! ## Phase 6: Bridge to ℓ² -/

/-- Convert L² function to ℓ² sequence via Fourier coefficients -/
def L2_to_seqD (d : ℕ) (u : L2_TorusD d) : SeqD d where
  a := fun k => coeffD d u k
  summable_sq := by
    -- Use Bessel inequality: orthonormal families have summable inner products
    have h := (orthonormal_EkD d).inner_products_summable u
    have heq : (fun k : Fin d → ℤ => ‖inner (𝕜 := ℂ) (EkD d k) u‖^2) =
               (fun k => ‖coeffD d u k‖^2) := by
      funext k
      simp only [coeffD, norm_inner_symm]
    rwa [← heq]

/-- Mean-zero condition transfers to sequence layer -/
lemma meanZero_transfers (d : ℕ) (u : L2_TorusD d)
    (hmean : ∫ p, u p ∂(μD d) = 0) :
    meanZero (L2_to_seqD d u) := by
  unfold meanZero L2_to_seqD
  simp only
  -- Goal: coeffD d u (fun _ => 0) = 0
  rw [coeffD_eq_prod_integral]
  -- Show prodCharD d (fun _ => 0) = fun _ => 1
  have : prodCharD d (fun _ => 0) = fun _ => 1 := by
    ext p
    simp [prodCharD]
  rw [this]
  simp only [map_one, mul_one]
  exact hmean

/-- H¹ bound transfers to sequence layer

    If ‖u‖²_{H¹} ≤ R², then the weighted ℓ² sum is bounded. -/
lemma h1Bound_transfers (d : ℕ) (u : L2_TorusD d) (R : ℚ)
    (hH1 : Summable (fun k : Fin d → ℤ =>
             (1 + 4 * Real.pi^2 * (∑ i, (k i : ℝ)^2)) * ‖coeffD d u k‖^2) ∧
           (∑' k : Fin d → ℤ,
             (1 + 4 * Real.pi^2 * (∑ i, (k i : ℝ)^2)) * ‖coeffD d u k‖^2) ≤ (R : ℝ)^2) :
    InH1Ball (R : ℝ) (L2_to_seqD d u) := by
  rcases hH1 with ⟨hsum, hbd⟩
  unfold InH1Ball
  intro F
  have heq : ∀ k, h1Weight k * ‖(L2_to_seqD d u).a k‖^2 =
                   (1 + 4 * Real.pi^2 * (∑ i, (k i : ℝ)^2)) * ‖coeffD d u k‖^2 := by
    intro k
    simp [h1Weight, ℓ2ZD.normSq, L2_to_seqD]
  calc Finset.sum F (fun k => h1Weight k * ‖(L2_to_seqD d u).a k‖^2)
      = Finset.sum F (fun k => (1 + 4 * Real.pi^2 * (∑ i, (k i : ℝ)^2)) * ‖coeffD d u k‖^2) := by
        simp only [heq]
    _ ≤ ∑' k, (1 + 4 * Real.pi^2 * (∑ i, (k i : ℝ)^2)) * ‖coeffD d u k‖^2 := by
        apply hsum.sum_le_tsum F
        intro k _; positivity
    _ ≤ (R : ℝ)^2 := hbd

/-- Main witness existence theorem via L² bridge

    Given:  u ∈ L²(𝕋ᵈ) with mean zero and H¹ bound
    Proves: ∃ constructive grid witness with error < ε

    Strategy:
    1. Convert u to ℓ² sequence via L2_to_seqD
    2. Transfer hypotheses (mean-zero, H¹ bound)
    3. Apply gridFinset_sound_d_proof from Soundness.lean
    4. Package result

    This proves witness EXISTENCE without relying on new axioms,
    with the dimension-free tail bound R²/(4π²M²). -/
theorem witness_soundness_via_L2_D
    (d : ℕ) [NeZero d] (ε R : ℚ) (hε : 0 < ε) (hR : 0 < R)
    (u : L2_TorusD d)
    (hmean : ∫ p, u p ∂(μD d) = 0)
    (hH1 : Summable (fun k : Fin d → ℤ =>
             (1 + 4 * Real.pi^2 * (∑ i, (k i : ℝ)^2)) * ‖coeffD d u k‖^2) ∧
           (∑' k : Fin d → ℤ,
             (1 + 4 * Real.pi^2 * (∑ i, (k i : ℝ)^2)) * ‖coeffD d u k‖^2) ≤ (R : ℝ)^2) :
    ∃ (g : GridPointD d ε R (M_of ε R)),
      ∀ F : Finset (Fin d → ℤ),
        Finset.sum F (fun k =>
          ‖coeffD d u k - (gridToSeqD ε R (M_of ε R) g).a k‖^2)
          < (ε : ℝ)^2 := by
  -- Convert u to sequence
  let u_seq := L2_to_seqD d u
  -- Transfer hypotheses
  have hmean_seq : meanZero u_seq :=
    meanZero_transfers d u hmean
  have hH1_seq : InH1Ball (R : ℝ) u_seq :=
    h1Bound_transfers d u R hH1
  -- Apply gridFinset_sound_d_proof from Soundness.lean
  have hε_real : 0 < (ε : ℝ) := by exact_mod_cast hε
  have hR_real : 0 < (R : ℝ) := by exact_mod_cast hR
  obtain ⟨g, hg_bound⟩ :=
    gridFinset_sound_d_proof ε R hε_real hR_real u_seq hmean_seq hH1_seq
  -- Package result
  use g
  intro F
  have heq : ∀ k, coeffD d u k = u_seq.a k := by
    intro k; rfl
  simp only [heq]
  exact hg_bound F

/-! ## Auxiliary Lemmas -/

/-- prodCharD (fun _ => 0) is the constant function 1 -/
lemma prodCharD_zero_eq_one (d : ℕ) : prodCharD d (fun _ => 0) = fun _ => 1 := by
  ext p
  unfold prodCharD
  simp

/-- Characters are bounded -/
lemma prodCharD_bounded (d : ℕ) (k : Fin d → ℤ) (p : TD d) :
    ‖prodCharD d k p‖ = 1 := by
  unfold prodCharD
  calc ‖∏ i : Fin d, fourier (k i) (p i)‖
      = ∏ i : Fin d, ‖fourier (k i) (p i)‖ := by rw [norm_prod]
    _ = ∏ i : Fin d, (1 : ℝ) := by
        congr 1; ext i; exact Circle.norm_coe _
    _ = 1 := by simp

end  -- noncomputable section
end L2Bridge
end RellichKondrachovD
