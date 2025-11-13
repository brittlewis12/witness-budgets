/-
Rellich-Kondrachov 3D — L² Bridge

This file connects L²(𝕋³) functions to ℓ²(ℤ³) sequences via Fourier analysis.

Strategy: Iterate 1D Fourier API via triple Fubini (no new 3D theory required).
Approach: Bessel inequality and tail bounds suffice for witness extraction
         (full Parseval not needed).

Phases:
1. Setup & Definitions - Product characters and 3D coefficients
2. Product Integral Identity - Triple Fubini bridge
3. Orthonormality - Product of 1D orthonormal systems
4. Bessel Inequality - Finite sum energy bound
5. Tail Bound - Dimension-free weight inequality
6. Bridge to ℓ² - Main soundness theorem

Budget: C0-C2 (strategic sorries acceptable for Fubini/Tonelli if needed)
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Budgets.RellichKondrachov3D
import Budgets.RellichKondrachov3D.Seq

open MeasureTheory Complex BigOperators AddCircle
open scoped Real FourierTransform ComplexConjugate

namespace RellichKondrachov3D
namespace L2Bridge

open ℓ2Z3

noncomputable section

/-! ## Phase 1: Setup & Definitions -/

/-- The 1-dimensional unit torus -/
abbrev T := UnitAddCircle

/-- The 3-dimensional torus (triple product of unit circles).
    Note: Uses nested pairs (T × T) × T to match Mathlib's product measure structure. -/
abbrev T3 := (T × T) × T

/-- Haar measure on 1D torus -/
abbrev μT : Measure T := haarAddCircle

/-- Product measure on 3D torus: μ = μT ⊗ μT ⊗ μT -/
abbrev μ3 : Measure T3 := (μT.prod μT).prod μT

/-- L² space on 3D torus -/
abbrev L2_Torus3 := Lp ℂ 2 μ3

/-- Product character: E_k(x,y,z) = e_{k₁}(x) · e_{k₂}(y) · e_{k₃}(z)

    Uses Mathlib's `fourier` from `AddCircle`.
    For `fourier k : UnitAddCircle → ℂ`, we have:
      fourier k t = exp(2πi·k·t)

    The product character iterates this in all three coordinates.
    Note: T3 = (T × T) × T, so p.1.1 is x, p.1.2 is y, p.2 is z. -/
def prodChar3D (k : ℤ × ℤ × ℤ) : T3 → ℂ :=
  fun p => fourier k.1 p.1.1 * fourier k.2.1 p.1.2 * fourier k.2.2 p.2

/-- Product character as an L² element

    This promotes prodChar3D to an element of L²(𝕋³), establishing measurability
    and square-integrability automatically.

    Uses MemLp.toLp from Mathlib with MemLp.of_bound for bounded continuous functions. -/
def Ek3D (k : ℤ × ℤ × ℤ) : L2_Torus3 :=
  have hcont : Continuous (prodChar3D k) := by
    unfold prodChar3D
    fun_prop
  have hbound : ∀ p, ‖prodChar3D k p‖ ≤ 1 := by
    intro p
    haveI : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
    simp only [prodChar3D, norm_mul]
    have h1 : ‖fourier k.1 p.1.1‖ = 1 := Circle.norm_coe _
    have h2 : ‖fourier k.2.1 p.1.2‖ = 1 := Circle.norm_coe _
    have h3 : ‖fourier k.2.2 p.2‖ = 1 := Circle.norm_coe _
    rw [h1, h2, h3]
    norm_num
  have hmem : MemLp (prodChar3D k) 2 μ3 :=
    MemLp.of_bound hcont.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound)
  hmem.toLp (prodChar3D k)

/-- 3D Fourier coefficient as inner product

    This is the DEFINITION we use throughout. The integral form is available
    via coeff3D_eq_prod_integral.

    Note: We use `inner (Ek3D k) f` (not `inner f (Ek3D k)`) to match the standard
    Fourier convention: ⟨f, e_k⟩ = ∫ f * conj(e_k). -/
def coeff3D (f : L2_Torus3) (k : ℤ × ℤ × ℤ) : ℂ :=
  inner (𝕜 := ℂ) (Ek3D k) f

/-! ## Phase 2: Product Integral Identity (Triple Fubini Bridge) -/

/-- Coefficient equals integral against conjugate character

    This bridges the inner product definition to the classical integral form.
    Uses L2.inner_def: inner product in L² equals integral of pointwise inner products. -/
lemma coeff3D_eq_prod_integral (f : L2_Torus3) (k : ℤ × ℤ × ℤ) :
    coeff3D f k = ∫ p, f p * conj (prodChar3D k p) ∂μ3 := by
  -- Using coeff3D f k = inner (Ek3D k) f:
  -- L2.inner_def: inner g h = ∫ inner (g p) (h p)
  -- RCLike.inner_apply: inner a b = conj a * b
  rw [coeff3D, L2.inner_def]
  -- Unfold Ek3D to get the MemLp.toLp structure
  simp only [Ek3D]
  -- Prepare MemLp instance for prodChar3D (matching the one in Ek3D definition)
  have hcont : Continuous (prodChar3D k) := by unfold prodChar3D; fun_prop
  have hbound : ∀ p, ‖prodChar3D k p‖ ≤ 1 := by
    intro p
    simp only [prodChar3D, norm_mul]
    have h1 : ‖fourier k.1 p.1.1‖ = 1 := Circle.norm_coe _
    have h2 : ‖fourier k.2.1 p.1.2‖ = 1 := Circle.norm_coe _
    have h3 : ‖fourier k.2.2 p.2‖ = 1 := Circle.norm_coe _
    rw [h1, h2, h3]
    norm_num
  have hmem : MemLp (prodChar3D k) 2 μ3 :=
    MemLp.of_bound hcont.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound)
  -- Show toLp equals prodChar3D a.e., then apply inner_apply and commute
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hmem] with p hp
  rw [RCLike.inner_apply, hp, mul_comm]

/-! ## Phase 3: Orthonormality -/

/-- Product of integrals equals integral of product (triple Fubini for bounded functions)

    Direct application of Mathlib's `integral_prod_mul` twice.

    Strategy: Apply integral_prod_mul iteratively:
    1. First for the inner product (first × second coordinates)
    2. Then for the outer product ((first × second) × third coordinate)

    This navigates the nested product structure (T × T) × T correctly. -/
lemma integral_prod_eq_3D (f g h : T → ℂ) :
    (∫ x, f x ∂μT) * (∫ y, g y ∂μT) * (∫ z, h z ∂μT) =
    ∫ p, f p.1.1 * g p.1.2 * h p.2 ∂μ3 := by
  -- μ3 = (μT.prod μT).prod μT, so we apply integral_prod_mul twice
  unfold μ3
  -- Start from LHS and work towards RHS
  calc (∫ x, f x ∂μT) * (∫ y, g y ∂μT) * (∫ z, h z ∂μT)
      = ((∫ x, f x ∂μT) * (∫ y, g y ∂μT)) * (∫ z, h z ∂μT) := by
        ring
    _ = (∫ p12, f p12.1 * g p12.2 ∂μT.prod μT) * (∫ p3, h p3 ∂μT) := by
        congr 1
        rw [← integral_prod_mul (μ := μT) (ν := μT)]
    _ = ∫ p, (f p.1.1 * g p.1.2) * h p.2 ∂(μT.prod μT).prod μT := by
        rw [← integral_prod_mul (μ := μT.prod μT) (ν := μT)]
    _ = ∫ p, f p.1.1 * g p.1.2 * h p.2 ∂(μT.prod μT).prod μT := by
        simp [mul_assoc]

/-- 1D Fourier characters are orthonormal

    Uses Mathlib's orthonormal_fourier and converts to integral form. -/
lemma fourier_orthonormal_integral (k j : ℤ) :
    ∫ x, fourier k x * conj (fourier j x) ∂μT = if k = j then 1 else 0 := by
  -- Use the orthonormality of fourierLp to get the inner product
  have h := (orthonormal_iff_ite (v := @fourierLp 1 _ 2 _)).mp orthonormal_fourier j k
  -- Convert inner product to integral using ContinuousMap.inner_toLp
  rw [ContinuousMap.inner_toLp] at h
  -- h now says: (if j = k then 1 else 0) = ∫ fourier k * conj(fourier j)
  -- We need: ∫ fourier k * conj(fourier j) = if k = j then 1 else 0
  simp only [eq_comm] at h
  exact h.symm

/-- Product characters form an orthonormal system (integral form)

    ⟨E_k, E_j⟩ = ∫∫∫ E_k(x,y,z) · conj(E_j(x,y,z)) dx dy dz
                = ∫ e_{k₁}(x)·conj(e_{j₁}(x)) dx ·
                  ∫ e_{k₂}(y)·conj(e_{j₂}(y)) dy ·
                  ∫ e_{k₃}(z)·conj(e_{j₃}(z)) dz
                = δ_{k₁,j₁} · δ_{k₂,j₂} · δ_{k₃,j₃}
                = δ_{k,j}

    Strategy: Apply integral_prod_eq_3D to separate, then apply 1D orthonormality thrice. -/
lemma orthonormal_prodChar3D :
    ∀ k j : ℤ × ℤ × ℤ,
      ∫ p, prodChar3D k p * conj (prodChar3D j p) ∂μ3 =
      if k = j then 1 else 0 := by
  intro k j
  -- Expand definitions and rearrange
  calc ∫ p, prodChar3D k p * conj (prodChar3D j p) ∂μ3
      = ∫ p, (fourier k.1 p.1.1 * fourier k.2.1 p.1.2 * fourier k.2.2 p.2) *
              conj (fourier j.1 p.1.1 * fourier j.2.1 p.1.2 * fourier j.2.2 p.2) ∂μ3 := by
        simp only [prodChar3D]
    _ = ∫ p, (fourier k.1 p.1.1 * fourier k.2.1 p.1.2 * fourier k.2.2 p.2) *
              (conj (fourier j.1 p.1.1) * conj (fourier j.2.1 p.1.2) * conj (fourier j.2.2 p.2)) ∂μ3 := by
        congr 1; ext p; simp only [map_mul]
    _ = ∫ p, (fourier k.1 p.1.1 * conj (fourier j.1 p.1.1)) *
              (fourier k.2.1 p.1.2 * conj (fourier j.2.1 p.1.2)) *
              (fourier k.2.2 p.2 * conj (fourier j.2.2 p.2)) ∂μ3 := by
        congr 1; ext p; ring
    _ = (∫ x, fourier k.1 x * conj (fourier j.1 x) ∂μT) *
        (∫ y, fourier k.2.1 y * conj (fourier j.2.1 y) ∂μT) *
        (∫ z, fourier k.2.2 z * conj (fourier j.2.2 z) ∂μT) := by
        -- Define the functions for triple Fubini
        let f₁ : T → ℂ := fun x => fourier k.1 x * conj (fourier j.1 x)
        let f₂ : T → ℂ := fun y => fourier k.2.1 y * conj (fourier j.2.1 y)
        let f₃ : T → ℂ := fun z => fourier k.2.2 z * conj (fourier j.2.2 z)
        change ∫ p, f₁ p.1.1 * f₂ p.1.2 * f₃ p.2 ∂μ3 = _
        exact (integral_prod_eq_3D f₁ f₂ f₃).symm
    _ = (if k.1 = j.1 then 1 else 0) *
        (if k.2.1 = j.2.1 then 1 else 0) *
        (if k.2.2 = j.2.2 then 1 else 0) := by
        rw [fourier_orthonormal_integral k.1 j.1,
            fourier_orthonormal_integral k.2.1 j.2.1,
            fourier_orthonormal_integral k.2.2 j.2.2]
    _ = if k = j then 1 else 0 := by
        by_cases h1 : k.1 = j.1
        · by_cases h2 : k.2.1 = j.2.1
          · by_cases h3 : k.2.2 = j.2.2
            · simp [h1, h2, h3, Prod.ext_iff]
            · simp [h1, h2, h3, Prod.ext_iff]
          · simp [h1, h2, Prod.ext_iff]
        · simp [h1, Prod.ext_iff]

/-- Product characters form an orthonormal family in L²

    This is the key lemma for applying Bessel and other Hilbert space theorems.
    Connects the L² inner product to the integral formula via L2.inner_def. -/
lemma orthonormal_Ek3D : Orthonormal ℂ (fun k : ℤ × ℤ × ℤ => Ek3D k) := by
  -- Strategy: Convert to integral form and apply orthonormal_prodChar3D
  rw [orthonormal_iff_ite]
  intro j k
  -- Goal: inner (Ek3D j) (Ek3D k) = if j = k then 1 else 0
  -- Use L2.inner_def to convert inner product to integral
  rw [L2.inner_def]
  -- Prepare MemLp instances (same as in Ek3D definition)
  have hcont_j : Continuous (prodChar3D j) := by unfold prodChar3D; fun_prop
  have hbound_j : ∀ p, ‖prodChar3D j p‖ ≤ 1 := by
    intro p
    simp only [prodChar3D, norm_mul]
    have h1 : ‖fourier j.1 p.1.1‖ = 1 := Circle.norm_coe _
    have h2 : ‖fourier j.2.1 p.1.2‖ = 1 := Circle.norm_coe _
    have h3 : ‖fourier j.2.2 p.2‖ = 1 := Circle.norm_coe _
    rw [h1, h2, h3]
    norm_num
  have hmem_j : MemLp (prodChar3D j) 2 μ3 :=
    MemLp.of_bound hcont_j.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound_j)
  have hcont_k : Continuous (prodChar3D k) := by unfold prodChar3D; fun_prop
  have hbound_k : ∀ p, ‖prodChar3D k p‖ ≤ 1 := by
    intro p
    simp only [prodChar3D, norm_mul]
    have h1 : ‖fourier k.1 p.1.1‖ = 1 := Circle.norm_coe _
    have h2 : ‖fourier k.2.1 p.1.2‖ = 1 := Circle.norm_coe _
    have h3 : ‖fourier k.2.2 p.2‖ = 1 := Circle.norm_coe _
    rw [h1, h2, h3]
    norm_num
  have hmem_k : MemLp (prodChar3D k) 2 μ3 :=
    MemLp.of_bound hcont_k.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound_k)
  -- Unfold Ek3D and rewrite integrand using coeFn_toLp, then apply orthonormal_prodChar3D
  simp only [Ek3D]
  calc ∫ p, inner ℂ (hmem_j.toLp (prodChar3D j) p) (hmem_k.toLp (prodChar3D k) p) ∂μ3
      = ∫ p, inner ℂ (prodChar3D j p) (prodChar3D k p) ∂μ3 := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp hmem_j, MemLp.coeFn_toLp hmem_k] with p hpj hpk
        rw [hpj, hpk]
    _ = ∫ p, prodChar3D k p * conj (prodChar3D j p) ∂μ3 := by
        simp only [RCLike.inner_apply]
    _ = if k = j then 1 else 0 := orthonormal_prodChar3D k j
    _ = if j = k then 1 else 0 := by
        by_cases h : j = k <;> simp [h, eq_comm]

/-! ## Phase 4: Bessel Inequality -/

/-- Bessel inequality for finite cubes

    For any finite set K of frequencies:
      Σ_{k∈K} |⟨f, E_k⟩|² ≤ ‖f‖²

    This is generic for orthonormal families in Hilbert spaces.
    Direct application of Mathlib's Orthonormal.sum_inner_products_le. -/
lemma bessel_cube (f : L2_Torus3) (K : Finset (ℤ × ℤ × ℤ)) :
    Finset.sum K (fun k => ‖coeff3D f k‖^2) ≤ ‖f‖^2 := by
  -- Direct application of Bessel's inequality: coeff3D unfolds to inner product
  convert @Orthonormal.sum_inner_products_le ℂ L2_Torus3 _ _ _ (ℤ × ℤ × ℤ) f
                                             (fun k => Ek3D k) K orthonormal_Ek3D
    using 3

/-! ## Phase 5: Tail Bound (Dimension-Free!)

Tail bound with weight inequality:

For k outside [-N,N]³, we have max(|k₁|, |k₂|, |k₃|) ≥ N+1, hence k₁² + k₂² + k₃² ≥ (N+1)².

This gives:
  Σ_{k∉[-N,N]³} |aₖ|² ≤ (1/(N+1)²) · Σ_k (k₁²+k₂²+k₃²)|aₖ|²

This formula parallels the sequence space bound in Seq.lean, applied to coefficients.
-/

/-- Auxiliary: Outside the cube implies large frequency -/
lemma outside_cube_implies_large_freq {N : ℕ} {k : ℤ × ℤ × ℤ}
    (h : max (max (|k.1|) (|k.2.1|)) (|k.2.2|) ≥ (N + 1 : ℤ)) :
    (k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2 ≥ ((N + 1) : ℝ)^2 := by
  have h1 : (|k.1| : ℝ) ≥ (N + 1 : ℝ) ∨ (|k.2.1| : ℝ) ≥ (N + 1 : ℝ) ∨ (|k.2.2| : ℝ) ≥ (N + 1 : ℝ) := by
    have hmax : (max (max (|k.1|) (|k.2.1|)) (|k.2.2|) : ℝ) ≥ (N + 1 : ℝ) := by
      exact_mod_cast h
    cases' le_max_iff.mp hmax with h' h'
    · cases' le_max_iff.mp h' with h'' h''
      · left; exact h''
      · right; left; exact h''
    · right; right; exact h'
  cases h1 with
  | inl h1 =>
    calc (k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2
        ≥ (k.1 : ℝ)^2 := by linarith [sq_nonneg (k.2.1 : ℝ), sq_nonneg (k.2.2 : ℝ)]
      _ = (|k.1| : ℝ)^2 := by simp [sq_abs]
      _ ≥ ((N + 1) : ℝ)^2 := by nlinarith [sq_nonneg (|k.1| : ℝ), sq_nonneg ((N + 1) : ℝ)]
  | inr h2 =>
    cases h2 with
    | inl h2 =>
      calc (k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2
          ≥ (k.2.1 : ℝ)^2 := by linarith [sq_nonneg (k.1 : ℝ), sq_nonneg (k.2.2 : ℝ)]
        _ = (|k.2.1| : ℝ)^2 := by simp [sq_abs]
        _ ≥ ((N + 1) : ℝ)^2 := by nlinarith [sq_nonneg (|k.2.1| : ℝ), sq_nonneg ((N + 1) : ℝ)]
    | inr h3 =>
      calc (k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2
          ≥ (k.2.2 : ℝ)^2 := by linarith [sq_nonneg (k.1 : ℝ), sq_nonneg (k.2.1 : ℝ)]
        _ = (|k.2.2| : ℝ)^2 := by simp [sq_abs]
        _ ≥ ((N + 1) : ℝ)^2 := by nlinarith [sq_nonneg (|k.2.2| : ℝ), sq_nonneg ((N + 1) : ℝ)]

/-- Main tail bound for L² functions (DIMENSION-FREE!)

    Assumes: Σ_k (k₁²+k₂²+k₃²)|coeff(k)|² < ∞  (H¹-type condition)
    Proves:  Tail sum ≤ (1/(N+1)²) · weighted sum

    This bound is computably extractable and sufficient for witness construction.

    Proof strategy:
    1. Use `outside_cube_implies_large_freq` to show k₁² + k₂² + k₃² ≥ (N+1)² for tail
    2. This gives ‖aₖ‖² ≤ (1/(N+1)²) · (k₁² + k₂² + k₃²) · ‖aₖ‖² pointwise
    3. Sum both sides and factor out constant (1/(N+1)²)
    4. Tail weighted sum ≤ total weighted sum by subtype injection -/
lemma tail_bound_L2_3D (f : L2_Torus3) (N : ℕ)
    (hsum : Summable (fun k : ℤ × ℤ × ℤ =>
             ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2) * ‖coeff3D f k‖^2)) :
    (∑' (k : {k : ℤ × ℤ × ℤ // max (max (|k.1|) (|k.2.1|)) (|k.2.2|) ≥ (N + 1 : ℤ)}),
      ‖coeff3D f k.val‖^2) ≤
    (1 / ((N + 1) : ℝ)^2) *
    (∑' k : ℤ × ℤ × ℤ, ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2) * ‖coeff3D f k‖^2) := by
  -- Step 1: Establish pointwise bound for tail elements
  have tail_pointwise : ∀ (k : {k : ℤ × ℤ × ℤ // max (max (|k.1|) (|k.2.1|)) (|k.2.2|) ≥ N + 1}),
      ‖coeff3D f k.val‖^2 ≤
      (1 / ((N + 1) : ℝ)^2) * (((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) * ‖coeff3D f k.val‖^2) := by
    intro k
    have h := outside_cube_implies_large_freq k.property
    by_cases hz : ‖coeff3D f k.val‖^2 = 0
    · simp [hz]
    · have hpos : 0 < ((N + 1) : ℝ)^2 := by positivity
      have key : ‖coeff3D f k.val‖^2 * ((N + 1 : ℝ)^2) ≤ ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) * ‖coeff3D f k.val‖^2 := by
        have : ‖coeff3D f k.val‖^2 * ((N + 1 : ℝ)^2) = ((N + 1 : ℝ)^2 * ‖coeff3D f k.val‖^2) := mul_comm _ _
        rw [this]
        apply mul_le_mul_of_nonneg_right h (sq_nonneg _)
      -- Divide both sides by (N+1)^2 and rearrange
      have : ‖coeff3D f k.val‖^2 ≤ ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) * ‖coeff3D f k.val‖^2 / ((N + 1 : ℝ)^2) := by
        field_simp [ne_of_gt hpos] at key ⊢
        exact key
      calc ‖coeff3D f k.val‖^2
          ≤ ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) * ‖coeff3D f k.val‖^2 / ((N + 1 : ℝ)^2) := this
        _ = (1 / ((N + 1 : ℝ)^2)) * (((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) * ‖coeff3D f k.val‖^2) := by
            rw [div_eq_mul_inv, inv_eq_one_div, mul_comm]
  -- Step 2: Prepare summability facts for the subtype
  have hsub1 : Summable (fun k : {k : ℤ × ℤ × ℤ // max (max (|k.1|) (|k.2.1|)) (|k.2.2|) ≥ N + 1} =>
      ‖coeff3D f k.val‖^2) := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) ?_ (hsum.subtype _)
    intro k
    by_cases h : ‖coeff3D f k.val‖^2 = 0
    · simp [h]
    · have h1 : ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) ≥ 1 := by
        have hfreq0 := outside_cube_implies_large_freq k.property
        -- Convert (↑N + 1 : ℤ) to (N + 1 : ℕ) cast
        have hfreq : ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) ≥ ((N + 1 : ℕ) : ℝ)^2 := by
          convert hfreq0 using 2
          norm_cast
        have hge : (N + 1 : ℕ) ≥ 1 := Nat.succ_le_succ (Nat.zero_le N)
        calc ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2)
            ≥ ((N + 1 : ℕ) : ℝ)^2 := hfreq
          _ ≥ (1 : ℝ)^2 := by gcongr; exact_mod_cast hge
          _ = 1 := by norm_num
      calc ‖coeff3D f k.val‖^2
          = 1 * ‖coeff3D f k.val‖^2 := by ring
        _ ≤ ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) * ‖coeff3D f k.val‖^2 := by gcongr
  have hsub2 : Summable (fun k : {k : ℤ × ℤ × ℤ // max (max (|k.1|) (|k.2.1|)) (|k.2.2|) ≥ N + 1} =>
      (1 / ((N + 1) : ℝ)^2) * (((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) * ‖coeff3D f k.val‖^2)) := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) ?_ (hsum.subtype _)
    intro k
    simp only [one_div]
    have hpos : 0 < ((N + 1) : ℝ)^2 := by positivity
    calc (((N + 1) : ℝ)^2)⁻¹ * (((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) * ‖coeff3D f k.val‖^2)
        = (((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) * ‖coeff3D f k.val‖^2) * (((N + 1) : ℝ)^2)⁻¹ := by ring
      _ ≤ (((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) * ‖coeff3D f k.val‖^2) * 1 := by
          gcongr
          have : 1 ≤ ((N + 1) : ℝ)^2 := by
            have : (1 : ℝ) ≤ ((N + 1) : ℕ) := by norm_num
            calc (1 : ℝ) ≤ ((N + 1) : ℕ) := this
              _ = ((N + 1) : ℝ) := by simp
              _ ≤ ((N + 1) : ℝ)^2 := by nlinarith
          exact inv_le_one_of_one_le₀ this
      _ = ((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) * ‖coeff3D f k.val‖^2 := by ring
  -- Step 3: Sum the pointwise bounds
  calc ∑' (k : {k : ℤ × ℤ × ℤ // max (max (|k.1|) (|k.2.1|)) (|k.2.2|) ≥ N + 1}), ‖coeff3D f k.val‖^2
      ≤ ∑' (k : {k : ℤ × ℤ × ℤ // max (max (|k.1|) (|k.2.1|)) (|k.2.2|) ≥ N + 1}),
          (1 / ((N + 1) : ℝ)^2) * (((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) * ‖coeff3D f k.val‖^2) := by
        apply hsub1.tsum_le_tsum tail_pointwise hsub2
    _ = (1 / ((N + 1) : ℝ)^2) *
          ∑' (k : {k : ℤ × ℤ × ℤ // max (max (|k.1|) (|k.2.1|)) (|k.2.2|) ≥ N + 1}),
            (((k.val.1 : ℝ)^2 + (k.val.2.1 : ℝ)^2 + (k.val.2.2 : ℝ)^2) * ‖coeff3D f k.val‖^2) := by
        rw [tsum_mul_left]
    _ ≤ (1 / ((N + 1) : ℝ)^2) *
          ∑' k : ℤ × ℤ × ℤ, (((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2) * ‖coeff3D f k‖^2) := by
        gcongr
        have hnonneg : ∀ k : ℤ × ℤ × ℤ, (0 : ℝ) ≤ ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2) * ‖coeff3D f k‖^2 := by
          intro k
          apply mul_nonneg
          · apply add_nonneg
            · apply add_nonneg
              · apply sq_nonneg
              · apply sq_nonneg
            · apply sq_nonneg
          · apply sq_nonneg
        apply hsum.tsum_subtype_le
        exact hnonneg

/-! ## Phase 6: Bridge to ℓ² -/

/-- Convert L² function to ℓ² sequence via Fourier coefficients -/
def L2_to_seq3D (u : L2_Torus3) : Seq3D where
  a := fun k => coeff3D u k
  summable_sq := by
    -- Use Bessel inequality: orthonormal families have summable inner products
    have h := orthonormal_Ek3D.inner_products_summable u
    have heq : (fun k : ℤ × ℤ × ℤ => ‖inner (𝕜 := ℂ) (Ek3D k) u‖^2) = (fun k => ‖coeff3D u k‖^2) := by
      funext k
      simp only [coeff3D, norm_inner_symm]
    rwa [← heq]

/-- Mean-zero condition transfers to sequence layer -/
lemma meanZero_transfers (u : L2_Torus3)
    (hmean : ∫ p, u p ∂μ3 = 0) :
    meanZero (L2_to_seq3D u) := by
  -- Unfold definitions: meanZero means a(0,0,0) = 0
  unfold meanZero L2_to_seq3D
  -- Simplify the structure projection
  simp only
  -- Goal: coeff3D u (0, (0, 0)) = 0
  -- Use the integral formula for coefficients
  rw [coeff3D_eq_prod_integral]
  -- Goal: ∫ p, u p * conj (prodChar3D (0, (0, 0)) p) ∂μ3 = 0
  -- Show that prodChar3D (0, (0, 0)) p = 1 for all p
  have hprodChar : prodChar3D (0, (0, 0)) = fun _ => 1 := by
    ext p
    unfold prodChar3D
    simp
  -- Use this to simplify the integral
  rw [hprodChar]
  -- Simplify: conj 1 = 1 and u p * 1 = u p
  simp only [map_one, mul_one]
  -- Now the goal is ∫ p, u p ∂μ3 = 0, which is exactly hmean
  exact hmean

/-- H¹ bound transfers to sequence layer

    If ‖u‖²_{H¹} ≤ R², then the weighted ℓ² sum is bounded. -/
lemma h1Bound_transfers (u : L2_Torus3) (R : ℚ)
    (hH1 : Summable (fun k : ℤ × ℤ × ℤ =>
             (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2)) * ‖coeff3D u k‖^2) ∧
           (∑' k : ℤ × ℤ × ℤ,
             (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2)) * ‖coeff3D u k‖^2) ≤ (R : ℝ)^2) :
    InH1Ball (R : ℝ) (L2_to_seq3D u) := by
  -- InH1Ball says: ∀ F, Finset.sum F (weighted) ≤ R²
  rcases hH1 with ⟨hsum, hbd⟩
  unfold InH1Ball
  intro F
  -- Goal: Finset.sum F (fun k => (1 + 4π²(k₁²+k₂²+k₃²)) * ‖(L2_to_seq3D u).a k‖^2) ≤ R^2
  calc Finset.sum F (fun k => (h1Weight k) * ‖(L2_to_seq3D u).a k‖^2)
      = Finset.sum F (fun k => (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2)) * ‖coeff3D u k‖^2) := by
        simp [L2_to_seq3D, h1Weight]
    _ ≤ ∑' k, (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2)) * ‖coeff3D u k‖^2 := by
        apply hsum.sum_le_tsum F
        intro k hk; positivity
    _ ≤ (R : ℝ)^2 := hbd

/-- Main witness existence theorem via L² bridge

    Given:  u ∈ L²(𝕋³) with mean zero and H¹ bound
    Proves: ∃ constructive grid witness

    Strategy:
    1. Convert u to ℓ² sequence via L2_to_seq3D
    2. Construct grid point via roundToGrid3D
    3. Prove witness belongs to the grid (by construction)

    NOTE: This proves witness EXISTENCE without relying on new axioms.
          The error bound ‖u - witness‖ < ε follows from gridFinset_sound_3D. -/
theorem witness_soundness_via_L2_3D
    (ε R : ℚ) (hε : 0 < ε) (hR : 0 < R)
    (u : L2_Torus3)
    (hmean : ∫ p, u p ∂μ3 = 0)
    (hH1 : Summable (fun k : ℤ × ℤ × ℤ =>
             (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2)) * ‖coeff3D u k‖^2) ∧
           (∑' k : ℤ × ℤ × ℤ,
             (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2.1 : ℝ)^2 + (k.2.2 : ℝ)^2)) * ‖coeff3D u k‖^2) ≤ (R : ℝ)^2) :
    ∃ (M : ℕ) (δ : ℚ) (g : GridPoint3D ε R M),
      M = M_of ε R ∧
      0 < δ ∧
      δ = mesh3D ε M ∧
      g ∈ gridFinset3D ε R M ∧
      ∀ F : Finset (ℤ × ℤ × ℤ),
        Finset.sum F (fun k => ‖coeff3D u k - (gridToSeq ε R M g).a k‖^2) < (ε : ℝ)^2 := by
  -- Convert u to sequence
  let u_seq := L2_to_seq3D u
  -- Transfer hypotheses to sequence layer
  have hmean_seq : meanZero u_seq := meanZero_transfers u hmean
  have hH1_seq : InH1Ball (R : ℝ) u_seq := h1Bound_transfers u R hH1
  -- Apply gridFinset_sound_3D from the sequence layer
  have hε_real : 0 < (ε : ℝ) := by exact_mod_cast hε
  have hR_real : 0 < (R : ℝ) := by exact_mod_cast hR
  obtain ⟨g, hg_bound⟩ := gridFinset_sound_3D ε R hε_real hR_real u_seq hmean_seq hH1_seq
  -- Package the result
  use M_of ε R, mesh3D ε (M_of ε R), g
  refine ⟨rfl, ?_, rfl, ?_, ?_⟩
  · exact_mod_cast mesh3D_pos ε (M_of ε R) hε
  · -- Show g ∈ gridFinset3D ε R M
    -- This is automatically true because g has type GridPoint3D ε R M
    -- and gridFinset3D is defined as all such grid points
    apply Finset.mem_pi.mpr
    intro k hk
    simp [coeffBoxSubtype]
  · intro F
    -- The bound transfers directly because coeff3D u k = u_seq.a k
    have heq : ∀ k, coeff3D u k = u_seq.a k := by
      intro k
      rfl
    simp only [heq]
    exact hg_bound F

/-! ## Auxiliary Lemmas for Future Development -/

/-- prodChar3D (0,0,0) is the constant function 1 -/
lemma prodChar3D_zero_eq_one : prodChar3D (0, (0, 0)) = fun _ => 1 := by
  ext p
  unfold prodChar3D
  simp

/-- Characters are bounded -/
lemma prodChar3D_bounded (k : ℤ × ℤ × ℤ) (p : T3) :
    ‖prodChar3D k p‖ = 1 := by
  unfold prodChar3D
  rw [norm_mul, norm_mul]
  have h1 : ‖fourier k.1 p.1.1‖ = 1 := Circle.norm_coe _
  have h2 : ‖fourier k.2.1 p.1.2‖ = 1 := Circle.norm_coe _
  have h3 : ‖fourier k.2.2 p.2‖ = 1 := Circle.norm_coe _
  rw [h1, h2, h3]
  norm_num

end  -- noncomputable section
end L2Bridge
end RellichKondrachov3D
