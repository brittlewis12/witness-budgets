/-
Rellich-Kondrachov 2D — L² Bridge

This file connects L²(𝕋²) functions to ℓ²(ℤ²) sequences via Fourier analysis.

Strategy: Iterate 1D Fourier API via Tonelli/Fubini (no new 2D theory required).
Approach: Bessel inequality and tail bounds suffice for witness extraction
         (full Parseval not needed).

Phases:
1. Setup & Definitions - Product characters and 2D coefficients
2. Product Integral Identity - Fubini bridge
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
import Budgets.RellichKondrachov2D
import Budgets.RellichKondrachov2D.Seq

open MeasureTheory Complex BigOperators AddCircle
open scoped Real FourierTransform ComplexConjugate

namespace RellichKondrachov2D
namespace L2Bridge

open RellichKondrachov2D.Seq
open RellichKondrachov2D.Seq.ℓ2Z2

noncomputable section

/-! ## Phase 1: Setup & Definitions -/

/-- The 1-dimensional unit torus -/
abbrev T := UnitAddCircle

/-- The 2-dimensional torus (product of unit circles) -/
abbrev T2 := T × T

/-- Haar measure on 1D torus -/
abbrev μT : Measure T := haarAddCircle

/-- Product measure on 2D torus -/
abbrev μ : Measure T2 := μT.prod μT

/-- L² space on 2D torus -/
abbrev L2_Torus2 := Lp ℂ 2 μ

/-- Product character: E_k(x,y) = e_{k₁}(x) · e_{k₂}(y)

    Uses Mathlib's `fourier` from `AddCircle`.
    For `fourier k : UnitAddCircle → ℂ`, we have:
      fourier k t = exp(2πi·k·t)

    The product character iterates this in both coordinates. -/
def prodChar (k : ℤ × ℤ) : T2 → ℂ :=
  fun p => fourier k.1 p.1 * fourier k.2 p.2

/-- Product character as an L² element

    This promotes prodChar to an element of L²(𝕋²), establishing measurability
    and square-integrability automatically.

    Uses MemLp.toLp from Mathlib with MemLp.of_bound for bounded continuous functions. -/
def Ek (k : ℤ × ℤ) : L2_Torus2 :=
  have hcont : Continuous (prodChar k) := by
    unfold prodChar
    fun_prop
  have hbound : ∀ p, ‖prodChar k p‖ ≤ 1 := by
    intro p
    haveI : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩
    simp only [prodChar, norm_mul]
    have h1 : ‖fourier k.1 p.1‖ = 1 := Circle.norm_coe _
    have h2 : ‖fourier k.2 p.2‖ = 1 := Circle.norm_coe _
    rw [h1, h2, mul_one]
  have hmem : MemLp (prodChar k) 2 μ :=
    MemLp.of_bound hcont.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound)
  hmem.toLp (prodChar k)

/-- 2D Fourier coefficient as inner product

    This is the DEFINITION we use throughout. The integral form is available
    via coeff2D_eq_prod_integral.

    Note: We use `inner (Ek k) f` (not `inner f (Ek k)`) to match the standard
    Fourier convention: ⟨f, e_k⟩ = ∫ f * conj(e_k). -/
def coeff2D (f : L2_Torus2) (k : ℤ × ℤ) : ℂ :=
  inner (𝕜 := ℂ) (Ek k) f

/-! ## Phase 2: Product Integral Identity (Fubini/Tonelli Bridge) -/

/-- Coefficient equals integral against conjugate character

    This bridges the inner product definition to the classical integral form.
    Uses L2.inner_def: inner product in L² equals integral of pointwise inner products. -/
lemma coeff2D_eq_prod_integral (f : L2_Torus2) (k : ℤ × ℤ) :
    coeff2D f k = ∫ p, f p * conj (prodChar k p) ∂μ := by
  -- Using coeff2D f k = inner (Ek k) f:
  -- L2.inner_def: inner g h = ∫ inner (g p) (h p)
  -- RCLike.inner_apply: inner a b = conj a * b
  rw [coeff2D, L2.inner_def]
  -- Unfold Ek to get the MemLp.toLp structure
  simp only [Ek]
  -- Prepare MemLp instance for prodChar (matching the one in Ek definition)
  have hcont : Continuous (prodChar k) := by unfold prodChar; fun_prop
  have hbound : ∀ p, ‖prodChar k p‖ ≤ 1 := by
    intro p
    simp only [prodChar, norm_mul]
    have h1 : ‖fourier k.1 p.1‖ = 1 := Circle.norm_coe _
    have h2 : ‖fourier k.2 p.2‖ = 1 := Circle.norm_coe _
    rw [h1, h2, mul_one]
  have hmem : MemLp (prodChar k) 2 μ :=
    MemLp.of_bound hcont.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound)
  -- Show toLp equals prodChar a.e., then apply inner_apply and commute
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hmem] with p hp
  rw [RCLike.inner_apply, hp, mul_comm]

/-! ## Phase 3: Orthonormality -/

/-- Product of integrals equals integral of product (Fubini for bounded functions)

    Direct application of Mathlib's `integral_prod_mul`. -/
lemma integral_prod_eq (f : T → ℂ) (g : T → ℂ) :
    (∫ x, f x ∂μT) * (∫ y, g y ∂μT) =
    ∫ p, f p.1 * g p.2 ∂μ := by
  unfold μ
  rw [← integral_prod_mul (μ := μT) (ν := μT) f g]

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

    ⟨E_k, E_j⟩ = ∫∫ E_k(x,y) · conj(E_j(x,y)) dx dy
                = ∫ e_{k₁}(x)·conj(e_{j₁}(x)) dx · ∫ e_{k₂}(y)·conj(e_{j₂}(y)) dy
                = δ_{k₁,j₁} · δ_{k₂,j₂}
                = δ_{k,j}

    Strategy: Apply integral_prod_mul to separate, then apply 1D orthonormality. -/
lemma orthonormal_prodChar :
    ∀ k j : ℤ × ℤ,
      ∫ p, prodChar k p * conj (prodChar j p) ∂μ =
      if k = j then 1 else 0 := by
  intro k j
  -- Expand definitions and rearrange
  calc ∫ p, prodChar k p * conj (prodChar j p) ∂μ
      = ∫ p, (fourier k.1 p.1 * fourier k.2 p.2) * conj (fourier j.1 p.1 * fourier j.2 p.2) ∂μ := by
        simp only [prodChar]
    _ = ∫ p, (fourier k.1 p.1 * fourier k.2 p.2) * (conj (fourier j.1 p.1) * conj (fourier j.2 p.2)) ∂μ := by
        congr 1; ext p; simp only [map_mul]
    _ = ∫ p, (fourier k.1 p.1 * conj (fourier j.1 p.1)) * (fourier k.2 p.2 * conj (fourier j.2 p.2)) ∂μ := by
        congr 1; ext p; ring
    _ = (∫ x, fourier k.1 x * conj (fourier j.1 x) ∂μT) * (∫ y, fourier k.2 y * conj (fourier j.2 y) ∂μT) := by
        -- Define the functions for Fubini
        let f₁ : T → ℂ := fun x => fourier k.1 x * conj (fourier j.1 x)
        let f₂ : T → ℂ := fun y => fourier k.2 y * conj (fourier j.2 y)
        change ∫ p, f₁ p.1 * f₂ p.2 ∂μ = _
        unfold μ
        rw [integral_prod_mul]
    _ = (if k.1 = j.1 then 1 else 0) * (if k.2 = j.2 then 1 else 0) := by
        rw [fourier_orthonormal_integral k.1 j.1, fourier_orthonormal_integral k.2 j.2]
    _ = if k = j then 1 else 0 := by
        by_cases h1 : k.1 = j.1
        · by_cases h2 : k.2 = j.2
          · simp [h1, h2, Prod.ext_iff]
          · simp [h1, h2, Prod.ext_iff]
        · simp [h1, Prod.ext_iff]

/-- Product characters form an orthonormal family in L²

    This is the key lemma for applying Bessel and other Hilbert space theorems.
    Connects the L² inner product to the integral formula via L2.inner_def. -/
lemma orthonormal_Ek : Orthonormal ℂ (fun k : ℤ × ℤ => Ek k) := by
  -- Strategy: Convert to integral form and apply orthonormal_prodChar
  rw [orthonormal_iff_ite]
  intro j k
  -- Goal: inner (Ek j) (Ek k) = if j = k then 1 else 0
  -- Use L2.inner_def to convert inner product to integral
  rw [L2.inner_def]
  -- Prepare MemLp instances (same as in Ek definition)
  have hcont_j : Continuous (prodChar j) := by unfold prodChar; fun_prop
  have hbound_j : ∀ p, ‖prodChar j p‖ ≤ 1 := by
    intro p
    simp only [prodChar, norm_mul]
    have h1 : ‖fourier j.1 p.1‖ = 1 := Circle.norm_coe _
    have h2 : ‖fourier j.2 p.2‖ = 1 := Circle.norm_coe _
    rw [h1, h2, mul_one]
  have hmem_j : MemLp (prodChar j) 2 μ :=
    MemLp.of_bound hcont_j.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound_j)
  have hcont_k : Continuous (prodChar k) := by unfold prodChar; fun_prop
  have hbound_k : ∀ p, ‖prodChar k p‖ ≤ 1 := by
    intro p
    simp only [prodChar, norm_mul]
    have h1 : ‖fourier k.1 p.1‖ = 1 := Circle.norm_coe _
    have h2 : ‖fourier k.2 p.2‖ = 1 := Circle.norm_coe _
    rw [h1, h2, mul_one]
  have hmem_k : MemLp (prodChar k) 2 μ :=
    MemLp.of_bound hcont_k.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound_k)
  -- Unfold Ek and rewrite integrand using coeFn_toLp, then apply orthonormal_prodChar
  simp only [Ek]
  calc ∫ p, inner ℂ (hmem_j.toLp (prodChar j) p) (hmem_k.toLp (prodChar k) p) ∂μ
      = ∫ p, inner ℂ (prodChar j p) (prodChar k p) ∂μ := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp hmem_j, MemLp.coeFn_toLp hmem_k] with p hpj hpk
        rw [hpj, hpk]
    _ = ∫ p, prodChar k p * conj (prodChar j p) ∂μ := by
        simp only [RCLike.inner_apply]
    _ = if k = j then 1 else 0 := orthonormal_prodChar k j
    _ = if j = k then 1 else 0 := by
        by_cases h : j = k <;> simp [h, eq_comm]

/-! ## Phase 4: Bessel Inequality -/

/-- Bessel inequality for finite rectangles

    For any finite set K of frequencies:
      Σ_{k∈K} |⟨f, E_k⟩|² ≤ ‖f‖²

    This is generic for orthonormal families in Hilbert spaces.
    Direct application of Mathlib's Orthonormal.sum_inner_products_le. -/
lemma bessel_rect (f : L2_Torus2) (K : Finset (ℤ × ℤ)) :
    Finset.sum K (fun k => ‖coeff2D f k‖^2) ≤ ‖f‖^2 := by
  -- Direct application of Bessel's inequality: coeff2D unfolds to inner product
  convert @Orthonormal.sum_inner_products_le ℂ L2_Torus2 _ _ _ (ℤ × ℤ) f (fun k => Ek k) K orthonormal_Ek using 3

/-! ## Phase 5: Tail Bound (Dimension-Free!)

Tail bound with weight inequality:

For k outside [-N,N]², we have max(|k₁|, |k₂|) ≥ N+1, hence k₁² + k₂² ≥ (N+1)².

This gives:
  Σ_{k∉[-N,N]²} |aₖ|² ≤ (1/(N+1)²) · Σ_k (k₁²+k₂²)|aₖ|²

This formula parallels the sequence space bound in Seq.lean, applied to coefficients.
-/

/-- Auxiliary: Outside the box implies large frequency -/
lemma outside_box_implies_large_freq {N : ℕ} {k : ℤ × ℤ}
    (h : max (|k.1|) (|k.2|) ≥ (N + 1 : ℤ)) :
    (k.1 : ℝ)^2 + (k.2 : ℝ)^2 ≥ ((N + 1) : ℝ)^2 := by
  have h1 : (|k.1| : ℝ) ≥ (N + 1 : ℝ) ∨ (|k.2| : ℝ) ≥ (N + 1 : ℝ) := by
    have hmax : (max (|k.1|) (|k.2|) : ℝ) ≥ (N + 1 : ℝ) := by
      exact_mod_cast h
    cases' le_max_iff.mp hmax with h' h'
    · left; exact h'
    · right; exact h'
  cases h1 with
  | inl h1 =>
    calc (k.1 : ℝ)^2 + (k.2 : ℝ)^2
        ≥ (k.1 : ℝ)^2 := by linarith [sq_nonneg (k.2 : ℝ)]
      _ = (|k.1| : ℝ)^2 := by simp [sq_abs]
      _ ≥ ((N + 1) : ℝ)^2 := by nlinarith [sq_nonneg (|k.1| : ℝ), sq_nonneg ((N + 1) : ℝ)]
  | inr h2 =>
    calc (k.1 : ℝ)^2 + (k.2 : ℝ)^2
        ≥ (k.2 : ℝ)^2 := by linarith [sq_nonneg (k.1 : ℝ)]
      _ = (|k.2| : ℝ)^2 := by simp [sq_abs]
      _ ≥ ((N + 1) : ℝ)^2 := by nlinarith [sq_nonneg (|k.2| : ℝ), sq_nonneg ((N + 1) : ℝ)]

/-- Main tail bound for L² functions

    Assumes: Σ_k (k₁²+k₂²)|coeff(k)|² < ∞  (H¹-type condition)
    Proves:  Tail sum ≤ (1/(N+1)²) · weighted sum

    This bound is computably extractable and sufficient for witness construction.

    Proof strategy:
    1. Use `outside_box_implies_large_freq` to show k₁² + k₂² ≥ (N+1)² for tail elements
    2. This gives ‖aₖ‖² ≤ (1/(N+1)²) · (k₁² + k₂²) · ‖aₖ‖² pointwise
    3. Sum both sides and factor out constant (1/(N+1)²)
    4. Tail weighted sum ≤ total weighted sum by subtype injection -/
lemma tail_bound_L2 (f : L2_Torus2) (N : ℕ)
    (hsum : Summable (fun k : ℤ × ℤ => ((k.1 : ℝ)^2 + (k.2 : ℝ)^2) * ‖coeff2D f k‖^2)) :
    (∑' (k : {k : ℤ × ℤ // max (|k.1|) (|k.2|) ≥ (N + 1 : ℤ)}),
      ‖coeff2D f k.val‖^2) ≤
    (1 / ((N + 1) : ℝ)^2) *
    (∑' k : ℤ × ℤ, ((k.1 : ℝ)^2 + (k.2 : ℝ)^2) * ‖coeff2D f k‖^2) := by
  -- Step 1: Establish pointwise bound for tail elements
  have tail_pointwise : ∀ (k : {k : ℤ × ℤ // max (|k.1|) (|k.2|) ≥ N + 1}),
      ‖coeff2D f k.val‖^2 ≤
      (1 / ((N + 1) : ℝ)^2) * (((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) * ‖coeff2D f k.val‖^2) := by
    intro k
    have h := outside_box_implies_large_freq k.property
    by_cases hz : ‖coeff2D f k.val‖^2 = 0
    · simp [hz]
    · have hpos : 0 < ((N + 1) : ℝ)^2 := by positivity
      have key : ‖coeff2D f k.val‖^2 * ((N + 1 : ℝ)^2) ≤ ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) * ‖coeff2D f k.val‖^2 := by
        have : ‖coeff2D f k.val‖^2 * ((N + 1 : ℝ)^2) = ((N + 1 : ℝ)^2 * ‖coeff2D f k.val‖^2) := mul_comm _ _
        rw [this]
        apply mul_le_mul_of_nonneg_right h (sq_nonneg _)
      -- Divide both sides by (N+1)^2 and rearrange
      have : ‖coeff2D f k.val‖^2 ≤ ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) * ‖coeff2D f k.val‖^2 / ((N + 1 : ℝ)^2) := by
        field_simp [ne_of_gt hpos] at key ⊢
        exact key
      calc ‖coeff2D f k.val‖^2
          ≤ ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) * ‖coeff2D f k.val‖^2 / ((N + 1 : ℝ)^2) := this
        _ = (1 / ((N + 1 : ℝ)^2)) * (((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) * ‖coeff2D f k.val‖^2) := by
            rw [div_eq_mul_inv, inv_eq_one_div, mul_comm]
  -- Step 2: Prepare summability facts for the subtype
  have hsub1 : Summable (fun k : {k : ℤ × ℤ // max (|k.1|) (|k.2|) ≥ N + 1} =>
      ‖coeff2D f k.val‖^2) := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) ?_ (hsum.subtype _)
    intro k
    by_cases h : ‖coeff2D f k.val‖^2 = 0
    · simp [h]
    · have h1 : ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) ≥ 1 := by
        have hfreq0 := outside_box_implies_large_freq k.property
        -- Convert (↑N + 1 : ℤ) to (N + 1 : ℕ) cast
        have hfreq : ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) ≥ ((N + 1 : ℕ) : ℝ)^2 := by
          convert hfreq0 using 2
          norm_cast
        have hge : (N + 1 : ℕ) ≥ 1 := Nat.succ_le_succ (Nat.zero_le N)
        calc ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2)
            ≥ ((N + 1 : ℕ) : ℝ)^2 := hfreq
          _ ≥ (1 : ℝ)^2 := by gcongr; exact_mod_cast hge
          _ = 1 := by norm_num
      calc ‖coeff2D f k.val‖^2
          = 1 * ‖coeff2D f k.val‖^2 := by ring
        _ ≤ ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) * ‖coeff2D f k.val‖^2 := by gcongr
  have hsub2 : Summable (fun k : {k : ℤ × ℤ // max (|k.1|) (|k.2|) ≥ N + 1} =>
      (1 / ((N + 1) : ℝ)^2) * (((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) * ‖coeff2D f k.val‖^2)) := by
    refine Summable.of_nonneg_of_le (fun _ => by positivity) ?_ (hsum.subtype _)
    intro k
    simp only [one_div]
    have hpos : 0 < ((N + 1) : ℝ)^2 := by positivity
    calc (((N + 1) : ℝ)^2)⁻¹ * (((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) * ‖coeff2D f k.val‖^2)
        = (((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) * ‖coeff2D f k.val‖^2) * (((N + 1) : ℝ)^2)⁻¹ := by ring
      _ ≤ (((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) * ‖coeff2D f k.val‖^2) * 1 := by
          gcongr
          have : 1 ≤ ((N + 1) : ℝ)^2 := by
            have : (1 : ℝ) ≤ ((N + 1) : ℕ) := by norm_num
            calc (1 : ℝ) ≤ ((N + 1) : ℕ) := this
              _ = ((N + 1) : ℝ) := by simp
              _ ≤ ((N + 1) : ℝ)^2 := by nlinarith
          exact inv_le_one_of_one_le₀ this
      _ = ((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) * ‖coeff2D f k.val‖^2 := by ring
  -- Step 3: Sum the pointwise bounds
  calc ∑' (k : {k : ℤ × ℤ // max (|k.1|) (|k.2|) ≥ N + 1}), ‖coeff2D f k.val‖^2
      ≤ ∑' (k : {k : ℤ × ℤ // max (|k.1|) (|k.2|) ≥ N + 1}),
          (1 / ((N + 1) : ℝ)^2) * (((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) * ‖coeff2D f k.val‖^2) := by
        apply hsub1.tsum_le_tsum tail_pointwise hsub2
    _ = (1 / ((N + 1) : ℝ)^2) *
          ∑' (k : {k : ℤ × ℤ // max (|k.1|) (|k.2|) ≥ N + 1}),
            (((k.val.1 : ℝ)^2 + (k.val.2 : ℝ)^2) * ‖coeff2D f k.val‖^2) := by
        rw [tsum_mul_left]
    _ ≤ (1 / ((N + 1) : ℝ)^2) *
          ∑' k : ℤ × ℤ, (((k.1 : ℝ)^2 + (k.2 : ℝ)^2) * ‖coeff2D f k‖^2) := by
        gcongr
        have hnonneg : ∀ k : ℤ × ℤ, (0 : ℝ) ≤ ((k.1 : ℝ)^2 + (k.2 : ℝ)^2) * ‖coeff2D f k‖^2 := by
          intro k
          apply mul_nonneg
          · apply add_nonneg <;> apply sq_nonneg
          · apply sq_nonneg
        apply hsum.tsum_subtype_le
        exact hnonneg

/-! ## Phase 6: Bridge to ℓ² -/

/-- Convert L² function to ℓ² sequence via Fourier coefficients -/
def L2_to_seq2D (u : L2_Torus2) : ℓ2Z2 where
  a := fun k => coeff2D u k
  summable_sq := by
    -- Use Bessel inequality: orthonormal families have summable inner products
    have h := orthonormal_Ek.inner_products_summable u
    have heq : (fun k : ℤ × ℤ => ‖inner (𝕜 := ℂ) (Ek k) u‖^2) = (fun k => ‖coeff2D u k‖^2) := by
      funext k
      simp only [coeff2D, norm_inner_symm]
    rwa [← heq]

/-- Mean-zero condition transfers to sequence layer -/
lemma meanZero_transfers (u : L2_Torus2)
    (hmean : ∫ p, u p ∂μ = 0) :
    (L2_to_seq2D u).meanZero := by
  -- Unfold definitions: meanZero means a(0,0) = 0
  unfold meanZero L2_to_seq2D
  -- Simplify the structure projection
  simp only
  -- Goal: coeff2D u (0, 0) = 0
  -- Use the integral formula for coefficients
  rw [coeff2D_eq_prod_integral]
  -- Goal: ∫ p, u p * conj (prodChar (0, 0) p) ∂μ = 0
  -- Show that prodChar (0, 0) p = 1 for all p
  have hprodChar : prodChar (0, 0) = fun _ => 1 := by
    ext p
    unfold prodChar
    simp
  -- Use this to simplify the integral
  rw [hprodChar]
  -- Simplify: conj 1 = 1 and u p * 1 = u p
  simp only [map_one, mul_one]
  -- Now the goal is ∫ p, u p ∂μ = 0, which is exactly hmean
  exact hmean

/-- H¹ bound transfers to sequence layer

    If ‖u‖²_{H¹} ≤ R², then the weighted ℓ² sum is bounded. -/
lemma h1Bound_transfers (u : L2_Torus2) (R : ℚ)
    (hH1 : Summable (fun k : ℤ × ℤ =>
             (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖coeff2D u k‖^2) ∧
           (∑' k : ℤ × ℤ,
             (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖coeff2D u k‖^2) ≤ (R : ℝ)^2) :
    (L2_to_seq2D u).InH1Ball R := by
  -- InH1Ball is a structure with one field: h1_bound : h1BoundFinitary R x
  -- h1BoundFinitary says: ∀ F, Finset.sum F (weighted) ≤ R²
  rcases hH1 with ⟨hsum, hbd⟩
  constructor
  intro F
  -- Goal: Finset.sum F (fun k => (1 + 4π²(k₁²+k₂²)) * ‖(L2_to_seq2D u).a k‖^2) ≤ R^2
  calc Finset.sum F (fun k => (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖(L2_to_seq2D u).a k‖^2)
      = Finset.sum F (fun k => (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖coeff2D u k‖^2) := by
        simp [L2_to_seq2D]
    _ ≤ ∑' k, (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖coeff2D u k‖^2 := by
        apply hsum.sum_le_tsum F
        intro k hk; positivity
    _ ≤ (R : ℝ)^2 := hbd

/-- Main witness existence theorem via L² bridge

    Given:  u ∈ L²(𝕋²) with mean zero and H¹ bound
    Proves: ∃ constructive grid witness

    Strategy:
    1. Convert u to ℓ² sequence via L2_to_seq2D
    2. Construct grid point via roundToGrid2D
    3. Prove witness belongs to the grid (by construction)

    NOTE: This proves witness EXISTENCE without relying on new axioms.
          The error bound ‖u - witness‖ < ε would require additional
          soundness infrastructure from Seq.lean (not yet available). -/
theorem witness_soundness_via_L2_2D
    (ε R : ℚ) (hε : 0 < ε) (hR : 0 < R)
    (u : L2_Torus2)
    (hmean : ∫ p, u p ∂μ = 0)
    (hH1 : Summable (fun k : ℤ × ℤ =>
             (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖coeff2D u k‖^2) ∧
           (∑' k : ℤ × ℤ,
             (1 + 4 * Real.pi^2 * ((k.1 : ℝ)^2 + (k.2 : ℝ)^2)) * ‖coeff2D u k‖^2) ≤ (R : ℝ)^2) :
    ∃ (M : ℕ) (δ : ℚ) (g : GridPoint2D ε R M),
      M = M_of ε R ∧
      0 < δ ∧
      δ = mesh2D ε M ∧
      g ∈ gridFinset2D ε R M ∧
      ∀ F : Finset (ℤ × ℤ),
        Finset.sum F (fun k => ‖coeff2D u k - (gridToSeq ε R M g).a k‖^2) < (ε : ℝ)^2 := by
  -- Convert u to sequence
  let u_seq := L2_to_seq2D u
  -- Transfer hypotheses to sequence layer
  have hmean_seq : u_seq.meanZero := meanZero_transfers u hmean
  have hH1_seq : u_seq.InH1Ball R := h1Bound_transfers u R hH1
  -- Apply gridFinset_sound_2D from the sequence layer
  have hε_real : 0 < (ε : ℝ) := by exact_mod_cast hε
  have hR_real : 0 < (R : ℝ) := by exact_mod_cast hR
  obtain ⟨g, hg_mem, hg_bound⟩ := Seq.gridFinset_sound_2D ε R hε_real hR_real u_seq hmean_seq hH1_seq
  -- Package the result
  use M_of ε R, mesh2D ε (M_of ε R), g
  refine ⟨rfl, ?_, rfl, hg_mem, ?_⟩
  · exact_mod_cast mesh2D_pos ε (M_of ε R) hε
  · intro F
    -- The bound transfers directly because coeff2D u k = u_seq.a k
    have heq : ∀ k, coeff2D u k = u_seq.a k := by
      intro k
      rfl
    simp only [heq]
    exact hg_bound F

/-! ## Auxiliary Lemmas for Future Development -/

/-- prodChar (0,0) is the constant function 1 -/
lemma prodChar_zero_eq_one : prodChar (0, 0) = fun _ => 1 := by
  ext p
  unfold prodChar
  simp

/-- Characters are bounded -/
lemma prodChar_bounded (k : ℤ × ℤ) (p : T2) :
    ‖prodChar k p‖ = 1 := by
  unfold prodChar
  rw [norm_mul]
  have h1 : ‖fourier k.1 p.1‖ = 1 := Circle.norm_coe _
  have h2 : ‖fourier k.2 p.2‖ = 1 := Circle.norm_coe _
  rw [h1, h2, mul_one]

end  -- noncomputable section
end L2Bridge
end RellichKondrachov2D
