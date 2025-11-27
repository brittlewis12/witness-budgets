import Budgets.SemilinearHeat.SobolevSeq
import Budgets.SemilinearHeat.Operator
import Budgets.RellichKondrachovD.Core

/-!
# Bilinear Forms and Inner Products for Semilinear Heat PDE

This file provides the inner product, duality pairing, and bilinear form
structures needed for the weak formulation of the semilinear heat equation.

## Main Definitions

- `innerProductOn`: L² inner product on finite frequency sets
- `dualityPairingOn`: H⁻¹-H¹ duality pairing
- `bilinearFormOn`: Dirichlet energy bilinear form a(u,v)
- Associated bounds and properties

## Mathematical Background

For the semilinear heat PDE:
  ∂ₜu - Δu = N(u)  on (0,1) × (0,T)

The weak formulation requires:
- L² inner product: (u,v)_L² = ∫ u v̄ dx
- Dirichlet bilinear form: a(u,v) = ∫ u_x v_x dx
- Duality pairing: ⟨f,v⟩_{H⁻¹×H¹} = (f,v)_L²

All operations work on finite frequency sets for constructivity.
-/

namespace SemilinearHeat

open BigOperators Complex
open scoped ComplexConjugate
open ℓ2ZD (Lattice SeqD InH1Ball InHminusBall h1Weight hminusWeight)

noncomputable section

/-! ## L² Inner Product -/

/-- L² inner product on a finite frequency set.
For sequences u, v with Fourier coefficients u.a(k), v.a(k),
the L² inner product is:
  (u,v)_L² = Σₖ u.a(k) · conj(v.a(k))
-/
def innerProductOn (F : Finset (Lattice spatialDim))
    (u v : SeqD spatialDim) : ℂ :=
  Finset.sum F (fun k => u.a k * conj (v.a k))

@[simp]
lemma innerProductOn_empty (u v : SeqD spatialDim) :
    innerProductOn ∅ u v = 0 := by
  simp [innerProductOn]

lemma innerProductOn_comm (F : Finset (Lattice spatialDim))
    (u v : SeqD spatialDim) :
    innerProductOn F v u = conj (innerProductOn F u v) := by
  simp only [innerProductOn]
  rw [map_sum]
  congr 1
  ext k
  simp only [RingHom.map_mul, conj_conj]
  ring

lemma innerProductOn_self_nonneg (F : Finset (Lattice spatialDim))
    (u : SeqD spatialDim) :
    0 ≤ (innerProductOn F u u).re := by
  unfold innerProductOn
  calc
    Complex.re (Finset.sum F (fun k => u.a k * conj (u.a k)))
        = Complex.re (Finset.sum F (fun k => Complex.normSq (u.a k))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro k _
          exact Complex.mul_conj (u.a k)
    _ = Finset.sum F (fun k => ‖u.a k‖^2) := by
          rw [← Complex.ofReal_sum]
          simp only [Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    _ ≥ 0 := Finset.sum_nonneg (fun k _ => sq_nonneg _)

/- NOTE: The following lemma is MATHEMATICALLY INCORRECT and has been removed:

   `innerProductOn_mono`: Claims ‖innerProductOn F u v‖ ≤ ‖innerProductOn G u v‖ for F ⊆ G

   COUNTEREXAMPLE:
   - Let F = {k₁}, G = {k₁, k₂}
   - innerProductOn F u v = u.a(k₁) * conj(v.a(k₁))
   - innerProductOn G u v = u.a(k₁) * conj(v.a(k₁)) + u.a(k₂) * conj(v.a(k₂))
   - If the two terms have opposite phases, cancellation occurs and ‖·‖_G < ‖·‖_F

   The norm of a sum does NOT monotonically increase with larger sets due to
   possible cancellation in the complex plane. This is a fundamental property
   of complex inner products.
-/

/-! ## H⁻¹-H¹ Duality Pairing -/

/-- Duality pairing between H⁻¹ and H¹ spaces on a finite frequency set.
For f ∈ H⁻¹ and v ∈ H¹, the pairing is:
  ⟨f,v⟩ = Σₖ conj(f.a(k)) · v.a(k)

Note: This is the same as L² inner product at the sequence level,
but the interpretation differs (duality vs inner product).
-/
def dualityPairingOn (F : Finset (Lattice spatialDim))
    (f : Hminus1Seq) (v : H1Seq) : ℂ :=
  Finset.sum F (fun k => conj (f.coeff k) * v.coeff k)

@[simp]
lemma dualityPairingOn_empty (f : Hminus1Seq) (v : H1Seq) :
    dualityPairingOn ∅ f v = 0 := by
  simp [dualityPairingOn]

/- NOTE: The following lemma `dualityPairingOn_comm` was MATHEMATICALLY INCORRECT
   and has been REMOVED.

   ORIGINAL CLAIM (WRONG): dualityPairingOn F f v = conj (dualityPairingOn F f v)

   This claimed the pairing is real-valued (equals its own conjugate), which is
   FALSE for general complex-valued sequences f ∈ H⁻¹ and v ∈ H¹.

   EXPLANATION:
   The pairing ⟨f,v⟩ = Σₖ conj(f.coeff k) * v.coeff k is complex-valued in general.
   For it to be real, we would need ⟨f,v⟩ = conj(⟨f,v⟩), i.e.,
     Σₖ conj(f.coeff k) * v.coeff k = Σₖ f.coeff k * conj(v.coeff k)
   which requires f.coeff k = c * conj(v.coeff k) for some real c, not true in general.

   NOTE: We cannot formulate a "swapping arguments" version like innerProductOn_comm
   because f and v have different types (Hminus1Seq vs H1Seq), so the dual pairing
   is not symmetric in that sense.
-/

/-! ## Dirichlet Bilinear Form -/

/-- The Dirichlet energy bilinear form on a finite frequency set.
For u, v ∈ H₀¹(0,1), the bilinear form is:
  a(u,v) = ∫ u_x v_x dx = Σₖ λₖ · u.a(k) · conj(v.a(k))

where λₖ = π²k² is the Laplacian eigenvalue (laplacianWeight).
-/
def bilinearFormOn (F : Finset (Lattice spatialDim))
    (u v : H1Seq) : ℂ :=
  Finset.sum F (fun k => (laplacianWeight k : ℂ) * u.coeff k * conj (v.coeff k))

@[simp]
lemma bilinearFormOn_empty (u v : H1Seq) :
    bilinearFormOn ∅ u v = 0 := by
  simp [bilinearFormOn]

lemma bilinearFormOn_comm (F : Finset (Lattice spatialDim))
    (u v : H1Seq) :
    bilinearFormOn F v u = conj (bilinearFormOn F u v) := by
  simp only [bilinearFormOn]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  simp only [RingHom.map_mul, conj_conj]
  have : conj (laplacianWeight k : ℂ) = (laplacianWeight k : ℂ) := by simp
  rw [this]
  ring

/-! ## Connection to Energy Functionals -/

/-- The bilinear form on the diagonal equals the gradient energy. -/
lemma bilinearFormOn_eq_gradEnergy (F : Finset (Lattice spatialDim))
    (u : H1Seq) :
    (bilinearFormOn F u u).re = gradEnergyOn F u.toSeqD := by
  unfold bilinearFormOn gradEnergyOn
  simp only [H1Seq.coeff]
  calc
    Complex.re (Finset.sum F (fun k => (laplacianWeight k : ℂ) * u.toSeqD.a k * conj (u.toSeqD.a k)))
        = Complex.re (Finset.sum F (fun k => (laplacianWeight k : ℂ) * Complex.normSq (u.toSeqD.a k))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [← Complex.mul_conj (u.toSeqD.a k)]
          ring
    _ = Complex.re (Finset.sum F (fun k => ((laplacianWeight k * ‖u.toSeqD.a k‖^2 : ℝ) : ℂ))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Complex.normSq_eq_norm_sq]
          push_cast
          rfl
    _ = Finset.sum F (fun k => laplacianWeight k * ‖u.toSeqD.a k‖^2) := by
          rw [← Complex.ofReal_sum]
          simp only [Complex.ofReal_re]

lemma bilinearFormOn_self_nonneg (F : Finset (Lattice spatialDim))
    (u : H1Seq) :
    0 ≤ (bilinearFormOn F u u).re := by
  rw [bilinearFormOn_eq_gradEnergy]
  exact gradEnergyOn_nonneg F u.toSeqD

/-! ## Boundedness Properties -/

/-- Weighted Cauchy-Schwarz inequality for finite sums.
For nonnegative weights wₖ and complex coefficients aₖ, bₖ:
  |Σ wₖ aₖ b̄ₖ| ≤ √(Σ wₖ|aₖ|²) · √(Σ wₖ|bₖ|²)

Strategy: Absorb weights into coefficients by defining
  a'ₖ = √wₖ · aₖ,  b'ₖ = √wₖ · bₖ
Then apply triangle inequality and standard Cauchy-Schwarz.
-/
lemma weighted_cauchy_schwarz (F : Finset (Lattice spatialDim))
    (w : Lattice spatialDim → ℝ) (a b : Lattice spatialDim → ℂ)
    (hw : ∀ k ∈ F, 0 ≤ w k) :
    ‖Finset.sum F (fun k => w k * a k * conj (b k))‖
      ≤ Real.sqrt (Finset.sum F (fun k => w k * ‖a k‖^2))
        * Real.sqrt (Finset.sum F (fun k => w k * ‖b k‖^2)) := by
  -- Step 1: Bound norm of sum by sum of norms (triangle inequality)
  have h_tri : ‖Finset.sum F (fun k => w k * a k * conj (b k))‖
      ≤ Finset.sum F (fun k => ‖w k * a k * conj (b k)‖) :=
    norm_sum_le _ _
  -- Step 2: Simplify norms of products
  have h_norm_prod : ∀ k ∈ F, ‖w k * a k * conj (b k)‖ = w k * ‖a k‖ * ‖b k‖ := by
    intro k hk
    have hw_nonneg := hw k hk
    simp only [Complex.norm_mul, Complex.norm_real, Complex.norm_conj]
    rw [Real.norm_eq_abs, abs_of_nonneg hw_nonneg]
  -- Step 3: Apply Cauchy-Schwarz to the sum ∑ xᵢyᵢ ≤ √(∑ xᵢ²) √(∑ yᵢ²)
  -- Use: (∑ fᵢgᵢ)² ≤ (∑ fᵢ²)(∑ gᵢ²)
  calc
    ‖Finset.sum F (fun k => w k * a k * conj (b k))‖
        ≤ Finset.sum F (fun k => ‖w k * a k * conj (b k)‖) := h_tri
    _ = Finset.sum F (fun k => w k * ‖a k‖ * ‖b k‖) := by
        refine Finset.sum_congr rfl ?_
        exact h_norm_prod
    _ = Finset.sum F (fun k => (Real.sqrt (w k) * ‖a k‖) * (Real.sqrt (w k) * ‖b k‖)) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        have hw_nonneg := hw k hk
        conv_lhs => rw [show w k = Real.sqrt (w k) * Real.sqrt (w k) from (Real.mul_self_sqrt hw_nonneg).symm]
        ring
    _ ≤ Real.sqrt (Finset.sum F (fun k => (Real.sqrt (w k) * ‖a k‖)^2))
        * Real.sqrt (Finset.sum F (fun k => (Real.sqrt (w k) * ‖b k‖)^2)) := by
        -- Apply (∑ fᵢgᵢ)² ≤ (∑ fᵢ²)(∑ gᵢ²)
        have h_cs := Finset.sum_mul_sq_le_sq_mul_sq F
          (fun k => Real.sqrt (w k) * ‖a k‖)
          (fun k => Real.sqrt (w k) * ‖b k‖)
        have h_sum_nonneg : 0 ≤ Finset.sum F (fun k => (Real.sqrt (w k) * ‖a k‖) * (Real.sqrt (w k) * ‖b k‖)) :=
          Finset.sum_nonneg (fun k hk => by
            have := hw k hk
            positivity)
        -- From h_cs: (∑ fᵢgᵢ)² ≤ (∑ fᵢ²)(∑ gᵢ²)
        -- Take sqrt of both sides
        have h_lhs : Real.sqrt ((Finset.sum F (fun k => (Real.sqrt (w k) * ‖a k‖) * (Real.sqrt (w k) * ‖b k‖)))^2)
            = Finset.sum F (fun k => (Real.sqrt (w k) * ‖a k‖) * (Real.sqrt (w k) * ‖b k‖)) := by
          rw [Real.sqrt_sq h_sum_nonneg]
        have h_rhs : Real.sqrt ((Finset.sum F (fun k => (Real.sqrt (w k) * ‖a k‖)^2))
                * (Finset.sum F (fun k => (Real.sqrt (w k) * ‖b k‖)^2)))
            = Real.sqrt (Finset.sum F (fun k => (Real.sqrt (w k) * ‖a k‖)^2))
              * Real.sqrt (Finset.sum F (fun k => (Real.sqrt (w k) * ‖b k‖)^2)) := by
          rw [Real.sqrt_mul (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
        rw [← h_lhs, ← h_rhs]
        exact Real.sqrt_le_sqrt h_cs
    _ = Real.sqrt (Finset.sum F (fun k => w k * ‖a k‖^2))
        * Real.sqrt (Finset.sum F (fun k => w k * ‖b k‖^2)) := by
        congr 1 <;> (congr 1; refine Finset.sum_congr rfl ?_)
        · intro k hk
          have hw_nonneg := hw k hk
          have : (Real.sqrt (w k) * ‖a k‖)^2 = w k * ‖a k‖^2 := by
            rw [mul_pow, Real.sq_sqrt hw_nonneg]
          exact this
        · intro k hk
          have hw_nonneg := hw k hk
          have : (Real.sqrt (w k) * ‖b k‖)^2 = w k * ‖b k‖^2 := by
            rw [mul_pow, Real.sq_sqrt hw_nonneg]
          exact this

/-- The bilinear form is bounded on H¹ balls.
Mathematical idea:
  |a(u,v)| = |Σ λₖ uₖ v̄ₖ| ≤ √(Σ λₖ|uₖ|²) · √(Σ λₖ|vₖ|²)
where λₖ = laplacianWeight ≤ h1Weight allows us to bound by |R₁| · |R₂|.
-/
lemma bilinearFormOn_bounded (F : Finset (Lattice spatialDim))
    (R₁ R₂ : ℝ) (u v : H1Seq)
    (hu : InH1Ball R₁ u.toSeqD) (hv : InH1Ball R₂ v.toSeqD) :
    ‖bilinearFormOn F u v‖ ≤ |R₁| * |R₂| := by
  -- Unfold the bilinear form definition
  unfold bilinearFormOn
  simp only [H1Seq.coeff]
  -- Apply weighted Cauchy-Schwarz with weight = laplacianWeight
  have h_cs := weighted_cauchy_schwarz F
    (fun k => laplacianWeight k)
    (fun k => u.toSeqD.a k)
    (fun k => v.toSeqD.a k)
    (fun k _ => laplacianWeight_nonneg k)
  -- Bound the weighted sums using laplacianWeight ≤ h1Weight
  have h_u_bound : Finset.sum F (fun k => laplacianWeight k * ‖u.toSeqD.a k‖^2)
      ≤ Finset.sum F (fun k => h1Weight k * ‖u.toSeqD.a k‖^2) := by
    refine Finset.sum_le_sum ?_
    intro k _
    have h_weight := laplacianWeight_le_h1Weight k
    have h_sq_nonneg : 0 ≤ ‖u.toSeqD.a k‖^2 := sq_nonneg _
    exact mul_le_mul_of_nonneg_right h_weight h_sq_nonneg
  have h_v_bound : Finset.sum F (fun k => laplacianWeight k * ‖v.toSeqD.a k‖^2)
      ≤ Finset.sum F (fun k => h1Weight k * ‖v.toSeqD.a k‖^2) := by
    refine Finset.sum_le_sum ?_
    intro k _
    have h_weight := laplacianWeight_le_h1Weight k
    have h_sq_nonneg : 0 ≤ ‖v.toSeqD.a k‖^2 := sq_nonneg _
    exact mul_le_mul_of_nonneg_right h_weight h_sq_nonneg
  -- Apply InH1Ball hypotheses
  have h_u_h1 := hu F
  have h_v_h1 := hv F
  -- Chain the inequalities
  calc
    ‖Finset.sum F (fun k => (laplacianWeight k : ℂ) * u.toSeqD.a k * conj (v.toSeqD.a k))‖
        ≤ Real.sqrt (Finset.sum F (fun k => laplacianWeight k * ‖u.toSeqD.a k‖^2))
          * Real.sqrt (Finset.sum F (fun k => laplacianWeight k * ‖v.toSeqD.a k‖^2)) := h_cs
    _ ≤ Real.sqrt (Finset.sum F (fun k => h1Weight k * ‖u.toSeqD.a k‖^2))
        * Real.sqrt (Finset.sum F (fun k => h1Weight k * ‖v.toSeqD.a k‖^2)) := by
        have h_u_nonneg : 0 ≤ Finset.sum F (fun k => laplacianWeight k * ‖u.toSeqD.a k‖^2) :=
          Finset.sum_nonneg (fun k _ => mul_nonneg (laplacianWeight_nonneg k) (sq_nonneg _))
        have h_v_nonneg : 0 ≤ Finset.sum F (fun k => laplacianWeight k * ‖v.toSeqD.a k‖^2) :=
          Finset.sum_nonneg (fun k _ => mul_nonneg (laplacianWeight_nonneg k) (sq_nonneg _))
        have h_u_sqrt := Real.sqrt_le_sqrt h_u_bound
        have h_v_sqrt := Real.sqrt_le_sqrt h_v_bound
        exact mul_le_mul h_u_sqrt h_v_sqrt (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (R₁^2) * Real.sqrt (R₂^2) := by
        have h_u_sqrt := Real.sqrt_le_sqrt h_u_h1
        have h_v_sqrt := Real.sqrt_le_sqrt h_v_h1
        have h_R₁_nonneg : 0 ≤ Finset.sum F (fun k => h1Weight k * ‖u.toSeqD.a k‖^2) :=
          Finset.sum_nonneg (fun k _ => mul_nonneg (le_of_lt (ℓ2ZD.h1Weight_pos k)) (sq_nonneg _))
        have h_R₂_nonneg : 0 ≤ Finset.sum F (fun k => h1Weight k * ‖v.toSeqD.a k‖^2) :=
          Finset.sum_nonneg (fun k _ => mul_nonneg (le_of_lt (ℓ2ZD.h1Weight_pos k)) (sq_nonneg _))
        exact mul_le_mul h_u_sqrt h_v_sqrt (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = |R₁| * |R₂| := by simp [Real.sqrt_sq_eq_abs]

/-- The duality pairing is bounded. -/
lemma dualityPairingOn_bounded (F : Finset (Lattice spatialDim))
    (S : ℝ) (R : ℝ) (f : Hminus1Seq) (v : H1Seq)
    (hS : 0 ≤ S) (hR : 0 ≤ R)
    (hf : Finset.sum F (fun k => hminusWeight k * ‖f.coeff k‖^2) ≤ S^2)
    (hv : InH1Ball R v.toSeqD) :
    ‖dualityPairingOn F f v‖ ≤ S * R := by
  unfold dualityPairingOn

  -- Strategy: Factor each term as √(hminusWeight)·f · √(h1Weight)·v / 1
  -- then apply standard CS to the weighted coefficients
  calc
    ‖Finset.sum F (fun k => conj (f.coeff k) * v.coeff k)‖
        ≤ Finset.sum F (fun k => ‖f.coeff k‖ * ‖v.coeff k‖) := by
          calc ‖Finset.sum F (fun k => conj (f.coeff k) * v.coeff k)‖
              ≤ Finset.sum F (fun k => ‖conj (f.coeff k) * v.coeff k‖) := norm_sum_le _ _
          _ = Finset.sum F (fun k => ‖f.coeff k‖ * ‖v.coeff k‖) := by
              congr 1; ext k; simp
    _ = Finset.sum F (fun k => (Real.sqrt (hminusWeight k) * ‖f.coeff k‖)
                              * (Real.sqrt (h1Weight k) * ‖v.coeff k‖)) := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          -- Use hminusWeight * h1Weight = 1, so √(hminusWeight) * √(h1Weight) = 1
          have h_prod : hminusWeight k * h1Weight k = 1 := by
            unfold hminusWeight
            exact inv_mul_cancel₀ (ne_of_gt (ℓ2ZD.h1Weight_pos k))
          have h_sqrt_prod : Real.sqrt (hminusWeight k) * Real.sqrt (h1Weight k) = 1 := by
            rw [← Real.sqrt_mul (ℓ2ZD.hminusWeight_nonneg k), h_prod, Real.sqrt_one]
          calc ‖f.coeff k‖ * ‖v.coeff k‖
              = 1 * (‖f.coeff k‖ * ‖v.coeff k‖) := by ring
            _ = (Real.sqrt (hminusWeight k) * Real.sqrt (h1Weight k)) * (‖f.coeff k‖ * ‖v.coeff k‖) := by
                rw [h_sqrt_prod]
            _ = (Real.sqrt (hminusWeight k) * ‖f.coeff k‖) * (Real.sqrt (h1Weight k) * ‖v.coeff k‖) := by
                ring
    _ ≤ Real.sqrt (Finset.sum F (fun k => (Real.sqrt (hminusWeight k) * ‖f.coeff k‖)^2))
        * Real.sqrt (Finset.sum F (fun k => (Real.sqrt (h1Weight k) * ‖v.coeff k‖)^2)) := by
          have h_cs := Finset.sum_mul_sq_le_sq_mul_sq F
            (fun k => Real.sqrt (hminusWeight k) * ‖f.coeff k‖)
            (fun k => Real.sqrt (h1Weight k) * ‖v.coeff k‖)
          have h_nonneg : 0 ≤ Finset.sum F (fun k => (Real.sqrt (hminusWeight k) * ‖f.coeff k‖)
                                                      * (Real.sqrt (h1Weight k) * ‖v.coeff k‖)) := by
            refine Finset.sum_nonneg (fun k hk => ?_)
            exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
                             (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
          rw [← Real.sqrt_sq h_nonneg, ← Real.sqrt_mul (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
          exact Real.sqrt_le_sqrt h_cs
    _ = Real.sqrt (Finset.sum F (fun k => hminusWeight k * ‖f.coeff k‖^2))
        * Real.sqrt (Finset.sum F (fun k => h1Weight k * ‖v.coeff k‖^2)) := by
          congr 1 <;> (congr 1; refine Finset.sum_congr rfl (fun k hk => ?_))
          · rw [mul_pow, Real.sq_sqrt (ℓ2ZD.hminusWeight_nonneg k)]
          · simp only [H1Seq.coeff]
            rw [mul_pow, Real.sq_sqrt (le_of_lt (ℓ2ZD.h1Weight_pos k))]
    _ ≤ Real.sqrt (S^2) * Real.sqrt (R^2) := by
          refine mul_le_mul (Real.sqrt_le_sqrt hf) (Real.sqrt_le_sqrt (hv F))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = S * R := by rw [Real.sqrt_sq hS, Real.sqrt_sq hR]

/-! ## Coercivity -/

/-- Helper: For nonzero integer lattice points in dimension 1, the frequency is at least 1. -/
lemma dirichletFreq_sq_ge_one (k : Lattice spatialDim) (hk : k ≠ fun _ => 0) :
    1 ≤ (dirichletFreq k : ℝ)^2 := by
  have h_ne : dirichletFreq k ≠ 0 := by
    intro h_contra
    apply hk
    ext i
    fin_cases i
    exact h_contra
  have h_int : (dirichletFreq k : ℤ) ≠ 0 := h_ne
  have h_abs : 1 ≤ |(dirichletFreq k : ℤ)| := Int.one_le_abs h_int
  have h_sq : (1 : ℝ) ≤ ((dirichletFreq k : ℤ) : ℝ)^2 := by
    have h_abs_sq : (1 : ℝ) ≤ (|(dirichletFreq k : ℤ)| : ℝ)^2 := by
      have : (1 : ℝ) ≤ (|(dirichletFreq k : ℤ)| : ℝ) := by norm_cast
      nlinarith [sq_nonneg (|(dirichletFreq k : ℤ)| : ℝ)]
    calc (1 : ℝ) ≤ (|(dirichletFreq k : ℤ)| : ℝ)^2 := h_abs_sq
      _ = ((dirichletFreq k : ℤ) : ℝ)^2 := by simp only [sq_abs]
  exact h_sq

/-- Poincaré's inequality: gradient energy controls L² norm for mean-zero functions.
NOTE: The sharp constant for Dirichlet BC on (0,1) is 1/π², not 1/(4π²).
The factor of 4 appears in the torus H¹ weight but not in the Dirichlet Laplacian weight. -/
lemma poincare_inequality (F : Finset (Lattice spatialDim))
    (u : H1Seq) (h_meanZero : u.coeff (fun _ => 0) = 0) :
    Finset.sum F (fun k => ‖u.coeff k‖^2) ≤
      (1 / Real.pi^2) * gradEnergyOn F u.toSeqD := by
  unfold gradEnergyOn
  by_cases h_empty : F = ∅
  · simp [h_empty]
  -- The proof works uniformly: for each k in F, bound the term
  have h_mul : (1 / Real.pi^2) * Finset.sum F (fun k => laplacianWeight k * ‖u.toSeqD.a k‖^2) =
      Finset.sum F (fun k => (1 / Real.pi^2) * (laplacianWeight k * ‖u.toSeqD.a k‖^2)) := by
    rw [Finset.mul_sum]
  rw [h_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  simp only [H1Seq.coeff]
  by_cases hk_zero : k = fun _ => 0
  · -- k = 0 case
    subst hk_zero
    have h_zero : laplacianWeight (fun _ => 0) = 0 := by
      unfold laplacianWeight dirichletFreq
      simp
    have h_coeff_zero : u.toSeqD.a (fun _ => 0) = 0 := h_meanZero
    simp [h_zero, h_coeff_zero]
  · -- k ≠ 0 case
    have h_freq_ge : 1 ≤ (dirichletFreq k : ℝ)^2 := dirichletFreq_sq_ge_one k hk_zero
    calc ‖u.toSeqD.a k‖^2
        = (1 / Real.pi^2) * (Real.pi^2 * ‖u.toSeqD.a k‖^2) := by
          field_simp
      _ ≤ (1 / Real.pi^2) * (Real.pi^2 * ((dirichletFreq k : ℝ)^2 * ‖u.toSeqD.a k‖^2)) := by
          gcongr
          calc ‖u.toSeqD.a k‖^2 = 1 * ‖u.toSeqD.a k‖^2 := by ring
            _ ≤ (dirichletFreq k : ℝ)^2 * ‖u.toSeqD.a k‖^2 := by
              gcongr
      _ = (1 / Real.pi^2) * (laplacianWeight k * ‖u.toSeqD.a k‖^2) := by
          unfold laplacianWeight
          ring

/-- The bilinear form is coercive on mean-zero H¹ functions.
The bound α ≤ π² matches the sharp Poincaré constant for Dirichlet BC. -/
lemma bilinearForm_coercive (F : Finset (Lattice spatialDim))
    (u : H1Seq) (h_meanZero : u.coeff (fun _ => 0) = 0)
    (α : ℝ) (hα : 0 < α) (h_bound : α ≤ Real.pi^2) :
    α * Finset.sum F (fun k => ‖u.coeff k‖^2) ≤ (bilinearFormOn F u u).re := by
  rw [bilinearFormOn_eq_gradEnergy]
  have h_poincare := poincare_inequality F u h_meanZero
  have h_grad_nonneg : 0 ≤ gradEnergyOn F u.toSeqD := by
    unfold gradEnergyOn
    refine Finset.sum_nonneg fun k _ => ?_
    exact mul_nonneg (laplacianWeight_nonneg k) (sq_nonneg _)
  calc α * Finset.sum F (fun k => ‖u.coeff k‖^2)
      ≤ α * ((1 / Real.pi^2) * gradEnergyOn F u.toSeqD) := by
        gcongr
      _ = (α / Real.pi^2) * gradEnergyOn F u.toSeqD := by ring
      _ ≤ (Real.pi^2 / Real.pi^2) * gradEnergyOn F u.toSeqD := by
        gcongr
      _ = gradEnergyOn F u.toSeqD := by
        field_simp

end

end SemilinearHeat
