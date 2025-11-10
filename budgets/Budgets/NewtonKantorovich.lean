import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz
import Budgets.BanachExtraction

/-
# Newton–Kantorovich scaffolding

This file sets up the common structures we will use for the Newton demo.
In particular we package the parameters and hypotheses needed to turn
Newton iteration into a contraction map.  Detailed estimates and the
constructive extraction will be added in subsequent commits.
-/

namespace BanachNewton

noncomputable section

open scoped Classical ENNReal
open Real
open Set

/-- Parameters describing a one-dimensional Newton setup around an initial guess. -/
structure NewtonParams where
  f : ℝ → ℝ
  f' : ℝ → ℝ
  x₀ : ℝ
  radius : ℝ
  L : ℝ
  β : ℝ
  γ : ℝ

/-- Newton map associated with `(f, f')`. -/
def newtonMap (p : NewtonParams) : ℝ → ℝ :=
  fun x => x - p.f x / p.f' p.x₀

/-- Convenience wrapper: the closed ball around `x₀` with radius `r`. -/
def domainBall (p : NewtonParams) : Set ℝ :=
  {x | |x - p.x₀| ≤ p.radius}

/-- Hypotheses ensuring the Newton map is a contraction on the closed ball. -/
structure KantorovichHypotheses where
  params : NewtonParams
  hfDiff : DifferentiableOn ℝ params.f (domainBall params)
  derivative_bound :
    ∀ ⦃x⦄, x ∈ domainBall params →
      |params.f' x - params.f' params.x₀| ≤ params.L * |x - params.x₀|
  inverse_bound : |(params.f' params.x₀)⁻¹| ≤ params.β
  lipschitz_small : params.β * params.L ≤ (1 : ℝ) / 2
  residual_bound : |params.f params.x₀| ≤ params.γ
  gamma_le_radius : params.γ ≤ params.radius

namespace KantorovichHypotheses

/-- The Newton map attached to a hypothesis package. -/
def map (h : KantorovichHypotheses) : ℝ → ℝ :=
  newtonMap h.params

/-- The working domain. -/
def domain (h : KantorovichHypotheses) : Set ℝ :=
  domainBall h.params

end KantorovichHypotheses

-- Concrete example: Newton iteration for sqrt(2) on the interval [1, 2].
namespace SqrtExample

def domainSet : Set ℝ := Set.Icc (1 : ℝ) 2

def map (x : ℝ) : ℝ := x / 2 + 1 / x

lemma map_mem_domain {x : ℝ} (hx : x ∈ domainSet) : map x ∈ domainSet := by
  rcases hx with ⟨hx₁, hx₂⟩
  have hx_pos : 0 < x := by linarith
  have hx_ne : x ≠ 0 := by linarith
  constructor
  · -- Lower bound: 1 ≤ map x
    have h : 2 * x ≤ x ^ 2 + 2 := by nlinarith [sq_nonneg (x - 1)]
    calc 1 = (2 * x) / (2 * x) := by field_simp
      _ ≤ (x ^ 2 + 2) / (2 * x) := by gcongr
      _ = x / 2 + 1 / x := by field_simp [hx_ne]
  · -- Upper bound: map x ≤ 2
    have h : x ^ 2 + 2 ≤ 3 * x := by nlinarith [sq_nonneg x, sq_nonneg (x - 1)]
    calc map x = x / 2 + 1 / x := rfl
      _ = (x ^ 2 + 2) / (2 * x) := by field_simp [hx_ne]
      _ ≤ (3 * x) / (2 * x) := by gcongr
      _ = 3 / 2 := by field_simp [hx_ne]
      _ ≤ 2 := by norm_num

lemma map_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt map (1 / 2 - 1 / x ^ 2) x := by
  have h₁ : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
    convert hasDerivAt_id x |>.mul_const (1 / 2) using 1
    · ext; simp only [id]; ring
    · ring
  have h₂ : HasDerivAt (fun y : ℝ => y⁻¹) (- (x⁻¹ * x⁻¹)) x := by
    convert hasDerivAt_inv hx using 1
    rw [pow_two]; ring
  have h_eq : (fun y => y / 2 + y⁻¹) = map := by
    ext y; simp only [map]; ring
  rw [← h_eq]
  convert h₁.add h₂ using 1
  field_simp [pow_two]
  ring

lemma map_deriv {x : ℝ} (hx : x ≠ 0) :
    deriv map x = 1 / 2 - 1 / x ^ 2 := by
  simpa [map_hasDerivAt hx, one_div, pow_two, div_eq_mul_inv]
    using (map_hasDerivAt hx).deriv

lemma map_differentiableAt {x : ℝ} (hx : x ∈ domainSet) :
    DifferentiableAt ℝ map x := by
  have hx₁ : (1 : ℝ) ≤ x := hx.left
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx₁
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  exact (map_hasDerivAt hx_ne).differentiableAt

lemma map_deriv_abs {x : ℝ} (hx : x ∈ domainSet) :
    |deriv map x| ≤ (1 / 2 : ℝ) := by
  classical
  have hx₁ : (1 : ℝ) ≤ x := hx.left
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx₁
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  have hx_inv_sq_nonneg : 0 ≤ 1 / x ^ 2 := by
    have : 0 ≤ x ^ 2 := sq_nonneg x
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) this
  have h_expr : deriv map x = 1 / 2 - 1 / x ^ 2 := map_deriv hx_ne
  have h_upper : deriv map x ≤ 1 / 2 := by
    rw [h_expr]
    exact sub_le_self (1 / 2 : ℝ) hx_inv_sq_nonneg
  have h_lower : -(1 / 2 : ℝ) ≤ deriv map x := by
    have : 0 ≤ deriv map x + 1 / 2 := by
      have hx_sq_pos : 0 < x ^ 2 := pow_pos hx_pos 2
      have hx_sq_ge : (1 : ℝ) ≤ x ^ 2 := by
        have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
        calc x ^ 2 = x * x := pow_two x
          _ ≥ 1 * 1 := mul_le_mul hx₁ hx₁ (by norm_num : (0 : ℝ) ≤ 1) hx_nonneg
          _ = 1 := by norm_num
      have hx_inv_sq_le_one : 1 / x ^ 2 ≤ 1 := by
        rw [div_le_iff₀ hx_sq_pos]
        simpa using hx_sq_ge
      have : 0 ≤ 1 - 1 / x ^ 2 := sub_nonneg.mpr hx_inv_sq_le_one
      rw [h_expr]
      linarith
    linarith
  exact abs_le.2 ⟨h_lower, h_upper⟩

lemma map_deriv_nnnorm_le {x : ℝ} (hx : x ∈ domainSet) :
    ‖deriv map x‖₊ ≤ (1 / 2 : NNReal) := by
  have h := map_deriv_abs hx
  -- For reals, ‖x‖₊ = Real.toNNReal |x|, and |x| ≤ 1/2 gives us what we need
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
  exact h

lemma lipschitz : LipschitzOnWith (1 / 2 : NNReal) map domainSet := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
  · intro x hx
    exact map_differentiableAt hx
  · intro x hx
    exact map_deriv_nnnorm_le hx
  · exact convex_Icc 1 2

/-- The subtype representing the interval `[1,2]`. -/
def Domain := {x : ℝ // x ∈ domainSet}

instance : MetricSpace Domain := Subtype.metricSpace

/-- Newton iteration as a self-map on the interval `[1,2]`. -/
def mapSubtype (x : Domain) : Domain := ⟨map x.val, map_mem_domain x.property⟩

lemma mapSubtype_lipschitz :
    ∀ x y : Domain,
      dist (mapSubtype x) (mapSubtype y) ≤ (1 / 2 : ℝ) * dist x y := by
  intro x y
  -- Use the dist formulation of LipschitzOnWith
  have h : dist (map x.val) (map y.val) ≤ (1 / 2 : NNReal) * dist x.val y.val :=
    lipschitz.dist_le_mul x.val x.property y.val y.property
  simp only [mapSubtype] at h ⊢
  exact h

/-- Contraction data for Newton iteration approximating `√2`. -/
def contractionData : ContractionData Domain :=
{ f := mapSubtype
, K := 1 / 2
, K_nonneg := by norm_num
, K_lt_one := by norm_num
, lipschitz := mapSubtype_lipschitz }

end SqrtExample

end -- noncomputable section

end BanachNewton
