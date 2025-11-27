import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Budgets.RellichKondrachovInterval.Core

/-!
# Sine-basis infrastructure on `[0,1]`

We model Dirichlet test functions via their sine coefficients, mirroring the
sequence-based approach used on the torus.  This file introduces:

* sine modes `mode k x = √2 sin(π k x)`;
* the `FiniteSine` structure capturing finitely supported coefficient lists;
* evaluation of such a finite sine series;
* L² and H¹ seminorms via Parseval identities.
-/

open scoped Real

namespace RellichKondrachovInterval

/-- Normalised sine mode implementing the Dirichlet eigenfunctions. -/
noncomputable def sineMode (k : ℕ) (x : ℝ) : ℝ :=
  Real.sqrt 2 * Real.sin (Real.pi * (k.succ : ℝ) * x)

/-- Finitely-supported sine series used as test functions. -/
structure FiniteSine where
  coeffs : ℕ → ℝ
  support : Finset ℕ
  support_spec : ∀ k ∉ support, coeffs k = 0

namespace FiniteSine

/-- Evaluate the sine series on a real input. -/
noncomputable def eval (f : FiniteSine) (x : ℝ) : ℝ :=
  Finset.sum f.support fun k => f.coeffs k * sineMode k x

/-- L² norm squared on the interval `[0,1]`. -/
noncomputable def l2IntervalSq (f : FiniteSine) : ℝ :=
  Finset.sum f.support fun k => (f.coeffs k)^2

/-- H¹ seminorm squared on `[0,1]`. -/
noncomputable def h1IntervalSq (f : FiniteSine) : ℝ :=
  Finset.sum f.support fun k =>
    (Real.pi * (k.succ : ℝ))^2 * (f.coeffs k)^2

/-- L² norm squared on the torus after odd extension. -/
noncomputable def l2TorusSq (f : FiniteSine) : ℝ :=
  2 * l2IntervalSq f

/-- H¹ seminorm squared on the torus after odd extension. -/
noncomputable def h1TorusSq (f : FiniteSine) : ℝ :=
  2 * h1IntervalSq f

lemma l2TorusSq_eq (f : FiniteSine) : l2TorusSq f = 2 * l2IntervalSq f := rfl

lemma h1TorusSq_eq (f : FiniteSine) : h1TorusSq f = 2 * h1IntervalSq f := rfl

/-- Odd extension scales L² norm by √2. -/
lemma oddExtend_l2_norm (f : FiniteSine) :
    Real.sqrt (l2TorusSq f) = Real.sqrt 2 * Real.sqrt (l2IntervalSq f) := by
  classical
  have h0 : 0 ≤ l2IntervalSq f := by
    have hterm :
        ∀ k ∈ f.support, 0 ≤ (f.coeffs k)^2 :=
      by
        intro k hk
        exact sq_nonneg _
    simpa [l2IntervalSq] using Finset.sum_nonneg hterm
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  simp [l2TorusSq]

/-- Odd extension scales H¹ norm by √2. -/
lemma oddExtend_h1_norm (f : FiniteSine) :
    Real.sqrt (h1TorusSq f) = Real.sqrt 2 * Real.sqrt (h1IntervalSq f) := by
  classical
  have h0 : 0 ≤ h1IntervalSq f := by
    have hterm :
        ∀ k ∈ f.support,
            0 ≤ (Real.pi * (k.succ : ℝ))^2 * (f.coeffs k)^2 :=
      by
        intro k hk
        have hcoeff : 0 ≤ (f.coeffs k)^2 := sq_nonneg _
        have hfreq : 0 ≤ (Real.pi * (k.succ : ℝ))^2 := sq_nonneg _
        exact mul_nonneg hfreq hcoeff
    simpa [h1IntervalSq] using Finset.sum_nonneg hterm
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  simp [h1TorusSq]

end FiniteSine

end RellichKondrachovInterval
