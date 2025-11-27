import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum

/-!
# Interval variants of the QRK infrastructure

This file introduces the basic domain/coordinate definitions that will be used to
port the quantitative Rellich–Kondrachov theorem from the torus to the
interval `(0, 1)` with Dirichlet boundary conditions.

The goal for now is to provide:
* A convenient name for the closed interval `[0,1]`.
* A helper that folds any real number back into `[0,1]` using the standard
  "sawtooth" pattern (period `2` with an odd reflection).
* A corresponding sign helper, used when extending Dirichlet data to
  odd 2-periodic functions.
* A plain function-level odd 2-periodic extension `oddPeriodicExtend` that will
  later be lifted to the Sobolev/L² settings.

All the quantitative/analytic lemmas will live in subsequent files; this module
just provides the raw definitions together with rich docstrings describing the
intended behaviour.
-/

namespace RellichKondrachovInterval

open scoped Real

/-- The closed unit interval `[0, 1]` viewed as a set. -/
def interval01Set : Set ℝ := Set.Icc (0 : ℝ) (1 : ℝ)

@[simp] lemma mem_interval01Set {x : ℝ} :
    x ∈ interval01Set ↔ 0 ≤ x ∧ x ≤ 1 := Iff.rfl

/--
Fold a real number onto the interval `[0, 2)` using the `Real.fract` helper.
The quantity `foldSeed x := 2 * fract (x / 2)` keeps track of where `x`
lands inside a single period when working with 2-periodic functions.

Later on we will prove the expected algebraic properties (periodicity,
bounds), but having a dedicated definition up front makes subsequent code
clearer.
-/
noncomputable def foldSeed (x : ℝ) : ℝ := 2 * Int.fract (x / 2)

lemma foldSeed_add_two (x : ℝ) : foldSeed (x + 2) = foldSeed x := by
  have hx : (x + 2) / (2 : ℝ) = x / 2 + 1 := by
    have hx' : (x + 2) / (2 : ℝ) = x / 2 + (2 : ℝ) / 2 := by
      simpa using add_div x 2 (2 : ℝ)
    simpa using hx'
  simp [foldSeed, hx]

lemma foldSeed_nonneg (x : ℝ) : 0 ≤ foldSeed x := by
  have h := Int.fract_nonneg (x / 2)
  have h₂ : 0 ≤ (2 : ℝ) := by norm_num
  exact mul_nonneg h₂ h

lemma foldSeed_lt_two (x : ℝ) : foldSeed x < 2 := by
  have h := Int.fract_lt_one (x / 2)
  have h₂ : (0 : ℝ) < 2 := by norm_num
  have := mul_lt_mul_of_pos_left h h₂
  simpa [foldSeed] using this

/--
"Sawtooth" folding that sends any real number to `[0,1]`.

The definition first reduces to a number inside `[0,2)` (via `foldSeed`) and
then reflects across `1` whenever necessary.  Intuitively this is the unique
continuous map such that:

* `foldToUnit01 x = x` for `x ∈ [0,1]`;
* `foldToUnit01 x = 2 - x` for `x ∈ [1,2]`;
* `foldToUnit01` is 2-periodic.

We will prove these facts later in the development.
-/
noncomputable def foldToUnit01 (x : ℝ) : ℝ :=
  let t := foldSeed x
  if t ≤ 1 then t else 2 - t

lemma foldToUnit01_eq_of_le {x : ℝ} (h : foldSeed x ≤ 1) :
    foldToUnit01 x = foldSeed x := by
  simp [foldToUnit01, h]

lemma foldToUnit01_eq_two_sub_of_gt {x : ℝ} (h : 1 < foldSeed x) :
    foldToUnit01 x = 2 - foldSeed x := by
  simp [foldToUnit01, not_le.mpr h]

lemma foldToUnit01_mem (x : ℝ) : foldToUnit01 x ∈ interval01Set := by
  classical
  by_cases h : foldSeed x ≤ 1
  · have hx := foldSeed_nonneg x
    simp [interval01Set, foldToUnit01_eq_of_le h, hx, h]
  · have hgt : 1 < foldSeed x := lt_of_not_ge h
    have hx_le : foldSeed x ≤ 2 := le_of_lt (foldSeed_lt_two x)
    have hx_ge : (1 : ℝ) ≤ foldSeed x := le_of_lt hgt
    have hnonneg : 0 ≤ 2 - foldSeed x := sub_nonneg.mpr hx_le
    have hx_sum' : (2 : ℝ) ≤ 1 + foldSeed x := by
      have htwo : (2 : ℝ) = 1 + 1 := by norm_num
      simpa [htwo] using add_le_add_left hx_ge 1
    have hx_sum_right : (2 : ℝ) ≤ foldSeed x + 1 := by
      simpa [add_comm] using hx_sum'
    have hle : 2 - foldSeed x ≤ 1 := sub_le_iff_le_add'.mpr hx_sum_right
    simp [interval01Set, foldToUnit01_eq_two_sub_of_gt hgt, hnonneg, hle]

/--
Sign bookkeeping for the odd 2-periodic extension.

`foldSign x` returns `+1` when `x` folds into `[0,1]` with the original
orientation, and `-1` when the reflection branch is chosen.  This ensures that
`oddPeriodicExtend` will be odd and 2-periodic once the corresponding lemmas
are established.
-/
noncomputable def foldSign (x : ℝ) : ℝ :=
  let t := foldSeed x
  if t ≤ 1 then 1 else -1

lemma foldSign_eq_one_of_le {x : ℝ} (h : foldSeed x ≤ 1) : foldSign x = 1 := by
  simp [foldSign, h]

lemma foldSign_eq_neg_one_of_gt {x : ℝ} (h : 1 < foldSeed x) : foldSign x = -1 := by
  simp [foldSign, not_le.mpr h]

lemma foldSign_sq (x : ℝ) : foldSign x ^ 2 = 1 := by
  classical
  by_cases h : foldSeed x ≤ 1
  · have : foldSign x = 1 := foldSign_eq_one_of_le h
    simp [this]
  · have hx : 1 < foldSeed x := lt_of_not_ge h
    have : foldSign x = -1 := foldSign_eq_neg_one_of_gt hx
    simp [this]

/--
Plain odd 2-periodic extension of a function defined on `[0,1]`.

`oddPeriodicExtend u` is defined for *all* real numbers by first folding the
input back to `[0,1]` (`foldToUnit01`) and then attaching the correct sign to
keep the extension odd (`foldSign`).  This definition deliberately works with
plain functions `ℝ → ℂ`; the Sobolev/L² lifting will happen in later files so
that we can keep the algebraic reasoning separate from the analytic proofs.
-/
noncomputable def oddPeriodicExtend (u : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (foldSign x) * u (foldToUnit01 x)

end RellichKondrachovInterval
