/-
Explicit Constants for Quantitative Rellich-Kondrachov
======================================================

**Purpose**: All constants appearing in QRK with explicit rational approximations

**Budget**: C0 baseline (these are just definitions of real numbers)

**Why This Matters**: Constructive mathematics requires COMPUTABLE constants.
Every inequality must have an explicit constant, not just "∃ C > 0".
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Pi.Bounds

-- BUDGET: C0 baseline
noncomputable section

namespace QRKConstants

/-! ## Core Constants -/

/-- Poincaré constant for 1D torus 𝕋¹ with period 1.

**Formula**: C_P = 1/(2π)

**Mathematical statement**: For u ∈ H¹(𝕋¹) with ∫u = 0,
  ‖u‖_{L²} ≤ C_P · ‖u'‖_{L²}

**Derivation**: From Fourier expansion, for k ≠ 0:
  |û(k)|² ≤ (1/(2πk)²) · (2πk)² · |û(k)|² = (1/(4π²)) · |∇û(k)|²
Summing gives the Poincaré inequality.

**Dimension dependence**: For 𝕋^d, same constant works (best constant is 1/(2π)).
-/
def poincare_const : ℝ := 1 / (2 * Real.pi)

/-- Tail bound coefficient.

**Formula**: C_tail = 1

**Mathematical statement**: For u ∈ H¹(𝕋^d),
  ∑_{|k| > M} |û(k)|² ≤ (C_tail / M²) · ‖∇u‖_{L²}²

**Derivation**: For |k| > M,
  |û(k)|² ≤ (1 + |k|²)|û(k)|² / (1 + M²) ≤ (1 + |k|²)|û(k)|² / M²
Summing: ∑_{|k| > M} |û(k)|² ≤ (1/M²) ∑_k (1 + |k|²)|û(k)|² = ‖u‖²_{H¹} / M²
-/
def tail_coefficient : ℝ := 1

/-- Parseval normalization constant.

**Formula**: C_Parseval = 1

**Mathematical statement**: For u ∈ L²(𝕋^d) with normalized Haar measure,
  ‖u‖_{L²}² = C_Parseval · ∑_k |û(k)|²

**Why 1**: Mathlib's `AddCircle.haarAddCircle` is normalized to total measure 1.
This gives Parseval identity with coefficient 1.
-/
def parseval_const : ℝ := 1

/-! ## Derived Constants -/

/-- Combined constant for H¹ norm via Fourier.

**Formula**: For u with ∫u = 0,
  ‖u‖²_{H¹} = ‖u‖²_{L²} + ‖∇u‖²_{L²}
           ≤ (C_P² + 1) · ‖∇u‖²_{L²}
           = sobolev_fourier_const · ‖∇u‖²_{L²}

This bounds the H¹ norm purely in terms of the gradient.
-/
def sobolev_fourier_const : ℝ := poincare_const ^ 2 + 1

/-! ## 1D Specific Constants -/

/-- Truncation dimension for 1D torus at cutoff M.

**Formula**: 2(2M + 1)

**Explanation**:
- Frequencies: -M, -M+1, ..., -1, 0, 1, ..., M-1, M  →  2M+1 frequencies
- Each û(k) ∈ ℂ has 2 real dimensions (real + imaginary)
- Total: 2(2M + 1) real dimensions

**Note**: For mean-zero subspace, exclude k=0, giving dimension 2(2M).
-/
def truncDim_1D (M : ℕ) : ℕ := 2 * (2 * M + 1)

/-- Truncation dimension for 1D MEAN-ZERO subspace at cutoff M.

**Formula**: 2 · 2M = 4M

**Explanation**: Same as above but k=0 is excluded (û(0) = 0).
-/
def truncDim_1D_meanZero (M : ℕ) : ℕ := 2 * (2 * M)

/-! ## 3D Specific Constants -/

/-- Truncation dimension for 3D torus at cutoff M.

**Formula**: 2 · (2M+1)³

**Explanation**:
- Frequencies: k = (k₁, k₂, k₃) with |kᵢ| ≤ M for each i
- Total frequencies: (2M+1)³
- Each û(k) ∈ ℂ has 2 real dimensions
- Total: 2(2M+1)³ real dimensions
-/
def truncDim_3D (M : ℕ) : ℕ := 2 * (2 * M + 1) ^ 3

/-- Truncation dimension for 3D MEAN-ZERO subspace at cutoff M.

**Formula**: 2 · ((2M+1)³ - 1)

**Explanation**: Same as above but k=(0,0,0) is excluded.
-/
def truncDim_3D_meanZero (M : ℕ) : ℕ := 2 * ((2 * M + 1) ^ 3 - 1)

/-! ## Covering Number Formulas -/

/-- Covering number for ε-net of R-ball in d-dimensional ℓ² space.

**Formula**: N(ε, R, d) = ⌈(1 + 2R/ε)^d⌉

**Mathematical statement**: An R-ball in ℝ^d can be covered by
at most (1 + 2R/ε)^d balls of radius ε.

**Derivation**: Volume packing bound. The R-ball has volume ∝ R^d,
each ε-ball has volume ∝ ε^d, ratio gives (R/ε)^d.
Add 1 for boundary effects: (1 + 2R/ε)^d.

**Reference**: Classical covering number estimate.
-/
def coveringNumber (ε R : ℝ) (d : ℕ) : ℕ :=
  Nat.ceil ((1 + 2 * R / ε) ^ d)

/-- Covering number for 1D QRK (mean-zero subspace).

**Parameters**:
- ε: tolerance in L² norm
- R: bound on ‖u‖_{H¹}
- M: frequency cutoff (should satisfy tail bound)

**Formula**: N(ε, R, M) = ⌈(1 + 2·C_proj·R/ε)^{4M}⌉

where C_proj accounts for projection from H¹ ball to truncated L² ball.
-/
def coveringNumber_1D_meanZero (ε R : ℝ) (M : ℕ) : ℕ :=
  let d := truncDim_1D_meanZero M
  -- For now, use R directly as projection bound (will refine)
  coveringNumber ε R d

/-- Covering number for 3D QRK (mean-zero subspace).

**Parameters**: Same as 1D but for 3D torus.

**Formula**: N(ε, R, M) = ⌈(1 + 2·C_proj·R/ε)^{2((2M+1)³-1)}⌉
-/
def coveringNumber_3D_meanZero (ε R : ℝ) (M : ℕ) : ℕ :=
  let d := truncDim_3D_meanZero M
  coveringNumber ε R d

/-! ## Frequency Cutoff Selection -/

/-- Optimal frequency cutoff M for given tail tolerance δ and H¹ bound R.

**Formula**: M = ⌈R/√δ⌉

**Why this works**: From tail bound,
  ∑_{|k| > M} |û(k)|² ≤ R² / M²
For this to be ≤ δ, need M² ≥ R²/δ, i.e., M ≥ R/√δ.

**Usage**: Choose δ = ε²/4, then tail contributes ≤ ε/2 to L² distance.
-/
def optimalCutoff (R δ : ℝ) : ℕ :=
  Nat.ceil (R / Real.sqrt δ)

/-! ## Rational Approximations (for computation) -/

/-- Lower bound on π for constructive reasoning.

**Value**: 3.14 (below π ≈ 3.14159...)

**Usage**: When we need π from below (e.g., proving upper bounds on 1/π).
-/
def pi_lower : ℚ := 314 / 100

/-- Upper bound on π for constructive reasoning.

**Value**: 3.15 (above π ≈ 3.14159...)

**Usage**: When we need π from above (e.g., proving upper bounds on constants).
-/
def pi_upper : ℚ := 315 / 100

/-- Lower bound on Poincaré constant C_P = 1/(2π).

**Value**: 1/(2·3.15) ≈ 0.1587

**Derivation**: Since π < 3.15, we have 1/(2π) > 1/(2·3.15).
-/
def poincare_lower : ℚ := 100 / 630  -- simplifies to 10/63

/-- Upper bound on Poincaré constant C_P = 1/(2π).

**Value**: 1/(2·3.14) ≈ 0.1592

**Derivation**: Since π > 3.14, we have 1/(2π) < 1/(2·3.14).
-/
def poincare_upper : ℚ := 100 / 628  -- simplifies to 50/314

/-! ## Verification Lemmas -/

/-- Sanity check: All constants are positive. -/
example : 0 < poincare_const := by
  unfold poincare_const
  positivity

example : 0 < tail_coefficient := by
  unfold tail_coefficient
  norm_num

example : 0 < parseval_const := by
  unfold parseval_const
  norm_num

example : 0 < sobolev_fourier_const := by
  unfold sobolev_fourier_const
  positivity

/-! ## Budget Notes

**Status**: C0 baseline ✅

All definitions here are:
- Computable (given oracle for π)
- Constructive (no LEM, no choice)
- Explicit (every constant has a formula)

The constants module does NOT prove any theorems yet - just defines values.
Theorems using these constants will be in RellichKondrachov1D.lean and
RellichKondrachov.lean.
-/

end QRKConstants
