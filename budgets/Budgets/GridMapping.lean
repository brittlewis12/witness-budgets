import Budgets.RellichKondrachovD.Core
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Grid Mapping: Array ↔ Lattice Bijection

This module provides a bijection between lattice points in [-M,M]ᵈ and
flat array indices for computational representation.

## Main definitions

- `toIdx`: Maps lattice point k ∈ [-M,M] to array index [0, 2M]
- `fromIdx`: Maps array index to lattice point
- `arraySize`: Total number of elements in the grid (2M+1)^d
- `validIdx`: Predicate for valid array indices

## Key theorems

- `toIdx_fromIdx`: Round-trip from index to lattice and back
- `fromIdx_toIdx`: Round-trip from lattice to index and back (for valid lattice points)

## Implementation notes

Provides both 1D (specialized) and multi-dimensional (row-major) indexing:
- 1D: k ∈ [-M,M] maps to i = k + M ∈ [0, 2M]
- Multi-D: Row-major ordering with index = ∑ᵢ (kᵢ + M) · (2M+1)^i
-/

namespace GridMapping

open ℓ2ZD

/-! ## Type definitions and basic operations -/

/-! ### Multi-dimensional row-major indexing -/

/-- Row-major index for d-dimensional lattice point k ∈ [-M,M]ᵈ
    Formula: index = ∑ᵢ (kᵢ + M) · (2M+1)^i

    Example (2D with M=1): k=(-1,1) → offsets=(0,2) → index = 0 + 2·3 = 6
-/
def toIdxMultiDim {d : ℕ} (k : Lattice d) (M : ℕ) : ℕ :=
  Finset.sum (Finset.univ : Finset (Fin d)) fun i =>
    let offset := Int.toNat (k i + M)
    offset * (2 * M + 1) ^ (i : ℕ)

/-- Inverse row-major mapping: flat index → d-dimensional lattice point
    Uses repeated division to extract each coordinate
-/
def fromIdxMultiDim {d : ℕ} (idx : ℕ) (M : ℕ) : Lattice d :=
  fun i =>
    let stride := (2 * M + 1) ^ (i : ℕ)
    let coord := (idx / stride) % (2 * M + 1)
    (coord : ℤ) - M

/-! ### 1D specialized indexing (optimized) -/

/-- Map lattice point k ∈ [-M,M] to array index.
    For 1D: k ∈ [-M,M] maps to i = k + M ∈ [0, 2M] -/
def toIdx {d : ℕ} [NeZero d] (k : Lattice d) (M : ℕ) : ℕ :=
  Int.toNat (k ⟨0, NeZero.pos d⟩ + M)

/-- Map array index back to lattice point.
    For 1D: i ∈ [0, 2M] maps to k = i - M ∈ [-M,M] -/
def fromIdx {d : ℕ} [NeZero d] (i : ℕ) (M : ℕ) : Lattice d :=
  fun j => if j = ⟨0, NeZero.pos d⟩ then (i : ℤ) - M else 0

/-- Array size for M modes in d dimensions.
    Currently: (2M + 1)^d -/
def arraySize (M : ℕ) (d : ℕ := 1) : ℕ := (2 * M + 1) ^ d

/-- Valid index predicate: index must be in bounds -/
def validIdx (i : ℕ) (M : ℕ) (d : ℕ := 1) : Prop := i < arraySize M d

/-! ## Helper lemmas -/

/-- If i < 2M+1, then i ≤ 2M -/
private lemma lt_twoM_plus_one_imp_le (i M : ℕ) (h : i < 2 * M + 1) : i ≤ 2 * M := by
  omega

/-- If i < 2M+1, then 0 ≤ (i : ℤ) - M ≤ M -/
private lemma valid_idx_bounds (i M : ℕ) (h : i < 2 * M + 1) :
    -(M : ℤ) ≤ (i : ℤ) - M ∧ (i : ℤ) - M ≤ M := by
  constructor
  · have h1 : (0 : ℤ) ≤ i := Int.natCast_nonneg i
    omega
  · have h2 : i ≤ 2 * M := lt_twoM_plus_one_imp_le i M h
    have : (i : ℤ) ≤ (2 * M : ℤ) := by exact_mod_cast Nat.le_of_succ_le_succ (Nat.succ_le_of_lt h)
    omega

/-- For k ∈ [-M,M], we have 0 ≤ k + M -/
private lemma lattice_in_range_nonneg (k : ℤ) (M : ℕ) (h : -(M : ℤ) ≤ k ∧ k ≤ M) :
    0 ≤ k + M := by
  omega

/-- For k ∈ [-M,M], we have k + M ≤ 2M -/
private lemma lattice_in_range_le (k : ℤ) (M : ℕ) (h : -(M : ℤ) ≤ k ∧ k ≤ M) :
    k + M ≤ 2 * M := by
  omega

/-! ## Bijection theorems -/

/-- Round-trip property: fromIdx ∘ toIdx = id on valid 1D indices.
    This encoding only uses the first dimension, so it only works for
    indices in the 1D range [0, 2M]. For higher dimensions, indices beyond
    this range would map to lattice points outside [-M,M] in dimension 0. -/
theorem toIdx_fromIdx {d : ℕ} [NeZero d] (M : ℕ) (i : ℕ) (h : i < 2 * M + 1) :
    toIdx (fromIdx i M : Lattice d) M = i := by
  unfold toIdx fromIdx at *
  let i0 : Fin d := Fin.mk 0 (NeZero.pos d)
  -- Simplify: fromIdx returns i - M at position 0, toIdx adds M and converts to Nat
  simp only [ite_true]
  have hnonneg : 0 ≤ (i : ℤ) - M + M := by
    have := valid_idx_bounds i M h
    omega
  have eq1 : (↑i - ↑M + ↑M : ℤ).toNat = i := by
    have : (↑i - ↑M + ↑M : ℤ) = ↑i := by ring
    rw [this, Int.toNat_natCast]
  exact eq1

/-- Round-trip property: fromIdx ∘ toIdx = id on valid lattice points.
    If k ∈ [-M,M]ᵈ (only checking dimension 0 for 1D), then
    fromIdx (toIdx k M) M = k.

    For d > 1, we require that k is "1D-like", meaning all components
    except the first are zero. This matches our 1D encoding where only
    dimension 0 is stored in the array index. -/
theorem fromIdx_toIdx {d : ℕ} [NeZero d] (M : ℕ) (k : Lattice d)
    (h : -(M : ℤ) ≤ k ⟨0, NeZero.pos d⟩ ∧ k ⟨0, NeZero.pos d⟩ ≤ M)
    (h1d : ∀ i : Fin d, i ≠ ⟨0, NeZero.pos d⟩ → k i = 0) :
    fromIdx (toIdx k M) M = k := by
  unfold toIdx fromIdx
  funext i
  by_cases hi : i = ⟨0, NeZero.pos d⟩
  · -- Case i = 0: need to show (toNat (k 0 + M) : ℤ) - M = k 0
    simp only [hi, ite_true]
    have hnonneg : 0 ≤ k ⟨0, NeZero.pos d⟩ + M := lattice_in_range_nonneg (k ⟨0, NeZero.pos d⟩) M h
    rw [Int.toNat_of_nonneg hnonneg]
    ring
  · -- Case i ≠ 0: use the 1D hypothesis
    simp only [hi, ite_false]
    exact (h1d i hi).symm

/-! ## Range lemmas -/

/-- If k is in the valid range, then toIdx produces a valid index -/
theorem toIdx_valid {d : ℕ} [NeZero d] (M : ℕ) (k : Lattice d)
    (h : -(M : ℤ) ≤ k ⟨0, NeZero.pos d⟩ ∧ k ⟨0, NeZero.pos d⟩ ≤ M) :
    validIdx (toIdx k M) M d := by
  unfold validIdx toIdx arraySize
  have hnonneg : 0 ≤ k ⟨0, NeZero.pos d⟩ + M := lattice_in_range_nonneg (k ⟨0, NeZero.pos d⟩) M h
  have hle : k ⟨0, NeZero.pos d⟩ + M ≤ 2 * M := lattice_in_range_le (k ⟨0, NeZero.pos d⟩) M h
  have hnat : (k ⟨0, NeZero.pos d⟩ + M).toNat ≤ 2 * M := by
    have h1 := Int.toNat_le_toNat hle
    have h2 : (2 * M : ℤ).toNat = 2 * M := Int.toNat_natCast (2 * M)
    rw [← h2]
    exact h1
  obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  cases d' with
  | zero => -- d = 1
    simp only [Nat.pow_one]
    calc (k ⟨0, NeZero.pos 1⟩ + M).toNat
        ≤ 2 * M := hnat
      _ < 2 * M + 1 := by omega
  | succ d'' => -- d ≥ 2
    calc (k ⟨0, NeZero.pos (d'' + 2)⟩ + M).toNat
        ≤ 2 * M := hnat
      _ < 2 * M + 1 := by omega
      _ ≤ (2 * M + 1) ^ (d'' + 2) := by
        apply Nat.le_self_pow
        omega

/-- If i is a valid 1D index, then fromIdx produces a lattice point in range.
    This is restricted to i < 2M+1 since the encoding only uses dimension 0. -/
theorem fromIdx_inRange {d : ℕ} [NeZero d] (M : ℕ) (i : ℕ) (h : i < 2 * M + 1) :
    -(M : ℤ) ≤ (fromIdx i M : Lattice d) ⟨0, NeZero.pos d⟩ ∧
    (fromIdx i M : Lattice d) ⟨0, NeZero.pos d⟩ ≤ M := by
  unfold fromIdx at *
  let i0 : Fin d := Fin.mk 0 (NeZero.pos d)
  show -(M : ℤ) ≤ (if i0 = i0 then (i : ℤ) - M else 0) ∧
       (if i0 = i0 then (i : ℤ) - M else 0) ≤ M
  simp only [ite_true]
  exact valid_idx_bounds i M h

/-! ## Injectivity -/

/-- toIdx is injective on valid lattice points (in dimension 0) -/
theorem toIdx_injective {d : ℕ} [NeZero d] (M : ℕ) (k₁ k₂ : Lattice d)
    (h₁ : -(M : ℤ) ≤ k₁ ⟨0, NeZero.pos d⟩ ∧ k₁ ⟨0, NeZero.pos d⟩ ≤ M)
    (h₂ : -(M : ℤ) ≤ k₂ ⟨0, NeZero.pos d⟩ ∧ k₂ ⟨0, NeZero.pos d⟩ ≤ M)
    (heq : toIdx k₁ M = toIdx k₂ M) :
    k₁ ⟨0, NeZero.pos d⟩ = k₂ ⟨0, NeZero.pos d⟩ := by
  unfold toIdx at heq
  have hn₁ : 0 ≤ k₁ ⟨0, NeZero.pos d⟩ + M := lattice_in_range_nonneg (k₁ ⟨0, NeZero.pos d⟩) M h₁
  have hn₂ : 0 ≤ k₂ ⟨0, NeZero.pos d⟩ + M := lattice_in_range_nonneg (k₂ ⟨0, NeZero.pos d⟩) M h₂
  -- Use that toNat is injective on nonnegative integers
  have : k₁ ⟨0, NeZero.pos d⟩ + M = k₂ ⟨0, NeZero.pos d⟩ + M := by
    have h1 := Int.toNat_of_nonneg hn₁
    have h2 := Int.toNat_of_nonneg hn₂
    omega
  omega

/-- fromIdx is injective -/
theorem fromIdx_injective {d : ℕ} [NeZero d] (M : ℕ) (i₁ i₂ : ℕ)
    (heq : (fromIdx i₁ M : Lattice d) = (fromIdx i₂ M : Lattice d)) :
    i₁ = i₂ := by
  have : (fromIdx i₁ M : Lattice d) ⟨0, NeZero.pos d⟩ = (fromIdx i₂ M : Lattice d) ⟨0, NeZero.pos d⟩ := by
    rw [heq]
  unfold fromIdx at this
  simp only [ite_true] at this
  omega

/-! ## Size bounds -/

/-- The array size is positive for any M -/
theorem arraySize_pos (M d : ℕ) : 0 < arraySize M d := by
  unfold arraySize
  apply Nat.pow_pos
  omega

/-- For d=1, array size equals 2M+1 -/
theorem arraySize_one (M : ℕ) : arraySize M 1 = 2 * M + 1 := by
  unfold arraySize
  simp

end GridMapping
