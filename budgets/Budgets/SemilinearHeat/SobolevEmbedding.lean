import Mathlib
import Budgets.SemilinearHeat.BilinearForm
import Budgets.SemilinearHeat.SobolevSeq
import Budgets.RellichKondrachovD.Core

/-!
# Sobolev Embedding H¹(0,1) ↪ L∞(0,1)

This file proves the constructive Sobolev embedding theorem for the 1D Dirichlet problem.

## Main Theorem

`sobolev_embedding_H1_Linfty`: ‖u‖_{L∞} ≤ √C∞² · ‖u‖_{H¹}

This unlocks the cubic_map_inHminus proof in CubicConvolution.lean.
-/

namespace SemilinearHeat

open BigOperators Complex Real Set
open scoped ComplexConjugate
open ℓ2ZD (Lattice SeqD InH1Ball InHminusBall h1Weight hminusWeight)

noncomputable section

/-! ## Part 1: Dirichlet Basis Functions -/

/-- The k-th Dirichlet basis function: eₖ(x) = √2 · sin(kπx) -/
def dirichletBasis (k : ℕ+) (x : ℝ) : ℝ :=
  Real.sqrt 2 * Real.sin (↑k * Real.pi * x)

/-- Uniform bound: |eₖ(x)| ≤ √2 for all k and x -/
lemma dirichletBasis_bound (k : ℕ+) (x : ℝ) :
    |dirichletBasis k x| ≤ Real.sqrt 2 := by
  unfold dirichletBasis
  rw [abs_mul]
  have h_sin : |Real.sin (↑k * Real.pi * x)| ≤ 1 := Real.abs_sin_le_one _
  have h_sqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [abs_of_nonneg h_sqrt]
  exact mul_le_of_le_one_right h_sqrt h_sin

/-! ## Embedding Constant C∞² -/

/-- The Sobolev embedding constant (squared): C∞² = ∑_{k=1}^∞ 2/(1+(kπ)²) -/
def C_infty_sq : ℝ :=
  ∑' k : ℕ+, 2 / (1 + (↑k * Real.pi)^2)

/-- Summability of the embedding constant series -/
lemma C_infty_sq_summable :
    Summable (fun k : ℕ+ => 2 / (1 + (↑k * Real.pi)^2)) := by
  -- Step 1: Get summability for ℕ via p-series
  have nat_summable : Summable (fun n : ℕ => (1 : ℝ) / (n + 1) ^ 2) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    rw [← summable_nat_add_iff 1] at h
    convert h using 1
    funext n
    norm_cast

  -- Step 2: Convert to ℕ+ using embedding
  have pnat_one_sq : Summable (fun k : ℕ+ => (1 : ℝ) / (k : ℝ) ^ 2) := by
    let f_nat : ℕ → ℝ := fun n => if n = 0 then 0 else (1 : ℝ) / n ^ 2
    let emb : ℕ+ → ℕ := fun k => k.val
    have hf : Summable f_nat := by
      have h1 := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
      convert h1 using 1
      funext n
      by_cases hn : n = 0
      · simp [f_nat, hn]
      · simp [f_nat, hn]
    have emb_inj : Function.Injective emb := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ hab
      simp [emb] at hab
      exact Subtype.ext hab
    have h_vanish : ∀ n, n ∉ Set.range emb → f_nat n = 0 := by
      intro n hn
      simp [Set.mem_range, emb] at hn
      push_neg at hn
      simp [f_nat]
      by_cases h0 : n = 0
      · simp [h0]
      · exfalso
        have : ∃ (k : ℕ+), k.val = n := by
          use ⟨n, Nat.pos_of_ne_zero h0⟩
          rfl
        obtain ⟨k, hk⟩ := this
        exact hn k hk
    have key_equiv : (fun k : ℕ+ => (1 : ℝ) / (k : ℝ) ^ 2) = f_nat ∘ emb := by
      funext k
      simp [emb, f_nat, Function.comp, k.pos.ne']
    rw [key_equiv, Function.Injective.summable_iff emb_inj h_vanish]
    exact hf

  -- Step 3: Scale by 2
  have pnat_two_sq : Summable (fun k : ℕ+ => (2 : ℝ) / (k : ℝ) ^ 2) := by
    have := Summable.mul_left (2 : ℝ) pnat_one_sq
    convert this using 1
    funext k
    ring

  -- Step 4: Comparison test
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) pnat_two_sq
  · apply div_nonneg <;> [norm_num; positivity]
  · have key : (k : ℝ)^2 < 1 + ((k : ℝ) * Real.pi)^2 := by
      have h_pi2 : 1 < Real.pi^2 := by
        have h_pi := Real.pi_gt_three
        calc (1 : ℝ) < 9 := by norm_num
          _ = 3 ^ 2 := by norm_num
          _ < Real.pi ^ 2 := sq_lt_sq' (by linarith) h_pi
      by_cases hk : (k : ℝ) = 0
      · simp [hk]
      · have hpos : 0 < (k : ℝ)^2 := sq_pos_of_pos (by positivity : 0 < (k : ℝ))
        have step1 : (k : ℝ)^2 < (k : ℝ)^2 * Real.pi^2 := by
          calc (k : ℝ)^2 = (k : ℝ)^2 * 1 := by ring
            _ < (k : ℝ)^2 * Real.pi^2 := mul_lt_mul_of_pos_left h_pi2 hpos
        calc (k : ℝ)^2 < (k : ℝ)^2 * Real.pi^2 := step1
          _ = ((k : ℝ) * Real.pi)^2 := by ring
          _ = 0 + ((k : ℝ) * Real.pi)^2 := by ring
          _ < 1 + ((k : ℝ) * Real.pi)^2 := by linarith
    have h_pos : 0 < (k : ℝ)^2 := sq_pos_of_pos (by positivity : 0 < (k : ℝ))
    have h_pos' : 0 < 1 + (↑k * Real.pi)^2 := by positivity
    have : (k : ℝ)^2 ≤ 1 + ((k : ℝ) * Real.pi)^2 := le_of_lt key
    gcongr

/-- The embedding constant is positive -/
lemma C_infty_sq_pos : 0 < C_infty_sq := by
  unfold C_infty_sq
  have hpos_k : ∀ k : ℕ+, 0 ≤ 2 / (1 + (↑k * Real.pi)^2) := fun k => by
    apply div_nonneg <;> [norm_num; positivity]
  have witness : 0 < 2 / (1 + (↑(1 : ℕ+) * Real.pi)^2) := by
    apply div_pos
    · norm_num
    · positivity
  exact Summable.tsum_pos C_infty_sq_summable hpos_k 1 witness

/-! ## Connection to H¹ Weights -/

/-- For dimension 1, the h1Weight simplifies -/
lemma h1Weight_one_dim (k : ℕ+) :
    h1Weight (fun (_ : Fin spatialDim) => (k : ℤ)) = 1 + 4 * Real.pi^2 * (k : ℝ)^2 := by
  unfold h1Weight ℓ2ZD.normSq spatialDim
  simp only [Fin.sum_univ_one, pow_two]
  norm_cast

/-- Basis functions have bounded weighted squares -/
lemma basis_weighted_summable (x : Icc (0:ℝ) 1) :
    Summable (fun k : ℕ+ =>
      (dirichletBasis k x.val)^2 / h1Weight (fun _ : Fin spatialDim => (k : ℤ))) := by
  have h_nonneg : ∀ k, 0 ≤ (dirichletBasis k x.val)^2 / h1Weight (fun _ : Fin spatialDim => (k : ℤ)) := by
    intro k
    apply div_nonneg
    · exact sq_nonneg _
    · have : 0 < h1Weight (fun _ : Fin spatialDim => (k : ℤ)) := by
        rw [h1Weight_one_dim]
        positivity
      linarith
  refine Summable.of_nonneg_of_le h_nonneg (fun k => ?_) C_infty_sq_summable
  -- Bound: |e_k(x)|²/h1Weight(k) ≤ 2/(1+(kπ)²)
  have h_basis : (dirichletBasis k x.val)^2 ≤ 2 := by
    have h1 := dirichletBasis_bound k x.val
    have h2 : |dirichletBasis k x.val|^2 ≤ (Real.sqrt 2)^2 := by
      exact sq_le_sq' (by linarith [abs_nonneg (dirichletBasis k x.val)]) h1
    rw [sq_abs, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at h2
    exact h2
  have h_weight : h1Weight (fun _ : Fin spatialDim => (k : ℤ)) =
      1 + 4 * Real.pi^2 * (k : ℝ)^2 := h1Weight_one_dim k
  rw [h_weight]
  -- Show: (e_k)²/(1+4π²k²) ≤ 2/(1+(kπ)²)
  -- Using h_basis: (e_k)² ≤ 2
  -- Need: 2/(1+4π²k²) ≤ 2/(1+(kπ)²)
  -- Equivalent: 1+(kπ)² ≤ 1+4π²k²
  have h_denom : 1 + (↑k * Real.pi)^2 ≤ 1 + 4 * Real.pi^2 * (k : ℝ)^2 := by
    have h_expand1 : (↑k * Real.pi)^2 = (k : ℝ)^2 * Real.pi^2 := by ring
    have h_expand2 : 4 * Real.pi^2 * (k : ℝ)^2 = (k : ℝ)^2 * (4 * Real.pi^2) := by ring
    rw [h_expand1, h_expand2]
    have : Real.pi^2 ≤ 4 * Real.pi^2 := by
      have : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
      linarith
    nlinarith [sq_nonneg (k : ℝ)]
  -- Combine: (e_k)²/(1+4π²k²) ≤ 2/(1+4π²k²) ≤ 2/(1+(kπ)²)
  have h_step1 : (dirichletBasis k x.val)^2 / (1 + 4 * Real.pi^2 * (k : ℝ)^2) ≤
      2 / (1 + 4 * Real.pi^2 * (k : ℝ)^2) := by
    gcongr
  have h_step2 : 2 / (1 + 4 * Real.pi^2 * (k : ℝ)^2) ≤
      2 / (1 + (↑k * Real.pi)^2) := by
    gcongr
  linarith

/-- Uniform bound on weighted basis sums -/
lemma basis_weighted_bound (x : Icc (0:ℝ) 1) :
    ∑' k : ℕ+, (dirichletBasis k x.val)^2 / h1Weight (fun _ : Fin spatialDim => (k : ℤ))
      ≤ C_infty_sq := by
  unfold C_infty_sq
  refine (basis_weighted_summable x).tsum_le_tsum (fun k => ?_) C_infty_sq_summable
  -- Same inequality as in basis_weighted_summable
  have h_basis : (dirichletBasis k x.val)^2 ≤ 2 := by
    have h1 := dirichletBasis_bound k x.val
    have h2 : |dirichletBasis k x.val|^2 ≤ (Real.sqrt 2)^2 := by
      exact sq_le_sq' (by linarith [abs_nonneg (dirichletBasis k x.val)]) h1
    rw [sq_abs, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at h2
    exact h2
  have h_weight : h1Weight (fun _ : Fin spatialDim => (k : ℤ)) =
      1 + 4 * Real.pi^2 * (k : ℝ)^2 := h1Weight_one_dim k
  rw [h_weight]
  have h_denom : 1 + (↑k * Real.pi)^2 ≤ 1 + 4 * Real.pi^2 * (k : ℝ)^2 := by
    have h_expand1 : (↑k * Real.pi)^2 = (k : ℝ)^2 * Real.pi^2 := by ring
    have h_expand2 : 4 * Real.pi^2 * (k : ℝ)^2 = (k : ℝ)^2 * (4 * Real.pi^2) := by ring
    rw [h_expand1, h_expand2]
    have : Real.pi^2 ≤ 4 * Real.pi^2 := by
      have : 0 < Real.pi^2 := sq_pos_of_pos Real.pi_pos
      linarith
    nlinarith [sq_nonneg (k : ℝ)]
  have h_step1 : (dirichletBasis k x.val)^2 / (1 + 4 * Real.pi^2 * (k : ℝ)^2) ≤
      2 / (1 + 4 * Real.pi^2 * (k : ℝ)^2) := by
    gcongr
  have h_step2 : 2 / (1 + 4 * Real.pi^2 * (k : ℝ)^2) ≤
      2 / (1 + (↑k * Real.pi)^2) := by
    gcongr
  linarith

/-- Weighted Cauchy-Schwarz inequality for infinite sums.

    For nonnegative weights w and square-summable sequences:
      ∑' k, |a k * b k| ≤ √(∑' k, w k * a k²) · √(∑' k, b k² / w k)

    Strategy: Prove for each finite partial sum using finite CS,
    then take limit via Summable.tsum_le_of_sum_le.
-/
lemma weighted_cs_tsum
  (w : ℕ+ → ℝ) (a b : ℕ+ → ℝ)
  (hw_pos : ∀ k, 0 < w k)
  (ha : Summable (fun k => w k * a k ^ 2))
  (hb : Summable (fun k => (b k ^ 2) / w k)) :
  Summable (fun k => |a k * b k|) ∧
  (∑' k, |a k * b k|)
    ≤ Real.sqrt (∑' k, w k * a k ^ 2)
      * Real.sqrt (∑' k, (b k ^ 2) / w k) := by
  -- Define the tsums for clarity
  set Aw := ∑' k, w k * a k ^ 2 with hAw_def
  set Bw := ∑' k, (b k ^ 2) / w k with hBw_def

  -- STEP 1: Finite partial sum inequality
  have hF : ∀ (s : Finset ℕ+), (s.sum fun k => |a k * b k|) ≤ Real.sqrt Aw * Real.sqrt Bw := by
    intro s
    -- Bound partial tsums
    have h_partial_a : (s.sum fun k => w k * a k ^ 2) ≤ Aw := by
      apply ha.sum_le_tsum s
      intro k _
      apply mul_nonneg (le_of_lt (hw_pos k)) (sq_nonneg _)

    have h_partial_b : (s.sum fun k => (b k ^ 2) / w k) ≤ Bw := by
      apply hb.sum_le_tsum s
      intro k _
      apply div_nonneg (sq_nonneg _) (le_of_lt (hw_pos k))

    -- Rewrite using weighted variables
    have h_rewrite : ∀ k ∈ s,
        |a k * b k| = (Real.sqrt (w k) * |a k|) * (|b k| / Real.sqrt (w k)) := by
      intro k hk
      have hw_k : 0 < w k := hw_pos k
      rw [abs_mul]
      have hw_sqrt : 0 < Real.sqrt (w k) := Real.sqrt_pos.mpr hw_k
      calc |a k| * |b k|
          = |a k| * (|b k| * Real.sqrt (w k) / Real.sqrt (w k)) := by
            rw [mul_div_cancel_right₀ _ (ne_of_gt hw_sqrt)]
        _ = Real.sqrt (w k) * |a k| * (|b k| / Real.sqrt (w k)) := by
            ring

    -- Apply finite Cauchy-Schwarz
    have h_step1 : (s.sum fun k => |a k * b k|)
        = (s.sum fun k => (Real.sqrt (w k) * |a k|) * (|b k| / Real.sqrt (w k))) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      exact h_rewrite k hk

    have h_step2 : (s.sum fun k => (Real.sqrt (w k) * |a k|) * (|b k| / Real.sqrt (w k)))
        ≤ Real.sqrt (s.sum fun k => (Real.sqrt (w k) * |a k|)^2)
          * Real.sqrt (s.sum fun k => (|b k| / Real.sqrt (w k))^2) := by
      -- Use standard finite CS: (∑ xᵢyᵢ)² ≤ (∑ xᵢ²)(∑ yᵢ²)
      have h_cs := Finset.sum_mul_sq_le_sq_mul_sq s
        (fun k => Real.sqrt (w k) * |a k|)
        (fun k => |b k| / Real.sqrt (w k))
      have h_sum_nonneg : 0 ≤ (s.sum fun k => (Real.sqrt (w k) * |a k|) * (|b k| / Real.sqrt (w k))) :=
        Finset.sum_nonneg (fun k _ => by positivity)
      have h_lhs : Real.sqrt ((s.sum fun k => (Real.sqrt (w k) * |a k|) * (|b k| / Real.sqrt (w k)))^2)
          = (s.sum fun k => (Real.sqrt (w k) * |a k|) * (|b k| / Real.sqrt (w k))) :=
        Real.sqrt_sq h_sum_nonneg
      have h_sum1_nonneg : 0 ≤ (s.sum fun k => (Real.sqrt (w k) * |a k|)^2) :=
        Finset.sum_nonneg (fun k _ => sq_nonneg _)
      have h_rhs : Real.sqrt ((s.sum fun k => (Real.sqrt (w k) * |a k|)^2)
              * (s.sum fun k => (|b k| / Real.sqrt (w k))^2))
          = Real.sqrt (s.sum fun k => (Real.sqrt (w k) * |a k|)^2)
            * Real.sqrt (s.sum fun k => (|b k| / Real.sqrt (w k))^2) := by
        rw [Real.sqrt_mul h_sum1_nonneg]
      rw [← h_lhs, ← h_rhs]
      exact Real.sqrt_le_sqrt h_cs

    have h_step3 : Real.sqrt (s.sum fun k => (Real.sqrt (w k) * |a k|)^2)
          * Real.sqrt (s.sum fun k => (|b k| / Real.sqrt (w k))^2)
        = Real.sqrt (s.sum fun k => w k * a k ^ 2)
          * Real.sqrt (s.sum fun k => (b k ^ 2) / w k) := by
      congr 1
      · congr 1
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [mul_pow, Real.sq_sqrt (le_of_lt (hw_pos k)), sq_abs]
      · congr 1
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [div_pow, Real.sq_sqrt (le_of_lt (hw_pos k)), sq_abs]

    have h_step4 : Real.sqrt (s.sum fun k => w k * a k ^ 2)
          * Real.sqrt (s.sum fun k => (b k ^ 2) / w k)
        ≤ Real.sqrt Aw * Real.sqrt Bw := by
      gcongr

    calc (s.sum fun k => |a k * b k|)
        = (s.sum fun k => |a k * b k|) := rfl
      _ = (s.sum fun k => (Real.sqrt (w k) * |a k|) * (|b k| / Real.sqrt (w k))) := h_step1
      _ ≤ Real.sqrt (s.sum fun k => (Real.sqrt (w k) * |a k|)^2)
          * Real.sqrt (s.sum fun k => (|b k| / Real.sqrt (w k))^2) := h_step2
      _ = Real.sqrt (s.sum fun k => w k * a k ^ 2)
          * Real.sqrt (s.sum fun k => (b k ^ 2) / w k) := h_step3
      _ ≤ Real.sqrt Aw * Real.sqrt Bw := h_step4

  -- STEP 2: Summability from bounded partial sums
  have h_summable : Summable (fun k => |a k * b k|) := by
    apply Summable.of_nonneg_of_le
    · intro k
      exact abs_nonneg _
    · intro k
      -- Use: |ab| ≤ (wa² + b²/w)/2
      have h_weight_pos : 0 < w k := hw_pos k
      have h_amgm : |a k * b k| ≤ (w k * a k^2 + (b k^2) / w k) / 2 := by
        rw [abs_mul]
        have h1 : 0 ≤ (Real.sqrt (w k) * |a k| - |b k| / Real.sqrt (w k))^2 := sq_nonneg _
        have h2 : (Real.sqrt (w k) * |a k| - |b k| / Real.sqrt (w k))^2
            = w k * |a k|^2 - 2 * (|a k| * |b k|) + (|b k|^2) / w k := by
          rw [sub_sq]
          have hw_sqrt_sq : Real.sqrt (w k) ^ 2 = w k := Real.sq_sqrt (le_of_lt h_weight_pos)
          have hw_sqrt_ne : Real.sqrt (w k) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr h_weight_pos)
          simp only [mul_pow, div_pow, hw_sqrt_sq]
          field_simp [hw_sqrt_ne]
        calc |a k| * |b k|
            = (w k * |a k|^2 - (Real.sqrt (w k) * |a k| - |b k| / Real.sqrt (w k))^2
                + (|b k|^2) / w k) / 2 := by
              rw [h2]; field_simp; ring
          _ ≤ (w k * |a k|^2 + (|b k|^2) / w k) / 2 := by
              have : 0 ≤ (Real.sqrt (w k) * |a k| - |b k| / Real.sqrt (w k))^2 := h1
              linarith
          _ = (w k * a k^2 + (b k^2) / w k) / 2 := by
              rw [sq_abs, sq_abs]
      exact h_amgm
    · -- The sum (wa² + b²/w)/2 is summable
      have h_sum1 : Summable (fun k => w k * a k ^ 2 / 2) := Summable.div_const ha 2
      have h_sum2 : Summable (fun k => (b k ^ 2) / w k / 2) := Summable.div_const hb 2
      convert Summable.add h_sum1 h_sum2 using 1
      ext k
      ring

  -- STEP 3: Apply tsum_le_of_sum_le
  have htsum : ∑' k, |a k * b k| ≤ Real.sqrt Aw * Real.sqrt Bw := by
    apply h_summable.tsum_le_of_sum_le
    exact hF

  exact ⟨h_summable, htsum⟩

/-! ## Part 2: Evaluation Function -/

/-- Evaluate H¹ sequence at a point via Fourier series -/
def eval (u : H1Seq) (x : Icc (0:ℝ) 1) : ℝ :=
  ∑' k : ℕ+, (u.coeff (fun _ => (k : ℤ))).re * dirichletBasis k x.val

/-- Helper: ℕ+ summability from Lattice summability -/
lemma summable_pnat_of_lattice (u : H1Seq) :
    Summable (fun k : ℕ+ => h1Weight (fun _ : Fin spatialDim => (k : ℤ)) * ‖u.coeff (fun _ => (k : ℤ))‖^2) := by
  -- u.summable_h1_coeff is for all lattice points
  -- The ℕ+ sum is a subseries (restriction) of the full Lattice sum
  have h_full := u.summable_h1_coeff

  -- Define the embedding ℕ+ → Lattice
  let embed : ℕ+ → Lattice spatialDim := fun k => fun _ => (k : ℤ)

  -- Key: embed is injective
  have h_inj : Function.Injective embed := by
    intro k1 k2 heq
    have : (k1 : ℤ) = (k2 : ℤ) := congr_fun heq 0
    have : (k1 : ℕ) = (k2 : ℕ) := Nat.cast_injective this
    exact Subtype.ext this

  -- Use the injective function summability theorem
  exact h_full.comp_injective h_inj

/-- Pointwise summability -/
lemma eval_summable (u : H1Seq) (x : Icc (0:ℝ) 1) :
    Summable (fun k : ℕ+ => |(u.coeff (fun _ => (k : ℤ))).re * dirichletBasis k x.val|) := by
  -- Strategy: Use AM-GM inequality: |aₖ·bₖ| ≤ (w|aₖ|² + |bₖ|²/w)/2
  have h_sum1 : Summable (fun k : ℕ+ =>
      h1Weight (fun _ : Fin spatialDim => (k : ℤ)) * ‖u.coeff (fun _ => (k : ℤ))‖^2 / 2) := by
    apply Summable.div_const
    exact summable_pnat_of_lattice u
  have h_sum2 : Summable (fun k : ℕ+ =>
      (dirichletBasis k x.val)^2 / h1Weight (fun _ : Fin spatialDim => (k : ℤ)) / 2) := by
    apply Summable.div_const
    exact basis_weighted_summable x
  have h_sum : Summable (fun k : ℕ+ =>
      h1Weight (fun _ : Fin spatialDim => (k : ℤ)) * ‖u.coeff (fun _ => (k : ℤ))‖^2 / 2
      + (dirichletBasis k x.val)^2 / h1Weight (fun _ : Fin spatialDim => (k : ℤ)) / 2) :=
    Summable.add h_sum1 h_sum2

  apply Summable.of_nonneg_of_le
  · intro k; exact abs_nonneg _
  · intro k
    -- AM-GM: |ab| ≤ (wa² + b²/w)/2
    have h_weight_pos : 0 < h1Weight (fun _ : Fin spatialDim => (k : ℤ)) := by
      rw [h1Weight_one_dim]; positivity
    set w := h1Weight (fun _ : Fin spatialDim => (k : ℤ))
    set a := |(u.coeff (fun _ => (k : ℤ))).re|
    set b := |dirichletBasis k x.val|
    calc |(u.coeff (fun _ => (k : ℤ))).re * dirichletBasis k x.val|
      _ = a * b := abs_mul _ _
      _ ≤ (w * a^2 + b^2 / w) / 2 := by
        have key : 2 * (a * b) ≤ w * a^2 + b^2 / w := by
          have h1 : 0 ≤ (Real.sqrt w * a - b / Real.sqrt w)^2 := sq_nonneg _
          have sqrt_w_sq : (Real.sqrt w)^2 = w := Real.sq_sqrt (le_of_lt h_weight_pos)
          have h2 : (Real.sqrt w * a - b / Real.sqrt w)^2 = w * a^2 - 2 * (a * b) + b^2 / w := by
            have eq1 : (Real.sqrt w * a - b / Real.sqrt w)^2 =
              (Real.sqrt w)^2 * a^2 - 2 * Real.sqrt w * a * (b / Real.sqrt w) + (b / Real.sqrt w)^2 := by ring
            rw [eq1, sqrt_w_sq]
            have eq2 : 2 * Real.sqrt w * a * (b / Real.sqrt w) = 2 * a * b := by
              field_simp [ne_of_gt h_weight_pos]
            rw [eq2]
            have eq3 : (b / Real.sqrt w)^2 = b^2 / w := by
              rw [div_pow, sqrt_w_sq]
            rw [eq3]
            ring
          linarith
        linarith
      _ ≤ (w * ‖u.coeff (fun _ => (k : ℤ))‖^2 + (dirichletBasis k x.val)^2 / w) / 2 := by
        have ha2_le : a^2 ≤ ‖u.coeff (fun _ => (k : ℤ))‖^2 := by
          unfold a
          show |(u.coeff (fun _ => (k : ℤ))).re|^2 ≤ ‖u.coeff (fun _ => (k : ℤ))‖^2
          have h_norm : ‖u.coeff (fun _ => (k : ℤ))‖^2 =
            (u.coeff (fun _ => (k : ℤ))).re^2 + (u.coeff (fun _ => (k : ℤ))).im^2 := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
            ring
          rw [h_norm]
          have h_sq : |(u.coeff (fun _ => (k : ℤ))).re|^2 = (u.coeff (fun _ => (k : ℤ))).re^2 := sq_abs _
          rw [h_sq]
          nlinarith [sq_nonneg (u.coeff (fun _ => (k : ℤ))).im]
        have hb2_le : b^2 ≤ (dirichletBasis k x.val)^2 := by
          unfold b
          show |dirichletBasis k x.val|^2 ≤ (dirichletBasis k x.val)^2
          simp [sq_abs]
        have : (w * a^2 + b^2 / w) / 2 ≤ (w * ‖u.coeff (fun _ => (k : ℤ))‖^2 + (dirichletBasis k x.val)^2 / w) / 2 := by
          have h1 : w * a^2 ≤ w * ‖u.coeff (fun _ => (k : ℤ))‖^2 := mul_le_mul_of_nonneg_left ha2_le (le_of_lt h_weight_pos)
          have h2 : b^2 / w ≤ (dirichletBasis k x.val)^2 / w := by
            gcongr
          linarith
        exact this
      _ = w * ‖u.coeff (fun _ => (k : ℤ))‖^2 / 2 + (dirichletBasis k x.val)^2 / w / 2 := by
        ring
  · exact h_sum

/-- Pointwise bound in terms of H¹ norm - uses weighted_cs_tsum -/
lemma eval_pointwise_bound (u : H1Seq) (x : Icc (0:ℝ) 1) :
    |eval u x| ≤ Real.sqrt C_infty_sq *
      Real.sqrt (∑' k : ℕ+, h1Weight (fun (_ : Fin spatialDim) => (k:ℤ)) * ‖u.coeff (fun (_ : Fin spatialDim) => (k:ℤ))‖^2) := by
  unfold eval
  -- Set up for weighted CS: a_k = |(u.coeff k).re|, b_k = |dirichletBasis k x|, w_k = h1Weight k
  let w : ℕ+ → ℝ := fun k => h1Weight (fun _ : Fin spatialDim => (k : ℤ))
  let a : ℕ+ → ℝ := fun k => |(u.coeff (fun _ => (k : ℤ))).re|
  let b : ℕ+ → ℝ := fun k => |dirichletBasis k x.val|

  -- Verify hypotheses for weighted_cs_tsum
  have hw_pos : ∀ k, 0 < w k := by
    intro k; unfold w; rw [h1Weight_one_dim]; positivity

  have ha : Summable (fun k => w k * a k ^ 2) := by
    apply Summable.of_nonneg_of_le
    · intro k; apply mul_nonneg; unfold w; rw [h1Weight_one_dim]; positivity; exact sq_nonneg _
    · intro k
      show w k * a k ^ 2 ≤ h1Weight (fun _ : Fin spatialDim => (k : ℤ)) * ‖u.coeff (fun _ => (k : ℤ))‖ ^ 2
      unfold w a
      apply mul_le_mul_of_nonneg_left
      ·  gcongr; exact Complex.abs_re_le_norm (u.coeff (fun _ => (k : ℤ)))
      · rw [h1Weight_one_dim]; positivity
    · exact summable_pnat_of_lattice u

  have hb : Summable (fun k => (b k ^ 2) / w k) := by
    convert basis_weighted_summable x using 1
    funext k; unfold b w; rw [sq_abs]

  -- Apply weighted_cs_tsum
  have h_cs := weighted_cs_tsum w a b hw_pos ha hb

  -- Bound |∑ uₖ·eₖ| by ∑|uₖ·eₖ|
  calc |∑' k, (u.coeff _).re * dirichletBasis k x.val|
      ≤ ∑' k, |(u.coeff _).re * dirichletBasis k x.val| := by
        -- Triangle inequality for tsum
        have h_summable : Summable (fun (k : ℕ+) => (u.coeff (fun _ => (k : ℤ))).re * dirichletBasis k x.val) := by
          apply Summable.of_norm
          convert h_cs.1 using 1; funext (k : ℕ+)
          simp only [Real.norm_eq_abs, abs_mul]; unfold a b
          simp only [abs_abs]
        have h_norm : ‖∑' (k : ℕ+), (u.coeff (fun _ => (k : ℤ))).re * dirichletBasis k x.val‖ ≤
                      ∑' (k : ℕ+), ‖(u.coeff (fun _ => (k : ℤ))).re * dirichletBasis k x.val‖ :=
          norm_tsum_le_tsum_norm h_summable.norm
        simp only [Real.norm_eq_abs] at h_norm ⊢
        exact h_norm
    _ = ∑' k, |a k * b k| := by
        congr 1; funext k; unfold a b; simp only [abs_mul, abs_abs]
    _ ≤ Real.sqrt (∑' k, w k * a k ^ 2) * Real.sqrt (∑' k, (b k ^ 2) / w k) := h_cs.2
    _ ≤ Real.sqrt (∑' k, w k * ‖u.coeff _‖ ^ 2) * Real.sqrt C_infty_sq := by
        have h_tsum1 : ∑' k, w k * a k ^ 2 ≤ ∑' k, w k * ‖u.coeff (fun _ => (k : ℤ))‖ ^ 2 := by
          refine ha.tsum_le_tsum ?_ (summable_pnat_of_lattice u)
          intro k
          unfold w a
          apply mul_le_mul_of_nonneg_left
          · gcongr; exact Complex.abs_re_le_norm (u.coeff (fun _ => (k : ℤ)))
          · rw [h1Weight_one_dim]; positivity
        have h_tsum2 : ∑' k, (b k ^ 2) / w k ≤ C_infty_sq := by
          have h_le : ∑' k, (b k ^ 2) / w k ≤ ∑' k, (dirichletBasis k x.val) ^ 2 / h1Weight (fun _ : Fin spatialDim => (k : ℤ)) := by
            refine hb.tsum_le_tsum ?_ (basis_weighted_summable x)
            intro k; unfold b w; rw [sq_abs]
          exact le_trans h_le (basis_weighted_bound x)
        gcongr
    _ = Real.sqrt C_infty_sq * Real.sqrt (∑' k, w k * ‖u.coeff _‖ ^ 2) := mul_comm _ _

/-! ## L∞ Seminorm -/

/-- The L∞ seminorm: ‖u‖_∞ = sup_{x∈[0,1]} |u(x)| -/
def linfty_seminorm (u : H1Seq) : ℝ :=
  ⨆ x : Icc (0:ℝ) 1, |eval u x|

/-- L∞ seminorm is finite -/
lemma linfty_seminorm_finite (u : H1Seq) :
    ∃ C, ∀ x : Icc (0:ℝ) 1, |eval u x| ≤ C := by
  use Real.sqrt C_infty_sq * Real.sqrt (∑' k : ℕ+, h1Weight (fun (_ : Fin spatialDim) => (k:ℤ)) * ‖u.coeff (fun (_ : Fin spatialDim) => (k:ℤ))‖^2)
  exact eval_pointwise_bound u

/-! ## Main Theorem: Sobolev Embedding -/

/-- H¹ norm definition -/
def H1_norm (u : H1Seq) : ℝ :=
  Real.sqrt (∑' k : ℕ+, h1Weight (fun (_ : Fin spatialDim) => (k : ℤ)) * ‖u.coeff (fun _ => (k : ℤ))‖^2)

/-- THE MAIN THEOREM: Sobolev Embedding H¹₀(0,1) ↪ L∞(0,1) -/
theorem sobolev_embedding_H1_Linfty (u : H1Seq) :
    linfty_seminorm u ≤ Real.sqrt C_infty_sq * H1_norm u := by
  unfold linfty_seminorm H1_norm
  -- Use: ⨆ x, f x ≤ b ↔ ∀ x, f x ≤ b
  apply ciSup_le
  intro x
  exact eval_pointwise_bound u x

/-- Variant with explicit R² bound -/
theorem sobolev_embedding_explicit (u : H1Seq) (R : ℝ) (hR : 0 ≤ R)
    (h_bound : ∑' k : ℕ+, h1Weight (fun (_ : Fin spatialDim) => (k:ℤ)) * ‖u.coeff (fun (_ : Fin spatialDim) => (k:ℤ))‖^2 ≤ R^2) :
    linfty_seminorm u ≤ Real.sqrt C_infty_sq * R := by
  have h_main := sobolev_embedding_H1_Linfty u
  unfold H1_norm at h_main
  calc linfty_seminorm u
      ≤ Real.sqrt C_infty_sq * Real.sqrt (∑' k, h1Weight _ * ‖u.coeff _‖^2) := h_main
    _ ≤ Real.sqrt C_infty_sq * Real.sqrt (R^2) := by
        have : ∑' k, h1Weight _ * ‖u.coeff _‖^2 ≤ R^2 := h_bound
        gcongr
    _ = Real.sqrt C_infty_sq * R := by
        rw [Real.sqrt_sq hR]

/-! ## Connection to Cubic Operator -/

/-- Sobolev constant -/
def sobolev_constant : ℝ := Real.sqrt C_infty_sq

lemma sobolev_constant_pos : 0 < sobolev_constant := by
  unfold sobolev_constant
  exact Real.sqrt_pos.mpr C_infty_sq_pos

/-- Application to H¹ ball -/
lemma H1Ball_to_LinftyBound (u : H1Seq) (R : ℝ)
    (h_H1 : InH1Ball R u.toSeqD) :
    linfty_seminorm u ≤ sobolev_constant * |R| := by
  unfold sobolev_constant
  -- InH1Ball gives: ∀ F, ∑_{k∈F} h1Weight·‖uₖ‖² ≤ R²
  -- Need to show: ∑' k, h1Weight·‖uₖ‖² ≤ R²
  have h_tsum_bound : ∑' k : ℕ+, h1Weight (fun _ : Fin spatialDim => (k : ℤ)) * ‖u.coeff (fun _ => (k : ℤ))‖^2 ≤ R^2 := by
    -- The tsum is the supremum of all finite partial sums
    apply (summable_pnat_of_lattice u).tsum_le_of_sum_le
    intro F
    -- Need to convert F : Finset ℕ+ to Finset (Lattice spatialDim)
    let F_lattice : Finset (Lattice spatialDim) := F.image (fun k : ℕ+ => fun _ : Fin spatialDim => (k : ℤ))
    have h_bound_lattice := h_H1 F_lattice
    -- Show the two sums are equal
    have h_eq : Finset.sum F (fun k => h1Weight (fun _ : Fin spatialDim => (k : ℤ)) * ‖u.coeff (fun _ => (k : ℤ))‖^2)
        = Finset.sum F_lattice (fun k => h1Weight k * ‖u.toSeqD.a k‖^2) := by
      unfold F_lattice
      rw [Finset.sum_image]
      · rfl
      · -- Injective: k₁ ≠ k₂ → (fun _ => k₁) ≠ (fun _ => k₂)
        intro k1 _ k2 _ heq
        have h_eval : (k1 : ℤ) = (k2 : ℤ) := congr_fun heq (0 : Fin spatialDim)
        -- k₁ and k₂ are equal as ℤ, so equal as ℕ+
        have : (k1 : ℕ) = (k2 : ℕ) := Nat.cast_injective h_eval
        exact PNat.coe_injective this
    rw [h_eq]
    exact h_bound_lattice
  -- Apply sobolev_embedding_explicit
  by_cases hR : 0 ≤ R
  · calc linfty_seminorm u
        ≤ Real.sqrt C_infty_sq * R := sobolev_embedding_explicit u R hR h_tsum_bound
      _ = sobolev_constant * R := rfl
      _ = sobolev_constant * |R| := by rw [abs_of_nonneg hR]
  · -- R < 0 case: |R| = -R
    push_neg at hR
    have h_abs : |R| = -R := abs_of_neg hR
    have h_sq_pos : 0 ≤ R^2 := sq_nonneg R
    have h_tsum_nonneg : 0 ≤ ∑' k : ℕ+, h1Weight (fun _ : Fin spatialDim => (k : ℤ)) * ‖u.coeff (fun _ => (k : ℤ))‖^2 := by
      apply tsum_nonneg
      intro k
      apply mul_nonneg
      · have : 0 < h1Weight (fun _ : Fin spatialDim => (k : ℤ)) := by
          rw [h1Weight_one_dim]; positivity
        linarith
      · exact sq_nonneg _
    have h_neg_R_pos : 0 ≤ -R := le_of_lt (neg_pos.mpr hR)
    calc linfty_seminorm u
        ≤ Real.sqrt C_infty_sq * Real.sqrt (∑' k, h1Weight _ * ‖u.coeff _‖^2) := by
          have := sobolev_embedding_H1_Linfty u
          unfold H1_norm at this
          exact this
      _ ≤ Real.sqrt C_infty_sq * Real.sqrt (R^2) := by
          have : ∑' k, h1Weight _ * ‖u.coeff _‖^2 ≤ R^2 := h_tsum_bound
          gcongr
      _ = Real.sqrt C_infty_sq * |R| := by
          rw [Real.sqrt_sq_eq_abs]
      _ = sobolev_constant * |R| := rfl

end

end SemilinearHeat
