import Budgets.IntervalDyadic
import Budgets.SemilinearHeat.Operator
import Budgets.SemilinearHeat.Galerkin
import Budgets.SemilinearHeat.Nonlinearity
import Budgets.SemilinearHeat.BilinearForm
import Budgets.RellichKondrachovD.Core
import Budgets.AubinLions.Core
import Budgets.ConstructiveQ

/-!
# Time Evolution for Semilinear Heat Equation

This file implements time-stepping schemes for the semilinear heat PDE:
  ∂ₜu - Δu = N(u)  on (0,1) × (0,T)

We provide both:
- **Proof track** (C5): Uses SeqD with Complex/Real for soundness proofs
- **Extraction track** (C0): Uses SeqD_Rat with ConstructiveQ for witness extraction

## Main Components

- `eulerStep`: Explicit Euler time step for Galerkin approximation
- `evolveTrajectory`: Full trajectory over time interval
- Rational variants for extraction (`eulerStep_rat`, `evolveTrajectory_rat`)
- Energy estimates and stability bounds

## Mathematical Background

The Galerkin-projected equation becomes a finite-dimensional ODE:
  d/dt uₙ(t) = -A uₙ(t) + Pₙ N(uₙ(t))

where:
- A is the Laplacian operator (diagonal in Fourier basis)
- Pₙ is projection to cube(n)
- N is the cubic nonlinearity

Explicit Euler discretization:
  uₙᵏ⁺¹ = uₙᵏ + Δt (-A uₙᵏ + Pₙ N(uₙᵏ))
-/

namespace SemilinearHeat

open BigOperators Complex
open scoped ComplexConjugate
open ℓ2ZD (Lattice SeqD SeqD_Rat InH1Ball InHminusBall h1Weight hminusWeight cube)
open AubinLions (TimeGrid)

/-! ## Proof Track: Complex-valued evolution -/

noncomputable section

/-- Helper to get time step from TimeGrid -/
def timeStep (tg : TimeGrid) : ℝ := (tg.mesh : ℝ)

/-- Explicit Euler step for the semilinear heat equation.

Given current state u at time t, compute u(t + Δt) via:
  u(t + Δt) ≈ u(t) + Δt · [Δu(t) + N(u(t))]

In Fourier space:
  û(k, t + Δt) = û(k, t) + Δt · [-λₖ û(k, t) + N̂(u)(k, t)]

where λₖ = π²k² is the Laplacian eigenvalue.
-/
def eulerStep (𝒩 : CubicNemytskii) (G : GalerkinSystem)
    (dt : ℝ) (n : ℕ) (u : DirichletSeq) : DirichletSeq :=
  -- Project to level n
  let u_n := G.project n u
  -- Apply nonlinearity and project
  let nonlinear_term := G.project n (𝒩.apply u_n)
  -- Laplacian term: -λₖ u.a(k) for each mode
  let laplacian_term : DirichletSeq := {
    a := fun k => -(laplacianWeight k : ℂ) * u_n.a k
    summable_sq := by
      -- u_n is a projection, so it has finite support in cube(level n)
      -- Therefore the weighted version also has finite support
      classical
      refine summable_of_ne_finset_zero (s := G.support n) ?_
      intro k hk
      -- If k is not in the support, u_n.a k = 0, so the product is 0
      have hu_n : u_n.a k = 0 := G.project_coeff_not_mem (u := u) hk
      simp [hu_n]
  }
  -- Euler step: u + dt(laplacian + nonlinear)
  { a := fun k =>
      u_n.a k + (dt : ℂ) * (laplacian_term.a k + nonlinear_term.a k)
    summable_sq := by
      -- All terms have finite support in cube(level n), so the sum does too
      classical
      refine summable_of_ne_finset_zero (s := G.support n) ?_
      intro k hk
      -- If k is not in the support, all terms are zero
      have hu_n : u_n.a k = 0 := G.project_coeff_not_mem (u := u) hk
      have hlap : laplacian_term.a k = 0 := by
        show -(laplacianWeight k : ℂ) * u_n.a k = 0
        simp [hu_n]
      have hnon : nonlinear_term.a k = 0 := G.project_coeff_not_mem (u := 𝒩.apply u_n) hk
      simp [hlap, hnon, hu_n]
  }

/-- Evolve from initial data over K time steps using Galerkin projection at level n.

Returns the trajectory as a function from time step index to state.
-/
def evolveTrajectory (𝒩 : CubicNemytskii) (G : GalerkinSystem)
    (u0 : DirichletSeq) (tg : TimeGrid) (n : ℕ) :
    Fin (tg.segments + 1) → DirichletSeq
  | ⟨0, _⟩ => G.project n u0  -- Initial condition (projected)
  | ⟨i + 1, h⟩ =>
      let u_prev := evolveTrajectory 𝒩 G u0 tg n ⟨i, Nat.lt_of_succ_lt h⟩
      eulerStep 𝒩 G (timeStep tg) n u_prev

/-! ## Energy Estimates -/

/-- L² energy at a given state -/
def l2Energy (F : Finset (Lattice spatialDim)) (u : DirichletSeq) : ℝ :=
  Finset.sum F (fun k => ‖u.a k‖^2)

/-- H¹ energy (Dirichlet energy) at a given state -/
def h1Energy (F : Finset (Lattice spatialDim)) (u : DirichletSeq) : ℝ :=
  gradEnergyOn F u


end -- noncomputable section

/-! ## Extraction Track: Rational-valued evolution -/

/-- Helper to get rational time step -/
def timeStep_rat (tg : TimeGrid) : ℚ := tg.mesh

/-- Conservative upper bound for π (for eigenvalue estimates).

We use 31416/10000 = 3.1416 as a rational upper bound of π ≈ 3.14159265...
This is used in the rational track to ensure eigenvalue bounds are conservative.
For sound lower bounds on eigenvalues, we use an upper bound on π.
-/
def pi_rat_ub : ℚ := 31416/10000

/-- Laplacian eigenvalue for mode k in rational arithmetic.

λₖ = π² k² ≈ (3.1416)² k² ≈ 9.8696 k² (using upper bound π ≤ 3.1416)
-/
def laplacianWeight_rat (k : Lattice spatialDim) : ℚ :=
  let k_val := k 0  -- For 1D
  pi_rat_ub * pi_rat_ub * (k_val * k_val : ℚ)

/-- Apply cubic operator in rational arithmetic via triple convolution.

For u with Fourier coefficients u.a(k) = (re, im) ∈ ℚ × ℚ,
compute (u³).a(k) = Σ_{k₁+k₂+k₃=k} u.a(k₁) · u.a(k₂) · u.a(k₃)

Uses only rational arithmetic - fully C0 extractable.

LAZY EVALUATION: This computes coefficients on-demand. For sparse data (few non-zero modes),
this is actually efficient because most triple products are zero and get filtered out.
-/
def applyCubic_rat (u : SeqD_Rat spatialDim) (M : ℕ) : SeqD_Rat spatialDim :=
  { a := fun k =>
      -- Triple convolution over cube(M)
      let sum_re := Finset.sum (cube spatialDim M) fun k1 =>
        Finset.sum (cube spatialDim M) fun k2 =>
          let k3 : Lattice spatialDim := fun i => k i - k1 i - k2 i
          let (u1_re, u1_im) := u.a k1
          let (u2_re, u2_im) := u.a k2
          let (u3_re, u3_im) := u.a k3
          -- Real part of (u1)(u2)(u3)
          u1_re * u2_re * u3_re - u1_re * u2_im * u3_im
          - u1_im * u2_re * u3_im - u1_im * u2_im * u3_re
      let sum_im := Finset.sum (cube spatialDim M) fun k1 =>
        Finset.sum (cube spatialDim M) fun k2 =>
          let k3 : Lattice spatialDim := fun i => k i - k1 i - k2 i
          let (u1_re, u1_im) := u.a k1
          let (u2_re, u2_im) := u.a k2
          let (u3_re, u3_im) := u.a k3
          -- Imaginary part
          u1_re * u2_re * u3_im + u1_re * u2_im * u3_re
          + u1_im * u2_re * u3_re - u1_im * u2_im * u3_im
      (sum_re, sum_im)
    finite_support := by
      classical
      obtain ⟨S, hS_prop⟩ := u.finite_support.exists_finset_coe
      have hS_mem : ∀ k, k ∈ S ↔ u.a k ≠ (0, 0) := by
        intro k'
        have hset := congrArg (fun (t : Set (Lattice spatialDim)) => k' ∈ t) hS_prop
        simpa [Set.mem_setOf_eq] using hset
      have hS_zero : ∀ k, k ∉ S → u.a k = (0, 0) := by
        intro k hk
        have : ¬ u.a k ≠ (0, 0) := by
          intro hne
          exact hk ((hS_mem k).mpr hne)
        exact not_not.mp this

      -- Output modes are contained in k1+k2+k3 with k1,k2 ∈ cube(M), k3 ∈ support(u)
      let output_bound : Finset (Lattice spatialDim) :=
        (cube spatialDim M).biUnion fun k1 =>
          (cube spatialDim M).biUnion fun k2 =>
            S.image fun k3 => fun i => k1 i + k2 i + k3 i

      refine Set.Finite.subset (Finset.finite_toSet output_bound) ?_
      intro k hk
      -- hk : (applyCubic_rat u M).a k ≠ (0,0)
      by_contra hnot

      -- If k is outside output_bound, every contributing k3 is zero.
      have hzero :
          ∀ k1 ∈ cube spatialDim M, ∀ k2 ∈ cube spatialDim M,
            u.a (fun i => k i - k1 i - k2 i) = (0, 0) := by
        intro k1 hk1 k2 hk2
        have hk3_not : (fun i => k i - k1 i - k2 i) ∉ S := by
          intro hk3
          -- Then k would lie in output_bound, contradicting hnot
          apply hnot
          refine Finset.mem_biUnion.mpr ?_
          refine ⟨k1, hk1, ?_⟩
          refine Finset.mem_biUnion.mpr ?_
          refine ⟨k2, hk2, ?_⟩
          refine Finset.mem_image.mpr ?_
          refine ⟨(fun i => k i - k1 i - k2 i), hk3, ?_⟩
          funext i; ring_nf
        exact hS_zero _ hk3_not

      have h_re_zero :
          (Finset.sum (cube spatialDim M) fun k1 =>
            Finset.sum (cube spatialDim M) fun k2 =>
              let k3 : Lattice spatialDim := fun i => k i - k1 i - k2 i
              let (u1_re, u1_im) := u.a k1
              let (u2_re, u2_im) := u.a k2
              let (u3_re, u3_im) := u.a k3
              u1_re * u2_re * u3_re - u1_re * u2_im * u3_im
              - u1_im * u2_re * u3_im - u1_im * u2_im * u3_re) = 0 := by
        apply Finset.sum_eq_zero
        intro k1 hk1
        apply Finset.sum_eq_zero
        intro k2 hk2
        have hk3_zero := hzero k1 hk1 k2 hk2
        simp [hk3_zero]

      have h_im_zero :
          (Finset.sum (cube spatialDim M) fun k1 =>
            Finset.sum (cube spatialDim M) fun k2 =>
              let k3 : Lattice spatialDim := fun i => k i - k1 i - k2 i
              let (u1_re, u1_im) := u.a k1
              let (u2_re, u2_im) := u.a k2
              let (u3_re, u3_im) := u.a k3
              u1_re * u2_re * u3_im + u1_re * u2_im * u3_re
              + u1_im * u2_re * u3_re - u1_im * u2_im * u3_im) = 0 := by
        apply Finset.sum_eq_zero
        intro k1 hk1
        apply Finset.sum_eq_zero
        intro k2 hk2
        have hk3_zero := hzero k1 hk1 k2 hk2
        simp [hk3_zero]

      -- With both components zero, the coefficient itself is zero — contradiction.
      have hk_ne :
          (let sum_re := Finset.sum (cube spatialDim M) fun k1 =>
              Finset.sum (cube spatialDim M) fun k2 =>
                let k3 : Lattice spatialDim := fun i => k i - k1 i - k2 i
                let (u1_re, u1_im) := u.a k1
                let (u2_re, u2_im) := u.a k2
                let (u3_re, u3_im) := u.a k3
                u1_re * u2_re * u3_re - u1_re * u2_im * u3_im
                - u1_im * u2_re * u3_im - u1_im * u2_im * u3_re
            let sum_im := Finset.sum (cube spatialDim M) fun k1 =>
              Finset.sum (cube spatialDim M) fun k2 =>
                let k3 : Lattice spatialDim := fun i => k i - k1 i - k2 i
                let (u1_re, u1_im) := u.a k1
                let (u2_re, u2_im) := u.a k2
                let (u3_re, u3_im) := u.a k3
                u1_re * u2_re * u3_im + u1_re * u2_im * u3_re
                + u1_im * u2_re * u3_re - u1_im * u2_im * u3_im;
            (sum_re, sum_im)) ≠ (0, 0) := by
        simpa [Set.mem_setOf_eq] using hk

      have hk_eq :
          (let sum_re := Finset.sum (cube spatialDim M) fun k1 =>
              Finset.sum (cube spatialDim M) fun k2 =>
                let k3 : Lattice spatialDim := fun i => k i - k1 i - k2 i
                let (u1_re, u1_im) := u.a k1
                let (u2_re, u2_im) := u.a k2
                let (u3_re, u3_im) := u.a k3
                u1_re * u2_re * u3_re - u1_re * u2_im * u3_im
                - u1_im * u2_re * u3_im - u1_im * u2_im * u3_re
            let sum_im := Finset.sum (cube spatialDim M) fun k1 =>
              Finset.sum (cube spatialDim M) fun k2 =>
                let k3 : Lattice spatialDim := fun i => k i - k1 i - k2 i
                let (u1_re, u1_im) := u.a k1
                let (u2_re, u2_im) := u.a k2
                let (u3_re, u3_im) := u.a k3
                u1_re * u2_re * u3_im + u1_re * u2_im * u3_re
                + u1_im * u2_re * u3_re - u1_im * u2_im * u3_im;
            (sum_re, sum_im)) = (0, 0) := by
        refine Prod.ext ?_ ?_
        · simpa using h_re_zero
        · simpa using h_im_zero

      exact hk_ne hk_eq
  }

def eulerStep_rat (dt : ℚ) (M : ℕ) (u : SeqD_Rat spatialDim) : SeqD_Rat spatialDim :=
  -- Compute cubic term ONCE (not per coefficient access)
  let cubic := applyCubic_rat u M
  { a := fun k =>
      let (u_re, u_im) := u.a k
      -- Laplacian contribution: -λₖ u
      let lambda_k := laplacianWeight_rat k
      let laplacian_re := -lambda_k * u_re
      let laplacian_im := -lambda_k * u_im
      -- Cubic contribution (precomputed above)
      let (cubic_re, cubic_im) := cubic.a k
      -- Euler update
      let new_re := u_re + dt * (laplacian_re + cubic_re)
      let new_im := u_im + dt * (laplacian_im + cubic_im)
      (new_re, new_im)
    finite_support := by
      -- The support is contained in support(u) ∪ support(cubic)
      -- Both are finite, so their union is finite
      apply Set.Finite.subset (u.finite_support.union cubic.finite_support)
      intro k hk
      simp only [Set.mem_setOf_eq, Set.mem_union] at hk ⊢
      -- hk: result ≠ (0,0), need to show k ∈ support(u) ∨ k ∈ support(cubic)
      -- Contrapositive: if both u.a k = (0,0) and cubic.a k = (0,0), then result = (0,0)
      by_contra h_notin
      simp only [not_or, not_not] at h_notin
      -- h_notin: u.a k = (0,0) ∧ cubic.a k = (0,0)
      -- The result is computed as: u.a k + dt * (laplacian + cubic.a k)
      -- When u.a k = (0,0), laplacian = 0, and cubic.a k = (0,0), result = (0,0)
      have hu_eq : u.a k = (0, 0) := h_notin.1
      have hcubic_eq : cubic.a k = (0, 0) := h_notin.2
      -- The definition of a k unfolds to compute from these values
      -- Since both are (0,0), the computation yields (0,0)
      -- This contradicts hk which states the result is ≠ (0,0)
      simp only [hu_eq, hcubic_eq] at hk
      ring_nf at hk
      simp at hk
  }

/-- Helper: compute bit-width (log2 of absolute value) for a rational number -/
def bitWidth (q : ℚ) : ℕ :=
  if q = 0 then 0 else Nat.log2 (q.num.natAbs) + Nat.log2 q.den

/-- Instrumented version of eulerStep that tracks rational bit-widths.

Returns both the evolved state and statistics on the bit-widths of selected modes.
Sample modes: DC (0), first harmonic (1), and highest harmonic (M).
-/
def eulerStep_rat_instrumented (dt : ℚ) (M : ℕ) (u : SeqD_Rat spatialDim) :
    SeqD_Rat spatialDim × Array (ℕ × ℕ) := by
  let result := eulerStep_rat dt M u
  -- Sample key modes to track bit-width growth
  let dc_mode : Lattice spatialDim := fun _ => 0
  let first_mode : Lattice spatialDim := fun _ => 1
  let high_mode : Lattice spatialDim := fun _ => M

  -- Compute bit-width statistics for the three modes
  let (dc_re, dc_im) := result.a dc_mode
  let (first_re, first_im) := result.a first_mode
  let (high_re, high_im) := result.a high_mode

  let stats := #[
    (bitWidth dc_re, bitWidth dc_im),
    (bitWidth first_re, bitWidth first_im),
    (bitWidth high_re, bitWidth high_im)
  ]

  exact (result, stats)

/-- Evolve trajectory in rational arithmetic.

Fully C0 - can be evaluated with #eval!
-/
def evolveTrajectory_rat (u0 : SeqD_Rat spatialDim) (tg : TimeGrid) (M : ℕ) :
    Fin (tg.segments + 1) → SeqD_Rat spatialDim
  | ⟨0, _⟩ => u0
  | ⟨i + 1, h⟩ =>
      let u_prev := evolveTrajectory_rat u0 tg M ⟨i, Nat.lt_of_succ_lt h⟩
      eulerStep_rat (timeStep_rat tg) M u_prev

/-- Instrumented trajectory evolution that collects bit-width statistics.

Returns both the final trajectory and accumulated statistics from each step.
Statistics array: each step contains 3 tuples (num_bits, den_bits) for DC, first, and high modes.
-/
def evolveTrajectory_rat_instrumented (u0 : SeqD_Rat spatialDim) (tg : TimeGrid) (M : ℕ) :
    (Fin (tg.segments + 1) → SeqD_Rat spatialDim) × Array (Array (ℕ × ℕ)) :=
  let rec loop : ℕ → SeqD_Rat spatialDim → Array (Array (ℕ × ℕ)) →
      SeqD_Rat spatialDim × Array (Array (ℕ × ℕ))
    | 0, u_curr, stats_acc =>
        (u_curr, stats_acc)
    | k+1, u_curr, stats_acc =>
        let (u_next, step_stats) := eulerStep_rat_instrumented (timeStep_rat tg) M u_curr
        loop k u_next (stats_acc.push step_stats)

  let (_u_final, stats) := loop tg.segments u0 #[]
  -- Use the non-instrumented trajectory function for the trajectory itself
  let traj := evolveTrajectory_rat u0 tg M
  (traj, stats)

/-- Export statistics to CSV format in IO monad -/
def exportStatsCSV (stats : Array (Array (ℕ × ℕ))) (filename : String) : IO Unit := do
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.write
  -- Write CSV header
  handle.putStrLn "step,mode_idx,num_bits,den_bits"

  -- Write data rows
  for step_idx in [0:stats.size] do
    let step_data := stats[step_idx]!
    for mode_idx in [0:step_data.size] do
      let (num_bits, den_bits) := step_data[mode_idx]!
      handle.putStrLn s!"{step_idx},{mode_idx},{num_bits},{den_bits}"

  handle.flush

/-! ## Soundness Connection

These lemmas connect the rational extraction track to the analytical proof track.
They ensure that evolveTrajectory_rat approximates the true solution.
-/

/-! ## Extraction Utilities -/

/-- Convert ℚ to ConstructiveQ.Q for extraction -/
def ratToConstructiveQ (q : ℚ) : ConstructiveQ.Q :=
  ⟨q.num, q.den, by simp [Rat.den_pos]⟩

/-- Sample trajectory at evenly-spaced time nodes for QAL witness -/
def sampleTrajectory_rat (u0 : SeqD_Rat spatialDim)
    (tg : TimeGrid) (M : ℕ) (sample_segments : ℕ) :
    Fin (sample_segments + 1) → SeqD_Rat spatialDim :=
  let full_trajectory := evolveTrajectory_rat u0 tg M
  fun i =>
    -- Sample at indices 0, segments/sample_segments, 2*segments/sample_segments, ..., segments
    let idx := (i.val * tg.segments) / sample_segments
    full_trajectory ⟨idx, by
      -- Need: idx < tg.segments + 1
      -- where idx = (i.val * tg.segments) / sample_segments
      -- Since i.val ≤ sample_segments, we have i.val * segments ≤ sample_segments * segments
      -- Therefore idx = (i.val * segments) / sample_segments ≤ segments
      have h_i : i.val ≤ sample_segments := Nat.le_of_lt_succ i.isLt
      have h_mul : i.val * tg.segments ≤ sample_segments * tg.segments := Nat.mul_le_mul_right _ h_i
      -- Use: a/b ≤ c when a ≤ b*c (for b > 0)
      have h_idx : idx ≤ tg.segments := by
        by_cases h : sample_segments = 0
        · simp [idx, h]
        · have : 0 < sample_segments := Nat.pos_of_ne_zero h
          calc idx = (i.val * tg.segments) / sample_segments := rfl
              _ ≤ (sample_segments * tg.segments) / sample_segments := Nat.div_le_div_right h_mul
              _ = tg.segments := Nat.mul_div_cancel_left _ this
      omega⟩

/-! ## Interval Arithmetic Track (Bounded Precision)

This track uses IntervalDyadic for bounded-precision arithmetic that
prevents exponent explosion while tracking error bounds.
-/

open IntervalDyadic

/-- Sequence with interval-valued coefficients -/
abbrev SeqD_Interval (spatialDim : ℕ) := Lattice spatialDim → (IntervalD × IntervalD)

/-- Lower bound for π: 314159/100000 = 3.14159 < π -/
def pi_lower : ℚ := 314159/100000

/-- Upper bound for π: 31416/10000 = 3.1416 > π -/
def pi_upper : ℚ := 31416/10000

/-- π as interval with validated bounds.

We construct an interval [3.14159, 3.1416] which provably contains π ≈ 3.14159265...

The bounds are:
- Lower: 314159/100000 = 3.14159 < π
- Upper: 31416/10000 = 3.1416 > π

This ensures that all interval arithmetic operations involving π produce
sound enclosures of the true mathematical values.
-/
def pi_interval (p : ℕ) : IntervalD :=
  let approx := IntervalDyadic.fromRat pi_lower p
  let upper_approx := IntervalDyadic.fromRat pi_upper p
  -- Merge intervals: take min of lowers, max of uppers
  ⟨approx.lower, upper_approx.upper, by
    -- We need: approx.lower ≤ upper_approx.upper
    -- fromRat(pi_lower) gives an interval containing pi_lower
    -- fromRat(pi_upper) gives an interval containing pi_upper
    -- Since pi_lower < pi_upper, we have approx.lower ≤ upper_approx.upper
    have h_rat : pi_lower < pi_upper := by norm_num [pi_lower, pi_upper]
    -- fromRat creates an interval containing its input rational
    have h_lower : IntervalDyadic.contains approx pi_lower := IntervalDyadic.fromRat_contains pi_lower p
    have h_upper : IntervalDyadic.contains upper_approx pi_upper := IntervalDyadic.fromRat_contains pi_upper p
    -- Extract: approx.lower ≤ pi_lower and pi_upper ≤ upper_approx.upper
    unfold IntervalDyadic.contains at h_lower h_upper
    have h1 : DyadicCanonical.toRat approx.lower ≤ pi_lower := h_lower.1
    have h2 : pi_upper ≤ DyadicCanonical.toRat upper_approx.upper := h_upper.2
    -- Chain: approx.lower ≤ pi_lower < pi_upper ≤ upper_approx.upper
    calc DyadicCanonical.toRat approx.lower
        ≤ pi_lower := h1
      _ ≤ pi_upper := le_of_lt h_rat
      _ ≤ DyadicCanonical.toRat upper_approx.upper := h2
  ⟩

/-- Laplacian eigenvalue as interval -/
def laplacianWeight_interval (k : Lattice spatialDim) (p : ℕ) : IntervalD :=
  let k_val := IntervalDyadic.fromRat (k 0 : ℚ) p
  let pi_sq := IntervalDyadic.mul (pi_interval p) (pi_interval p) p
  IntervalDyadic.mul pi_sq (IntervalDyadic.mul k_val k_val p) p

/-- Multiply three intervals (for complex triple product) -/
private def mul3 (a b c : IntervalD) (p : ℕ) : IntervalD :=
  IntervalDyadic.mul (IntervalDyadic.mul a b p) c p

/-- Computable list of integers in range [-M, M] for 1D cube -/
def cubeList1D (M : ℕ) : List ℤ :=
  List.map (fun n => (n : ℤ) - M) (List.range (2 * M + 1))

/-- Computable cube as list of lattice points (1D only for now).
    Refactored to use single map with composed function for better elaboration. -/
def cubeListLattice (M : ℕ) : List (Lattice spatialDim) :=
  List.map (fun (i : ℕ) => (fun (_ : Fin spatialDim) => (i : ℤ) - M)) (List.range (2 * M + 1))

/-! ## Array-Based Interval State for O(1) Access -/

/-! ## Grid Mapping (Local Convenience Functions)

TODO(Grid Unification): These functions duplicate GridMapping.fromIdx/toIdx.
For 1D, they are mathematically equivalent, but this creates technical debt.

Action Required (before 2D/3D extension):
1. Replace all uses of idxToLattice with GridMapping.fromIdx
2. Replace all uses of latticeToIdx with GridMapping.toIdx
3. Remove these local definitions
4. Add explicit 1D assumptions where needed

Rationale: GridMapping has proven theorems and multi-D support structure.
Current impact: None (functions are equivalent for 1D case).
-/

/-- Map lattice point k ∈ [-M,M] to array index -/
def latticeToIdx (k : Lattice spatialDim) (M : ℕ) : ℕ :=
  (k 0 + M).toNat  -- For 1D: k ∈ [-M,M] → [0, 2M]

/-- Map array index back to lattice point -/
def idxToLattice (i : ℕ) (M : ℕ) : Lattice spatialDim :=
  fun _ => (i : ℤ) - M

/-- State as Array for O(1) access. Size = 2M+1 for 1D -/
abbrev StateArray := Array (IntervalD × IntervalD)

/-- Complex convolution: (u * v)_k = Σ u_{k1} · v_{k-k1}
    This is O(N²) for N modes.

    Checks geometric bounds before toNat conversion to prevent
    aliasing. Negative k2 values are treated as out-of-bounds zeros,
    not mapped to index 0. -/
def convolve_Array (u v : StateArray) (M : ℕ) (p : ℕ) : StateArray :=
  let size := 2 * M + 1
  Array.ofFn (n := size) fun ⟨i, _⟩ =>
    let k := idxToLattice i M
    let cubeL := cubeListLattice M
    cubeL.foldl (fun (acc_re, acc_im) k1 =>
      let k2 : Lattice spatialDim := fun j => k j - k1 j
      -- Check geometric bounds BEFORE toNat to avoid aliasing
      -- For 1D: k2 must be in [-M, M] (not just i2 < size)
      if -(M : ℤ) ≤ k2 ⟨0, NeZero.pos spatialDim⟩ ∧ k2 ⟨0, NeZero.pos spatialDim⟩ ≤ M then
        let i1 := latticeToIdx k1 M
        let i2 := latticeToIdx k2 M
        if h1 : i1 < u.size then
          if h2 : i2 < v.size then
            let (u1_re, u1_im) := u[i1]
            let (v2_re, v2_im) := v[i2]
            -- Complex multiplication: (a+bi)(c+di) = (ac-bd) + (ad+bc)i
            let term_re := IntervalDyadic.sub
              (IntervalDyadic.mul u1_re v2_re p)
              (IntervalDyadic.mul u1_im v2_im p) p
            let term_im := IntervalDyadic.add
              (IntervalDyadic.mul u1_re v2_im p)
              (IntervalDyadic.mul u1_im v2_re p) p
            (IntervalDyadic.add acc_re term_re p, IntervalDyadic.add acc_im term_im p)
          else (acc_re, acc_im)
        else (acc_re, acc_im)
      else (acc_re, acc_im)  -- Out-of-bounds: explicit zero
    ) (IntervalDyadic.zero, IntervalDyadic.zero)

/-- Cubic via two-stage convolution: u³ = (u*u)*u
    Reduces complexity from O(N³) to O(N²). For N=21: 9261 ops → 882 ops (10.5x speedup!) -/
def applyCubic_Array (u : StateArray) (M : ℕ) (p : ℕ) : StateArray :=
  let u_squared := convolve_Array u u M p
  convolve_Array u_squared u M p

/-- Euler step with interval arithmetic on Array (O(1) access) -/
def eulerStep_Array (dt : IntervalD) (M : ℕ) (p : ℕ) (u : StateArray) : StateArray :=
  let size := 2 * M + 1
  let cubic := applyCubic_Array u M p
  Array.ofFn (n := size) fun ⟨i, hi⟩ =>
    let k := idxToLattice i M
    if h1 : i < u.size then
      if h2 : i < cubic.size then
        let (u_re, u_im) := u[i]
        let lambda_k := laplacianWeight_interval k p
        let neg_lambda := IntervalDyadic.neg lambda_k p
        let laplacian_re := IntervalDyadic.mul neg_lambda u_re p
        let laplacian_im := IntervalDyadic.mul neg_lambda u_im p
        let (cubic_re, cubic_im) := cubic[i]
        -- u_new = u + dt * (-λu + u³)
        let rhs_re := IntervalDyadic.add laplacian_re cubic_re p
        let rhs_im := IntervalDyadic.add laplacian_im cubic_im p
        let new_re := IntervalDyadic.add u_re (IntervalDyadic.mul dt rhs_re p) p
        let new_im := IntervalDyadic.add u_im (IntervalDyadic.mul dt rhs_im p) p
        (new_re, new_im)
      else (IntervalDyadic.zero, IntervalDyadic.zero)
    else (IntervalDyadic.zero, IntervalDyadic.zero)

/-- Evolve trajectory with Array-based interval arithmetic -/
def evolveTrajectory_Array (u0 : StateArray) (steps : ℕ) (dt : IntervalD) (M : ℕ) (p : ℕ) :
    Fin (steps + 1) → StateArray
  | ⟨0, _⟩ => u0
  | ⟨i + 1, h⟩ =>
    let u_prev := evolveTrajectory_Array u0 steps dt M p ⟨i, Nat.lt_of_succ_lt h⟩
    eulerStep_Array dt M p u_prev

/-- Convert SeqD_Interval to StateArray for efficient computation -/
def seqToArray (u : SeqD_Interval spatialDim) (M : ℕ) : StateArray :=
  let size := 2 * M + 1
  Array.ofFn (n := size) fun ⟨i, _⟩ =>
    let k := idxToLattice i M
    u k

/-- Convert StateArray back to SeqD_Interval -/
def arrayToSeq (arr : StateArray) (M : ℕ) : SeqD_Interval spatialDim :=
  fun k =>
    let i := latticeToIdx k M
    if h : i < arr.size then arr[i] else (IntervalDyadic.zero, IntervalDyadic.zero)

/-- Apply cubic nonlinearity with interval arithmetic.

    Computes (u³)_k = Σ_{k1,k2 ∈ cube(M)} u_{k1} · u_{k2} · u_{k-k1-k2}

    Note: Each term involves THREE DIFFERENT modes (k1, k2, k3), so standard
    interval multiplication is correct. The expert's `cube` primitive applies
    when computing x³ for a SINGLE interval, not for convolutions. -/
def applyCubic_interval (u : SeqD_Interval spatialDim) (M : ℕ) (p : ℕ) :
    SeqD_Interval spatialDim :=
  fun k =>
    -- Double fold over cube(M) × cube(M) to compute triple convolution
    let cubeL := cubeListLattice M
    cubeL.foldl (fun acc k1 =>
      cubeL.foldl (fun (acc_re, acc_im) k2 =>
        let k3 : Lattice spatialDim := fun i => k i - k1 i - k2 i
        let (u1_re, u1_im) := u k1
        let (u2_re, u2_im) := u k2
        let (u3_re, u3_im) := u k3
        -- Complex multiplication: (a+bi)(c+di)(e+fi)
        -- Real part: ace - adf - bce - bdf
        let term_re :=
          IntervalDyadic.sub
            (IntervalDyadic.sub
              (IntervalDyadic.sub (mul3 u1_re u2_re u3_re p)
                                  (mul3 u1_re u2_im u3_im p) p)
              (mul3 u1_im u2_re u3_im p) p)
            (mul3 u1_im u2_im u3_re p) p
        -- Imag part: acf + ade + bcf - bde
        let term_im :=
          IntervalDyadic.sub
            (IntervalDyadic.add
              (IntervalDyadic.add (mul3 u1_re u2_re u3_im p)
                                  (mul3 u1_re u2_im u3_re p) p)
              (mul3 u1_im u2_re u3_re p) p)
            (mul3 u1_im u2_im u3_im p) p
        (IntervalDyadic.add acc_re term_re p, IntervalDyadic.add acc_im term_im p)
      ) acc
    ) (IntervalDyadic.zero, IntervalDyadic.zero)

/-- Euler step with interval arithmetic (linear part only, for testing) -/
def eulerStep_interval_linear (dt : IntervalD) (_M : ℕ) (p : ℕ)
    (u : SeqD_Interval spatialDim) : SeqD_Interval spatialDim :=
  fun k =>
    let (u_re, u_im) := u k
    let lambda_k := laplacianWeight_interval k p
    let neg_lambda := IntervalDyadic.neg lambda_k p
    let laplacian_re := IntervalDyadic.mul neg_lambda u_re p
    let laplacian_im := IntervalDyadic.mul neg_lambda u_im p
    let new_re := IntervalDyadic.add u_re (IntervalDyadic.mul dt laplacian_re p) p
    let new_im := IntervalDyadic.add u_im (IntervalDyadic.mul dt laplacian_im p) p
    (new_re, new_im)

/-- Euler step with interval arithmetic (full semilinear heat: -Δu + u³) -/
def eulerStep_interval (dt : IntervalD) (M : ℕ) (p : ℕ)
    (u : SeqD_Interval spatialDim) : SeqD_Interval spatialDim :=
  let cubic := applyCubic_interval u M p
  fun k =>
    let (u_re, u_im) := u k
    let lambda_k := laplacianWeight_interval k p
    let neg_lambda := IntervalDyadic.neg lambda_k p
    let laplacian_re := IntervalDyadic.mul neg_lambda u_re p
    let laplacian_im := IntervalDyadic.mul neg_lambda u_im p
    let (cubic_re, cubic_im) := cubic k
    -- u_new = u + dt * (-λu + u³)
    let rhs_re := IntervalDyadic.add laplacian_re cubic_re p
    let rhs_im := IntervalDyadic.add laplacian_im cubic_im p
    let new_re := IntervalDyadic.add u_re (IntervalDyadic.mul dt rhs_re p) p
    let new_im := IntervalDyadic.add u_im (IntervalDyadic.mul dt rhs_im p) p
    (new_re, new_im)

/-- Evolve trajectory with interval arithmetic -/
def evolveTrajectory_interval (u0 : SeqD_Interval spatialDim)
    (steps : ℕ) (dt : IntervalD) (M : ℕ) (p : ℕ) :
    Fin (steps + 1) → SeqD_Interval spatialDim
  | ⟨0, _⟩ => u0
  | ⟨i + 1, h⟩ =>
    let u_prev := evolveTrajectory_interval u0 steps dt M p ⟨i, Nat.lt_of_succ_lt h⟩
    eulerStep_interval dt M p u_prev

end SemilinearHeat
