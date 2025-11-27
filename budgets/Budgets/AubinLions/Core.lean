import Mathlib.Tactic
import Budgets.RellichKondrachovD.Core

/-!
# Quantitative Aubin–Lions core infrastructure

This module packages the reusable, *computational* data that the quantitative
Aubin–Lions construction needs.  The guiding philosophy mirrors the
`RellichKondrachovD` layout:

* make all parameters explicit (time horizon, spatial cutoff, budgets),
* keep witness structures factored (one rounded Fourier grid per time slot),
* avoid enumerating exponentially-large objects (everything is a function type).

The analytic estimates (time-modulus bounds, soundness theorem) will live in
`TimeModulus` and `Soundness`.  By introducing the core structures separately we
can develop and test the extraction story without being blocked on heavy
measure-theoretic proofs.
-/

open scoped BigOperators

namespace AubinLions

open ℓ2ZD

/-- Time-grid parameters for the space–time witness.  We insist that both the
total duration `horizon` and the number of subintervals `segments` are positive,
matching the eventual quantitative statement on `[0, horizon]`. -/
structure TimeGrid where
  /-- Total time horizon `[0, horizon]` (stored as a rational for extraction). -/
  horizon : ℚ
  /-- Number of uniform subintervals used for the time mesh. -/
  segments : ℕ
  /-- Witness that the horizon is strictly positive. -/
  hHorizon : 0 < (horizon : ℝ)
  /-- Witness that the number of segments is strictly positive. -/
  hSegments : 0 < segments
  deriving DecidableEq

namespace TimeGrid

/-- Time mesh size Δt = T / K. -/
@[simp] def mesh (tg : TimeGrid) : ℚ :=
  tg.horizon / tg.segments

/-- The mesh is positive in ℝ. -/
lemma mesh_pos (tg : TimeGrid) : 0 < ((mesh tg : ℚ) : ℝ) := by
  have hT : 0 < (tg.horizon : ℝ) := tg.hHorizon
  have hK : (0 : ℝ) < tg.segments := Nat.cast_pos.mpr tg.hSegments
  have := div_pos hT hK
  simpa [mesh] using this

lemma mesh_pos_rat (tg : TimeGrid) : 0 < mesh tg := by
  have := mesh_pos tg
  exact_mod_cast this

/-- The `i`-th time node on the uniform grid.  We use the left endpoints, so the
final interval `[t_{K-1}, T]` is covered without including `t = T` itself. -/
def node (tg : TimeGrid) : Fin tg.segments → ℚ :=
  fun i => (i : ℚ) * mesh tg

@[simp] lemma node_zero (tg : TimeGrid) :
    tg.node ⟨0, tg.hSegments⟩ = 0 := by
  simp [node]

lemma segments_pos (tg : TimeGrid) : 0 < tg.segments :=
  tg.hSegments

lemma segments_ne_zero (tg : TimeGrid) : tg.segments ≠ 0 :=
  Nat.ne_of_gt tg.segments_pos

lemma node_mono (tg : TimeGrid) {i j : Fin tg.segments} (hij : i ≤ j) :
    tg.node i ≤ tg.node j := by
  have hmesh_nonneg : 0 ≤ mesh tg := le_of_lt (mesh_pos_rat tg)
  have hij' : (i : ℚ) ≤ (j : ℚ) := by exact_mod_cast hij
  exact mul_le_mul_of_nonneg_right hij' hmesh_nonneg

lemma node_nonneg (tg : TimeGrid) (i : Fin tg.segments) :
    0 ≤ tg.node i := by
  have hmesh_nonneg : 0 ≤ mesh tg := le_of_lt (mesh_pos_rat tg)
  have hi_nonneg : 0 ≤ (i : ℚ) := by exact_mod_cast Nat.zero_le i.1
  have : tg.node i = (i : ℚ) * mesh tg := rfl
  simpa [this] using mul_nonneg hi_nonneg hmesh_nonneg

lemma node_le_horizon (tg : TimeGrid) (i : Fin tg.segments) :
    tg.node i ≤ tg.horizon := by
  have hseg_pos : 0 < (tg.segments : ℚ) := by
    exact_mod_cast tg.hSegments
  have hi_le : (i : ℚ) ≤ tg.segments := by
    exact_mod_cast (le_of_lt i.is_lt)
  have hH_pos : 0 < tg.horizon := by
    exact_mod_cast tg.hHorizon
  have hH_nonneg : 0 ≤ tg.horizon := le_of_lt hH_pos
  have hseg_ne : (tg.segments : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt tg.hSegments)
  have hfrac : (i : ℚ) / tg.segments ≤ 1 := by
    have hseg_inv_nonneg :
        0 ≤ (tg.segments : ℚ)⁻¹ := inv_nonneg.mpr (le_of_lt hseg_pos)
    have := mul_le_mul_of_nonneg_right hi_le hseg_inv_nonneg
    simpa [div_eq_mul_inv, hseg_ne] using this
  have hrepr :
      tg.node i = tg.horizon * ((i : ℚ) / tg.segments) := by
    calc
      tg.node i
          = (i : ℚ) * mesh tg := rfl
      _ = (i : ℚ) * (tg.horizon / tg.segments) := rfl
      _ = (i : ℚ) * (tg.horizon * (tg.segments : ℚ)⁻¹) := by
        simp [div_eq_mul_inv]
      _ = tg.horizon * ((i : ℚ) * (tg.segments : ℚ)⁻¹) := by
        ring
      _ = tg.horizon * ((i : ℚ) / tg.segments) := by
        simp [div_eq_mul_inv]
  calc
    tg.node i = tg.horizon * ((i : ℚ) / tg.segments) := hrepr
    _ ≤ tg.horizon * 1 := by
      exact mul_le_mul_of_nonneg_left hfrac hH_nonneg
    _ = tg.horizon := by simp

lemma mesh_mul_segments (tg : TimeGrid) :
    mesh tg * tg.segments = tg.horizon := by
  have hseg_ne : (tg.segments : ℚ) ≠ 0 := by
    exact_mod_cast tg.segments_ne_zero
  have hcalc : (tg.horizon / tg.segments) * tg.segments = tg.horizon := by
    field_simp [hseg_ne]
  simpa [mesh] using hcalc

/-- Endpoints of the time grid, including the final right endpoint. -/
def endpoint (tg : TimeGrid) (i : Fin (tg.segments + 1)) : ℚ :=
  if h : (i : ℕ) < tg.segments then
    tg.node ⟨i, h⟩
  else
    tg.horizon

lemma endpoint_mem {tg : TimeGrid} {i : Fin (tg.segments + 1)}
    (h : (i : ℕ) < tg.segments) :
    tg.endpoint i = tg.node ⟨i, h⟩ := by
  simp [endpoint, h]

lemma endpoint_zero (tg : TimeGrid) :
    tg.endpoint 0 = 0 := by
  have h : ((0 : Fin (tg.segments + 1)) : ℕ) < tg.segments :=
    by simpa using tg.segments_pos
  have := endpoint_mem (tg := tg) (i := 0) h
  simpa [node] using this

lemma endpoint_succ {tg : TimeGrid} {i : Fin tg.segments} :
    tg.endpoint i.castSucc =
        tg.node i := by
  have h : ((i.castSucc : Fin (tg.segments + 1)) : ℕ) < tg.segments := by
    simp -- using Nat.lt_of_lt_of_le i.property (le_of_eq rfl)
  simpa using endpoint_mem (tg := tg) (i := i.castSucc) h

lemma endpoint_last (tg : TimeGrid) :
    tg.endpoint (Fin.last tg.segments) = tg.horizon := by
  have : (Fin.last tg.segments : ℕ) = tg.segments := by simp
  have hfalse : ¬((Fin.last tg.segments : ℕ) < tg.segments) := by simp
  simp [endpoint]


lemma node_diff (tg : TimeGrid) (i j : Fin tg.segments) :
    tg.node j - tg.node i
      = ((j : ℚ) - (i : ℚ)) * mesh tg := by
  have : (j : ℚ) * mesh tg - (i : ℚ) * mesh tg
      = ((j : ℚ) - (i : ℚ)) * mesh tg := by ring
  simpa [node] using this

lemma node_diff_real (tg : TimeGrid) (i j : Fin tg.segments) :
    ((tg.node j : ℚ) : ℝ) - ((tg.node i : ℚ) : ℝ)
      = ((((j : ℚ) - (i : ℚ)) * mesh tg : ℚ)) := by
  exact_mod_cast node_diff tg i j

end TimeGrid

/-
## Budget parameters and admissible curves
-/

/-- Global parameters controlling the space (ε, H¹ radius) and time (derivative
budget and horizon) components of the quantitative Aubin–Lions theorem.  We
store everything as rationals so that downstream witness extraction works
uniformly across the codebase. -/
structure BudgetParams where
  /-- Spatial accuracy ε. -/
  ε : ℚ
  /-- Spatial H¹ radius R. -/
  R : ℚ
  /-- Time-derivative budget S (proxy for ‖∂ₜu‖_{H⁻¹}). -/
  S : ℚ
  /-- Time horizon T. -/
  horizon : ℚ
  hε : 0 < (ε : ℝ)
  hR : 0 < (R : ℝ)
  hS : 0 < (S : ℝ)
  hHorizon : 0 < (horizon : ℝ)
  deriving DecidableEq

namespace BudgetParams

@[simp] lemma horizon_pos (P : BudgetParams) : 0 < (P.horizon : ℝ) :=
  P.hHorizon

@[simp] lemma ε_pos (P : BudgetParams) : 0 < (P.ε : ℝ) :=
  P.hε

@[simp] lemma R_pos (P : BudgetParams) : 0 < (P.R : ℝ) :=
  P.hR

@[simp] lemma S_pos (P : BudgetParams) : 0 < (P.S : ℝ) :=
  P.hS

/-- Package the time-horizon information and a choice of `segments` into an
actual `TimeGrid`. -/
def toTimeGrid (P : BudgetParams) (segments : ℕ) (hsegments : 0 < segments) :
    TimeGrid :=
  { horizon := P.horizon
    segments := segments
    hHorizon := P.horizon_pos
    hSegments := hsegments }

@[simp] lemma toTimeGrid_horizon (P : BudgetParams) {segments : ℕ}
    (hsegments : 0 < segments) :
    (P.toTimeGrid segments hsegments).horizon = P.horizon := rfl

end BudgetParams

/-- Abstract data describing an H¹-bounded, mean-zero time curve together with a
proxy for the H⁻¹ time-derivative budget.  At this stage we merely record the
quantities we will later prove about concrete analytic functions. -/
structure Admissible (d : ℕ) (P : BudgetParams) where
  /-- The underlying curve u : [0, T] → SeqD d. -/
  curve : Set.Icc (0 : ℝ) (P.horizon : ℝ) → ℓ2ZD.SeqD d
  /-- A “formal time derivative” placeholder.  Later files will connect this to
  H⁻¹ control; for now it is just part of the data. -/
  timeDeriv : Set.Icc (0 : ℝ) (P.horizon : ℝ) → ℓ2ZD.SeqD d
  /-- Every time slice is mean zero. -/
  meanZero_curve : ∀ t, meanZero (curve t)
  /-- Each time slice lies in the H¹ ball of radius R. -/
  inH1_curve : ∀ t, InH1Ball (P.R : ℝ) (curve t)
  /-- Quantitative bound representing ∫‖u(t)‖_{H¹}² dt (to be justified later). -/
  h1Energy : ℝ
  h1Energy_nonneg : 0 ≤ h1Energy
  h1Energy_bound : h1Energy ≤ (P.R : ℝ)^2
  /-- Quantitative bound representing ∫‖∂ₜu(t)‖_{H⁻¹}² dt. -/
  derivEnergy : ℝ
  derivEnergy_nonneg : 0 ≤ derivEnergy
  derivEnergy_bound : derivEnergy ≤ (P.S : ℝ)^2
  /-- Continuous time-modulus bound in H⁻¹ weights (Bochner W^{1,2} estimate).

  This field provides the **continuous** quantitative bound for any pair of times
  t₁, t₂ ∈ [0, horizon], not just at discrete grid nodes. For any finite set F
  of lattice points, the H⁻¹-weighted difference satisfies:

    ∑_{k ∈ F} hminusWeight(k) · ‖curve(t₂).a(k) - curve(t₁).a(k)‖² ≤ S² · (t₂ - t₁)

  This is equivalent to the classical Bochner-Sobolev estimate:
    ‖u(t₂) - u(t₁)‖_{H⁻¹}² ≤ S² · |t₂ - t₁|

  but formulated constructively via finite sums over lattice points.

  **Key property:** Applies to ALL real times in [0, horizon], enabling integration
  of time-modulus bounds over time slabs in the Quantitative Aubin-Lions theorem.

  **Extractability:** Fully constructive - just data/proof in the structure, no
  non-constructive choices. -/
  timeModulus :
    ∀ {t₁ t₂ : Set.Icc (0 : ℝ) (P.horizon : ℝ)},
      ((t₁ : ℝ) ≤ (t₂ : ℝ)) →
      ∀ (F : Finset (ℓ2ZD.Lattice d)),
        Finset.sum F
            (fun k =>
              ℓ2ZD.hminusWeight k *
                ‖(curve t₂).a k - (curve t₁).a k‖^2)
          ≤ (P.S : ℝ)^2 * ((t₂ : ℝ) - (t₁ : ℝ))
  /-- Continuity of curve coefficients.

  For each lattice point k, the coefficient function t ↦ curve(t).a(k) is continuous.
  This is physically reasonable: smooth trajectories have continuous coefficients.
  This assumption enables integration over time slabs by ensuring measurability. -/
  curve_coeff_continuous : ∀ (k : ℓ2ZD.Lattice d),
    Continuous (fun t => (curve t).a k)

namespace Admissible

variable {d : ℕ} {P : BudgetParams}

@[simp] lemma coe_time (t : Set.Icc (0 : ℝ) (P.horizon : ℝ)) :
    ((t : ℝ) : ℝ) = t := rfl

/-- Evaluate an admissible curve at the given time. -/
@[simp] def eval (A : Admissible d P) (t : Set.Icc (0 : ℝ) (P.horizon : ℝ)) :
    ℓ2ZD.SeqD d :=
  A.curve t

lemma eval_meanZero (A : Admissible d P)
    (t : Set.Icc (0 : ℝ) (P.horizon : ℝ)) :
    meanZero (A.eval t) :=
  A.meanZero_curve t

lemma eval_inH1 (A : Admissible d P)
    (t : Set.Icc (0 : ℝ) (P.horizon : ℝ)) :
    InH1Ball (P.R : ℝ) (A.eval t) :=
  A.inH1_curve t

/-- Sample an admissible curve at the nodes of a `TimeGrid` whose horizon
matches the budget horizon.  This provides the discrete per-slot data that will
later be rounded into the factored witness. -/
def sampleAtNodes (A : Admissible d P) (tg : TimeGrid)
    (hcompat : tg.horizon = P.horizon) :
    Fin tg.segments → ℓ2ZD.SeqD d :=
  fun i =>
    let value : ℝ := (tg.node i : ℚ)
    have h0q : 0 ≤ tg.node i := TimeGrid.node_nonneg tg i
    have h0 : 0 ≤ value := by
      have : 0 ≤ (tg.node i : ℝ) := by exact_mod_cast h0q
      simpa [value] using this
    have h1q : tg.node i ≤ tg.horizon := TimeGrid.node_le_horizon tg i
    have h1tg : value ≤ (tg.horizon : ℝ) := by
      have : (tg.node i : ℝ) ≤ (tg.horizon : ℝ) := by exact_mod_cast h1q
      simpa [value] using this
    have h1 : value ≤ (P.horizon : ℝ) := by
      simpa [value, hcompat] using h1tg
    A.curve ⟨value, ⟨by simpa [value] using h0, h1⟩⟩

lemma sampleAtNodes_meanZero (A : Admissible d P) (tg : TimeGrid)
    (hcompat : tg.horizon = P.horizon) (i : Fin tg.segments) :
    meanZero (A.sampleAtNodes tg hcompat i) := by
  dsimp [sampleAtNodes]
  exact A.meanZero_curve _

lemma sampleAtNodes_inH1 (A : Admissible d P) (tg : TimeGrid)
    (hcompat : tg.horizon = P.horizon) (i : Fin tg.segments) :
    InH1Ball (P.R : ℝ) (A.sampleAtNodes tg hcompat i) := by
  dsimp [sampleAtNodes]
  exact A.inH1_curve _

lemma timeModulus_nodes {d : ℕ} [NeZero d]
    (A : Admissible d P) (tg : TimeGrid)
    (hcompat : tg.horizon = P.horizon)
    {i j : Fin tg.segments} (hij : i ≤ j)
    (F : Finset (ℓ2ZD.Lattice d)) :
    Finset.sum F
        (fun k =>
          ℓ2ZD.hminusWeight k *
            ‖(A.sampleAtNodes tg hcompat j).a k
                - (A.sampleAtNodes tg hcompat i).a k‖^2)
      ≤ (P.S : ℝ)^2 *
          (((tg.node j : ℚ) : ℝ) - ((tg.node i : ℚ) : ℝ)) := by
  classical
  have hnode_nonneg (t : Fin tg.segments) :
      0 ≤ ((tg.node t : ℚ) : ℝ) := by
    have := TimeGrid.node_nonneg tg t
    exact_mod_cast this
  have hnode_le :
      ((tg.node i : ℚ) : ℝ) ≤ ((tg.node j : ℚ) : ℝ) := by
    have := TimeGrid.node_mono tg hij
    exact_mod_cast this
  have hnode_le_horizon (t : Fin tg.segments) :
      ((tg.node t : ℚ) : ℝ) ≤ (P.horizon : ℝ) := by
    have := TimeGrid.node_le_horizon tg t
    have : ((tg.node t : ℚ) : ℝ) ≤ (tg.horizon : ℝ) := by
      exact_mod_cast this
    simpa [hcompat] using this
  set t₁ : Set.Icc (0 : ℝ) (P.horizon : ℝ) :=
    ⟨((tg.node i : ℚ) : ℝ),
      And.intro (hnode_nonneg i) (hnode_le_horizon i)⟩
  set t₂ : Set.Icc (0 : ℝ) (P.horizon : ℝ) :=
    ⟨((tg.node j : ℚ) : ℝ),
      And.intro (hnode_nonneg j) (hnode_le_horizon j)⟩
  have horder : (t₁ : ℝ) ≤ (t₂ : ℝ) := by
    simpa [t₁, t₂] using hnode_le
  have hdiff :
      ((t₂ : ℝ) - (t₁ : ℝ))
        = (((tg.node j : ℚ) : ℝ) - ((tg.node i : ℚ) : ℝ)) := by
    rfl
  have := A.timeModulus horder F
  simpa [t₁, t₂, hdiff, sampleAtNodes] using this

lemma sample_cube_diff_bound {d : ℕ} [NeZero d]
    (A : Admissible d P) (tg : TimeGrid)
    (hcompat : tg.horizon = P.horizon)
    {i j : Fin tg.segments} (hij : i ≤ j)
    (M : ℕ) :
    Finset.sum (ℓ2ZD.cube d M)
        (fun k =>
          ‖(A.sampleAtNodes tg hcompat j).a k
              - (A.sampleAtNodes tg hcompat i).a k‖^2)
      ≤ ℓ2ZD.h1CubeBound d M *
        (P.S : ℝ)^2 *
          (((tg.node j : ℚ) : ℝ) - ((tg.node i : ℚ) : ℝ)) := by
  classical
  have hsubset :
      ∀ k ∈ ℓ2ZD.cube d M, k ∈ ℓ2ZD.cube d M := fun _ hk => hk
  have hbound :=
    timeModulus_nodes (d := d) (A := A) tg hcompat hij
      (F := ℓ2ZD.cube d M)
  have hsum :=
    ℓ2ZD.sum_sq_le_hminus (d := d) (M := M)
      (F := ℓ2ZD.cube d M)
      (coeff := fun k =>
        (A.sampleAtNodes tg hcompat j).a k
        - (A.sampleAtNodes tg hcompat i).a k) hsubset
  have hmul :=
    mul_le_mul_of_nonneg_left hbound
      (le_of_lt (ℓ2ZD.h1CubeBound_pos d M))
  have htotal := le_trans hsum hmul
  simpa [mul_comm, mul_left_comm, mul_assoc] using htotal

end Admissible

/-- Spatial grid points are exactly the QRK-D witnesses taken at cutoff `M`. -/
abbrev SpaceGridPoint (d : ℕ) (ε R : ℚ) (M : ℕ) :=
  ℓ2ZD.GridPointD d ε R M

/-- Convert a spatial grid point to the corresponding sequence witness. -/
noncomputable def evalSpaceSlice {d : ℕ} (ε R : ℚ) (M : ℕ)
    (g : SpaceGridPoint d ε R M) : ℓ2ZD.SeqD d :=
  ℓ2ZD.gridToSeqD ε R M g

lemma evalSpaceSlice_meanZero {d : ℕ} (ε R : ℚ) (M : ℕ)
    (g : SpaceGridPoint d ε R M) :
    meanZero (evalSpaceSlice ε R M g) := by
  simpa using ℓ2ZD.gridToSeqD_meanZero (d := d) ε R M g

/-- A *space–time* witness stores one spatial grid point per time interval.  The
temporal component remains factored: no exponential enumeration, just a
dependent function `Fin segments → GridPoint`. -/
structure SpaceTimeGridPoint (d : ℕ) (ε R : ℚ) (M : ℕ) (tg : TimeGrid) where
  /-- Fourier grid chosen for each time slab. -/
  coeffs : Fin tg.segments → SpaceGridPoint d ε R M

namespace SpaceTimeGridPoint

/-- Evaluate a space–time grid at a specific slot as a `SeqD` witness. -/
noncomputable def slice {d : ℕ} {ε R : ℚ} {M : ℕ} {tg : TimeGrid}
    (g : SpaceTimeGridPoint d ε R M tg) (i : Fin tg.segments) : ℓ2ZD.SeqD d :=
  evalSpaceSlice ε R M (g.coeffs i)

@[simp] lemma slice_apply {d : ℕ} {ε R : ℚ} {M : ℕ} {tg : TimeGrid}
    (g : SpaceTimeGridPoint d ε R M tg) (i : Fin tg.segments) :
    slice g i = evalSpaceSlice ε R M (g.coeffs i) := rfl

lemma slice_meanZero {d : ℕ} {ε R : ℚ} {M : ℕ} {tg : TimeGrid}
    (g : SpaceTimeGridPoint d ε R M tg) (i : Fin tg.segments) :
    meanZero (slice g i) := by
  simpa [slice] using
    ℓ2ZD.gridToSeqD_meanZero (d := d) ε R M (g.coeffs i)

end SpaceTimeGridPoint

/-- Space–time witness package: records the spatial cutoff `M`, the time grid,
and the actual grid point assignment.  This mirrors the `WitnessPkgD` pattern
from the QRK files. -/
structure WitnessPkg (d : ℕ) (ε R : ℚ) where
  /-- Spatial frequency cutoff (shared by every time slice). -/
  cutoff : ℕ
  /-- Time discretisation grid. -/
  timeGrid : TimeGrid
  /-- Factored coefficient assignment. -/
  point : SpaceTimeGridPoint d ε R cutoff timeGrid

/-- Convenience constructor for the “all-zero” witness, useful as a basepoint
when reasoning about rounded data. -/
noncomputable def zeroWitness (d : ℕ) (ε R : ℚ)
    (M : ℕ) (tg : TimeGrid) : SpaceTimeGridPoint d ε R M tg :=
  ⟨fun _ => ℓ2ZD.zeroGridPointD (d := d) ε R M⟩

/-
## Spatial projection (Fourier truncation)
-/

section SpatialProjection

variable {d : ℕ} [NeZero d]

/-- Spectral truncation onto the cube `[-M,M]^d`.  Inside the cube we keep the
original coefficients, outside we zero them out. -/
noncomputable def truncate (M : ℕ) (x : ℓ2ZD.SeqD d) : ℓ2ZD.SeqD d := by
  classical
  refine ⟨fun k => if k ∈ cube d M then x.a k else 0, ?_⟩
  refine summable_of_ne_finset_zero (s := cube d M) ?_
  intro k hk
  by_cases h : k ∈ cube d M
  · exact (hk h).elim
  · simp [h]

@[simp] lemma truncate_apply {d : ℕ} [NeZero d] {M : ℕ}
    {x : ℓ2ZD.SeqD d} {k : ℓ2ZD.Lattice d} :
    (truncate M x).a k = if k ∈ cube d M then x.a k else 0 := rfl

lemma truncate_mem {d : ℕ} [NeZero d] {M : ℕ} {x : ℓ2ZD.SeqD d}
    {k : ℓ2ZD.Lattice d} (hk : k ∈ cube d M) :
    (truncate M x).a k = x.a k := by
  simp [truncate_apply, hk]

lemma truncate_not_mem {d : ℕ} [NeZero d] {M : ℕ} {x : ℓ2ZD.SeqD d}
    {k : ℓ2ZD.Lattice d} (hk : k ∉ cube d M) :
    (truncate M x).a k = 0 := by
  simp [truncate_apply, hk]

lemma truncate_origin {d : ℕ} [NeZero d] {M : ℕ} {x : ℓ2ZD.SeqD d} :
    (truncate M x).a (fun _ => 0) = x.a (fun _ => 0) := by
  have h0 : (fun _ => (0 : ℤ)) ∈ cube d M :=
    ℓ2ZD.zero_mem_cube (d := d) (M := M)
  simp [truncate_apply, h0]

lemma truncate_meanZero {d : ℕ} [NeZero d] {M : ℕ} {x : ℓ2ZD.SeqD d}
    (hmean : meanZero x) :
    meanZero (truncate M x) := by
  unfold meanZero at hmean
  unfold meanZero
  have h0 : (fun _ => (0 : ℤ)) ∈ cube d M :=
    ℓ2ZD.zero_mem_cube (d := d) (M := M)
  simpa [truncate_apply, h0] using hmean

end SpatialProjection

/-! ## Zero sequence -/

/-- The zero element of SeqD d: all coefficients are zero. -/
noncomputable def zeroSeqD (d : ℕ) : SeqD d where
  a := fun _ => 0
  summable_sq := by
    simp only [norm_zero, sq, zero_mul]
    exact summable_zero

@[simp] lemma zeroSeqD_apply (d : ℕ) (k : Lattice d) :
    (zeroSeqD d).a k = 0 := rfl

lemma zeroSeqD_meanZero (d : ℕ) :
    meanZero (zeroSeqD d) := by
  unfold meanZero
  simp [zeroSeqD]

end AubinLions
