import Budgets.SemilinearHeat.Spaces
import Budgets.SemilinearHeat.Operator
import Budgets.SemilinearHeat.Nonlinearity

/-!
# Semilinear Heat PDE (1D) – Galerkin projection infrastructure

This file packages the Galerkin-system scaffolding required for the interval
semilinear heat plan.  We work entirely in the `SeqD` model: each level
corresponds to truncating the odd 2-periodic coefficient lattice to
`cube 1 (M n)` and the projection is just the constructive `truncate` map used
throughout the QRK/QAL stack.  The lemmas stated here will later be used by
the Galerkin ODE construction and the energy estimates.
-/

open scoped BigOperators

namespace SemilinearHeat

open RellichKondrachovInterval AubinLions

noncomputable section

/-- Extensionality for Dirichlet sequences (1D). -/
@[ext] lemma dirichletSeq_ext {u v : DirichletSeq}
    (h : ∀ k, u.a k = v.a k) : u = v := by
  cases' u with ua usa
  cases' v with va vsa
  have hfun : ua = va := funext h
  subst hfun
  rfl

/-- Inclusion of lattice cubes when the cutoff grows. -/
lemma cube_subset {M N : ℕ} (h : M ≤ N) :
    ℓ2ZD.cube spatialDim M ⊆ ℓ2ZD.cube spatialDim N := by
  intro k hk
  have hk' := (ℓ2ZD.mem_cube.mp hk)
  refine (ℓ2ZD.mem_cube).mpr ?_
  intro i
  have hi := hk' i
  have hneg : -(N : ℤ) ≤ -(M : ℤ) :=
    neg_le_neg (Int.ofNat_le.mpr h)
  have hpos : (M : ℤ) ≤ (N : ℤ) := Int.ofNat_le.mpr h
  exact ⟨le_trans hneg hi.1, le_trans hi.2 hpos⟩

@[simp] lemma truncate_idem (M : ℕ) (u : DirichletSeq) :
    AubinLions.truncate (d := spatialDim) M
        (AubinLions.truncate (d := spatialDim) M u)
      = AubinLions.truncate (d := spatialDim) M u := by
  refine dirichletSeq_ext ?_
  intro k
  by_cases hk : k ∈ ℓ2ZD.cube spatialDim M
  · simp [AubinLions.truncate_apply, hk]
  · simp [AubinLions.truncate_apply, hk]

lemma truncate_comp_of_le {M N : ℕ} (h : M ≤ N)
    (u : DirichletSeq) :
    AubinLions.truncate (d := spatialDim) M
        (AubinLions.truncate (d := spatialDim) N u)
      = AubinLions.truncate (d := spatialDim) M u := by
  refine dirichletSeq_ext ?_
  intro k
  by_cases hk : k ∈ ℓ2ZD.cube spatialDim M
  · have hk' : k ∈ ℓ2ZD.cube spatialDim N :=
      cube_subset (M := M) (N := N) h hk
    simp [AubinLions.truncate_apply, hk, hk']
  · simp [AubinLions.truncate_apply, hk]

@[simp] lemma truncate_coeff_mem {M : ℕ} {u : DirichletSeq}
    {k : ℓ2ZD.Lattice spatialDim}
    (hk : k ∈ ℓ2ZD.cube spatialDim M) :
    (AubinLions.truncate (d := spatialDim) M u).a k = u.a k :=
  AubinLions.truncate_mem (d := spatialDim) (M := M) (x := u) hk

@[simp] lemma truncate_coeff_not_mem {M : ℕ} {u : DirichletSeq}
    {k : ℓ2ZD.Lattice spatialDim}
    (hk : k ∉ ℓ2ZD.cube spatialDim M) :
    (AubinLions.truncate (d := spatialDim) M u).a k = 0 :=
  AubinLions.truncate_not_mem (d := spatialDim) (M := M) (x := u) hk

lemma truncate_coeff_sq_le {M : ℕ} (u : DirichletSeq)
    (k : ℓ2ZD.Lattice spatialDim) :
    ‖(AubinLions.truncate (d := spatialDim) M u).a k‖^2
      ≤ ‖u.a k‖^2 := by
  by_cases hk : k ∈ ℓ2ZD.cube spatialDim M
  · simp [AubinLions.truncate_apply, hk]
  · have hnonneg : 0 ≤ ‖u.a k‖^2 := sq_nonneg _
    convert hnonneg using 1
    simp [AubinLions.truncate_apply, hk]

lemma truncate_inH1Ball {M : ℕ} {R : ℝ} {u : DirichletSeq}
    (hH1 : ℓ2ZD.InH1Ball R u) :
    ℓ2ZD.InH1Ball R (AubinLions.truncate (d := spatialDim) M u) := by
  intro F
  have hsum := hH1 F
  have hterm :
      Finset.sum F (fun k => ℓ2ZD.h1Weight k *
        ‖(AubinLions.truncate (d := spatialDim) M u).a k‖^2)
      ≤ Finset.sum F (fun k => ℓ2ZD.h1Weight k * ‖u.a k‖^2) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have hcoeff := truncate_coeff_sq_le (M := M) (u := u) k
    have hweight_nonneg : 0 ≤ ℓ2ZD.h1Weight k :=
      le_of_lt (ℓ2ZD.h1Weight_pos (d := spatialDim) k)
    exact mul_le_mul_of_nonneg_left hcoeff hweight_nonneg
  exact le_trans hterm hsum

lemma truncate_inHminusBall {M : ℕ} {S : ℝ} {u : DirichletSeq}
    (hH : ℓ2ZD.InHminusBall S u) :
    ℓ2ZD.InHminusBall S (AubinLions.truncate (d := spatialDim) M u) := by
  intro F
  have hsum := hH F
  have hterm :
      Finset.sum F (fun k => ℓ2ZD.hminusWeight k *
        ‖(AubinLions.truncate (d := spatialDim) M u).a k‖^2)
      ≤ Finset.sum F (fun k => ℓ2ZD.hminusWeight k * ‖u.a k‖^2) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have hcoeff := truncate_coeff_sq_le (M := M) (u := u) k
    have hnonneg : 0 ≤ ℓ2ZD.hminusWeight k :=
      ℓ2ZD.hminusWeight_nonneg (d := spatialDim) k
    exact mul_le_mul_of_nonneg_left hcoeff hnonneg
  exact le_trans hterm hsum

/-! ## Galerkin systems -/

structure GalerkinSystem where
  /-- Frequency cutoff at level `n`. -/
  level : ℕ → ℕ
  /-- Monotonicity ensures nested finite-dimensional spaces. -/
  level_mono : Monotone level
  /-- Every level keeps at least the zero frequency. -/
  level_pos : ∀ n, 0 < level n

namespace GalerkinSystem

variable (G : GalerkinSystem)

/-- Frequency cube used at level `n`. -/
def support (n : ℕ) : Finset (ℓ2ZD.Lattice spatialDim) :=
  ℓ2ZD.cube spatialDim (G.level n)

/-- Galerkin projection: truncate to the matching cube. -/
def project (n : ℕ) (u : DirichletSeq) : DirichletSeq :=
  AubinLions.truncate (d := spatialDim) (G.level n) u

@[simp] lemma support_subset {n m : ℕ} (hnm : n ≤ m) :
    G.support n ⊆ G.support m := by
  apply cube_subset
  exact G.level_mono hnm

lemma project_idem (n : ℕ) (u : DirichletSeq) :
    G.project n (G.project n u) = G.project n u := by
  dsimp [project]
  exact truncate_idem (M := G.level n) (u := u)

lemma project_comp_of_le {n m : ℕ} (hnm : n ≤ m)
    (u : DirichletSeq) :
    G.project n (G.project m u) = G.project n u := by
  dsimp [project]
  have hlev := G.level_mono hnm
  exact truncate_comp_of_le (M := G.level n) (N := G.level m) hlev u

lemma project_meanZero (n : ℕ) {u : DirichletSeq}
    (hmean : ℓ2ZD.meanZero u) :
    ℓ2ZD.meanZero (G.project n u) := by
  dsimp [project]
  exact AubinLions.truncate_meanZero (d := spatialDim) (M := G.level n)
        (x := u) hmean

lemma project_inH1 (n : ℕ) {R : ℝ} {u : DirichletSeq}
    (hH1 : ℓ2ZD.InH1Ball R u) :
    ℓ2ZD.InH1Ball R (G.project n u) :=
  truncate_inH1Ball (M := G.level n) (u := u) hH1

lemma project_inHminus (n : ℕ) {S : ℝ} {u : DirichletSeq}
    (hH : ℓ2ZD.InHminusBall S u) :
    ℓ2ZD.InHminusBall S (G.project n u) :=
  truncate_inHminusBall (M := G.level n) (u := u) hH

lemma project_coeff_mem {n : ℕ} {u : DirichletSeq}
    {k : ℓ2ZD.Lattice spatialDim}
    (hk : k ∈ G.support n) :
    (G.project n u).a k = u.a k :=
  truncate_coeff_mem (M := G.level n) (u := u) hk

lemma project_coeff_not_mem {n : ℕ} {u : DirichletSeq}
    {k : ℓ2ZD.Lattice spatialDim}
    (hk : k ∉ G.support n) :
    (G.project n u).a k = 0 :=
  truncate_coeff_not_mem (M := G.level n) (u := u) hk

lemma sum_support_project_diff_hminus (n : ℕ)
    (u v : DirichletSeq) :
    Finset.sum (G.support n)
        (fun k => ℓ2ZD.hminusWeight k *
          ‖(G.project n u).a k - (G.project n v).a k‖^2)
      = Finset.sum (G.support n)
          (fun k => ℓ2ZD.hminusWeight k * ‖u.a k - v.a k‖^2) := by
  classical
  unfold support
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [project_coeff_mem (G := G) (n := n) (u := u) hk,
    project_coeff_mem (G := G) (n := n) (u := v) hk]

lemma sum_support_project_diff_h1 (n : ℕ)
    (u v : DirichletSeq) :
    Finset.sum (G.support n)
        (fun k => ℓ2ZD.h1Weight k *
          ‖(G.project n u).a k - (G.project n v).a k‖^2)
      = Finset.sum (G.support n)
          (fun k => ℓ2ZD.h1Weight k * ‖u.a k - v.a k‖^2) := by
  classical
  unfold support
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [project_coeff_mem (G := G) (n := n) (u := u) hk,
    project_coeff_mem (G := G) (n := n) (u := v) hk]

lemma project_coeff_sq_le {n : ℕ} (u : DirichletSeq)
    (k : ℓ2ZD.Lattice spatialDim) :
    ‖(G.project n u).a k‖^2 ≤ ‖u.a k‖^2 :=
  truncate_coeff_sq_le (M := G.level n) (u := u) k

lemma gradEnergyOn_project (n : ℕ) (u : DirichletSeq) :
    gradEnergyOn (G.support n) (G.project n u)
      = gradEnergyOn (G.support n) u := by
  classical
  unfold gradEnergyOn support
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hcoeff := project_coeff_mem (G := G) (n := n) (u := u) hk
  simp [hcoeff]

lemma gradEnergyOn_project_le (n : ℕ) (u : DirichletSeq)
    (F : Finset (ℓ2ZD.Lattice spatialDim)) :
    gradEnergyOn F (G.project n u) ≤ gradEnergyOn F u := by
  unfold gradEnergyOn
  refine Finset.sum_le_sum ?_
  intro k hk
  have hcoeff := project_coeff_sq_le (G := G) (n := n) (u := u) k
  have hweight := laplacianWeight_nonneg k
  exact mul_le_mul_of_nonneg_left hcoeff hweight

lemma massEnergyOn_project_le (n : ℕ) (u : DirichletSeq)
    (F : Finset (ℓ2ZD.Lattice spatialDim)) :
    massEnergyOn F (G.project n u) ≤ massEnergyOn F u := by
  unfold massEnergyOn
  refine Finset.sum_le_sum ?_
  intro k hk
  exact project_coeff_sq_le (G := G) (n := n) (u := u) k

lemma project_apply_inHminus (𝒩 : CubicNemytskii) (n : ℕ)
    {R : ℝ} {u : DirichletSeq}
    (hH1 : ℓ2ZD.InH1Ball R u) :
    ℓ2ZD.InHminusBall (𝒩.bound R) (G.project n (𝒩.apply u)) := by
  have hminus := 𝒩.image_inHminus hH1
  exact project_inHminus (G := G) (n := n) hminus

lemma lipschitz_support (𝒩 : CubicNemytskii) {R : ℝ}
    {u v : DirichletSeq} (hu : ℓ2ZD.InH1Ball R u)
    (hv : ℓ2ZD.InH1Ball R v) (n : ℕ) :
    Finset.sum (G.support n)
        (fun k => ℓ2ZD.hminusWeight k *
          ‖(G.project n (𝒩.apply u)).a k
                - (G.project n (𝒩.apply v)).a k‖^2)
      ≤ (𝒩.bound R) *
        Finset.sum (G.support n)
          (fun k => ℓ2ZD.h1Weight k * ‖u.a k - v.a k‖^2) := by
  simpa [sum_support_project_diff_hminus (G := G) (n := n)
        (u := 𝒩.apply u) (v := 𝒩.apply v),
      sum_support_project_diff_h1 (G := G) (n := n) (u := u) (v := v)]
    using 𝒩.lipschitz_on_ball hu hv (G.support n)

end GalerkinSystem

/-- Canonical Galerkin chain: keep modes in `cube 1 (n+1)`. -/
def canonicalGalerkin : GalerkinSystem where
  level := fun n => n.succ
  level_mono := by
    intro n m hnm
    exact Nat.succ_le_succ hnm
  level_pos := fun n => Nat.succ_pos _

end

end SemilinearHeat
