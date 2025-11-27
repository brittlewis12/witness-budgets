import Mathlib
import Budgets.SemilinearHeat.Spaces

/-!
# Semilinear Heat PDE (1D) – Dirichlet bilinear helpers

This module introduces purely algebraic quantities for the Dirichlet stiffness
form (a weighted sum over the ℤ-lattice) that will later be used to formulate
the Galerkin energy estimates.  Everything is expressed in the `SeqD` model,
so the lemmas amount to straightforward inequalities between the lattice
weights already present in the QRK/QAL stack.
-/

open scoped BigOperators
open Finset
open Fin

namespace SemilinearHeat

open RellichKondrachovInterval AubinLions Complex

noncomputable section

variable {F : Finset (ℓ2ZD.Lattice spatialDim)}

/-- Frequency readback for `d = 1`: there is only one axis, so the frequency is
just the integer stored at index `0`. -/
@[simp] def dirichletFreq (k : ℓ2ZD.Lattice spatialDim) : ℤ := k 0

@[simp] lemma dirichletFreq_cast (k : ℓ2ZD.Lattice spatialDim) :
    ((dirichletFreq k : ℤ) : ℝ) = (k 0 : ℝ) := rfl

/-- Laplacian weight |k|²·π² that captures the Dirichlet stiffness when the
odd extension is expressed in the ℓ² lattice model. -/
def laplacianWeight (k : ℓ2ZD.Lattice spatialDim) : ℝ :=
  Real.pi^2 * ((dirichletFreq k : ℝ)^2)

lemma laplacianWeight_nonneg (k : ℓ2ZD.Lattice spatialDim) :
    0 ≤ laplacianWeight k := by
  have hpi : 0 ≤ Real.pi^2 := by exact sq_nonneg Real.pi
  have hf : 0 ≤ (dirichletFreq k : ℝ)^2 := sq_nonneg _
  exact mul_nonneg hpi hf

lemma normSq_one_dim (k : ℓ2ZD.Lattice spatialDim) :
    ℓ2ZD.normSq (d := spatialDim) k = ((dirichletFreq k : ℤ) : ℝ)^2 := by
  classical
  simp [ℓ2ZD.normSq, dirichletFreq]

lemma laplacianWeight_le_h1Weight (k : ℓ2ZD.Lattice spatialDim) :
    laplacianWeight k ≤ ℓ2ZD.h1Weight k := by
  classical
  have hfreq : 0 ≤ (dirichletFreq k : ℝ)^2 := sq_nonneg _
  have hposTerm : 0 ≤ 1 + 3 * Real.pi^2 * (dirichletFreq k : ℝ)^2 :=
    add_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
      (mul_nonneg (by positivity : 0 ≤ 3 * Real.pi^2) hfreq)
  set t := ((dirichletFreq k : ℤ) : ℝ)^2
  have hx : 4 * Real.pi^2 * t - Real.pi^2 * t = 3 * Real.pi^2 * t := by
    ring
  have hrepr : ℓ2ZD.h1Weight k - laplacianWeight k
      = 1 + 3 * Real.pi^2 * (dirichletFreq k : ℝ)^2 := by
    have hx' := congrArg (fun s : ℝ => 1 + s) hx
    simpa [ℓ2ZD.h1Weight, laplacianWeight, normSq_one_dim, t,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm,
      mul_left_comm, mul_assoc] using hx'
  have hdiff_nonneg : 0 ≤ ℓ2ZD.h1Weight k - laplacianWeight k := by
    simpa [hrepr, normSq_one_dim] using hposTerm
  exact sub_nonneg.mp hdiff_nonneg

@[simp] lemma abs_laplacianWeight (k : ℓ2ZD.Lattice spatialDim) :
    |laplacianWeight k| = laplacianWeight k :=
  abs_of_nonneg (laplacianWeight_nonneg k)

/-- Weighted inequality ensuring the Laplacian multiplier sends H¹ to H⁻¹. -/
lemma laplacian_weight_bound (k : ℓ2ZD.Lattice spatialDim) :
    ℓ2ZD.hminusWeight k * (laplacianWeight k)^2 ≤ ℓ2ZD.h1Weight k := by
  classical
  have hpos : 0 < ℓ2ZD.h1Weight k := ℓ2ZD.h1Weight_pos (d := spatialDim) k
  have hineq := laplacianWeight_le_h1Weight k
  have hnonnegH : 0 ≤ ℓ2ZD.h1Weight k := le_of_lt hpos
  have hsq : (laplacianWeight k)^2 ≤ (ℓ2ZD.h1Weight k)^2 := by
    have habs :
        |laplacianWeight k| ≤ |ℓ2ZD.h1Weight k| := by
      simpa [abs_laplacianWeight, abs_of_nonneg hnonnegH] using hineq
    exact (sq_le_sq.mpr habs)
  have hnonneg_inv : 0 ≤ (ℓ2ZD.h1Weight k)⁻¹ :=
    inv_nonneg.mpr hnonnegH
  have hineq' := mul_le_mul_of_nonneg_left hsq hnonneg_inv
  have hpos_ne : ℓ2ZD.h1Weight k ≠ 0 := ne_of_gt hpos
  have hleft :
      (ℓ2ZD.h1Weight k)⁻¹ * (laplacianWeight k)^2
        = ℓ2ZD.hminusWeight k * (laplacianWeight k)^2 := by
    simp [ℓ2ZD.hminusWeight, mul_comm]
  have hright :
      (ℓ2ZD.h1Weight k)⁻¹ * (ℓ2ZD.h1Weight k)^2
        = ℓ2ZD.h1Weight k := by
    have hpos_ne : ℓ2ZD.h1Weight k ≠ 0 := ne_of_gt hpos
    simp [pow_two, hpos_ne]
  simpa [hleft, hright] using hineq'

/-- Dirichlet stiffness computed over a finite frequency window. -/
def gradEnergyOn (F : Finset (ℓ2ZD.Lattice spatialDim))
    (u : DirichletSeq) : ℝ :=
  Finset.sum F (fun k => laplacianWeight k * ‖u.a k‖^2)

/-- ℓ²-energy restricted to a finite frequency set. -/
def massEnergyOn (F : Finset (ℓ2ZD.Lattice spatialDim))
    (u : DirichletSeq) : ℝ :=
  Finset.sum F (fun k => ‖u.a k‖^2)

lemma massEnergyOn_nonneg (F : Finset (ℓ2ZD.Lattice spatialDim))
    (u : DirichletSeq) : 0 ≤ massEnergyOn F u := by
  unfold massEnergyOn
  refine Finset.sum_nonneg ?_
  intro k hk
  exact sq_nonneg _

lemma laplacian_norm_sq (k : ℓ2ZD.Lattice spatialDim) (x : ℂ) :
    ‖laplacianWeight k * x‖^2 = (laplacianWeight k)^2 * ‖x‖^2 := by
  have hnorm : ‖(laplacianWeight k : ℂ)‖ = laplacianWeight k := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_laplacianWeight]
  calc
    ‖laplacianWeight k * x‖^2
        = (‖(laplacianWeight k : ℂ)‖ * ‖x‖)^2 := by simp
    _ = (laplacianWeight k)^2 * ‖x‖^2 := by
      simp [pow_two, mul_comm, mul_left_comm, mul_assoc]

lemma laplacian_coeff_bound (u : H1Seq)
    (k : ℓ2ZD.Lattice spatialDim) :
    ℓ2ZD.hminusWeight k * ‖(laplacianWeight k : ℂ) * u.coeff k‖^2
      ≤ ℓ2ZD.h1Weight k * ‖u.coeff k‖^2 := by
  have hcoeff : 0 ≤ ‖u.coeff k‖^2 := sq_nonneg _
  have hineq := laplacian_weight_bound k
  have hbound := mul_le_mul_of_nonneg_right hineq hcoeff
  have hnorm := laplacian_norm_sq k (u.coeff k)
  calc
    ℓ2ZD.hminusWeight k * ‖(laplacianWeight k : ℂ) * u.coeff k‖^2
        = ℓ2ZD.hminusWeight k *
            ((laplacianWeight k)^2 * ‖u.coeff k‖^2) := by
              simpa [H1Seq.coeff] using congrArg (fun t => ℓ2ZD.hminusWeight k * t) hnorm
    _ = (ℓ2ZD.hminusWeight k * (laplacianWeight k)^2) * ‖u.coeff k‖^2 := by
          simp [pow_two, H1Seq.coeff, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ ℓ2ZD.h1Weight k * ‖u.coeff k‖^2 := by
          simpa [H1Seq.coeff, mul_comm, mul_left_comm, mul_assoc] using hbound

lemma gradEnergyOn_nonneg (F : Finset (ℓ2ZD.Lattice spatialDim))
    (u : DirichletSeq) : 0 ≤ gradEnergyOn F u := by
  classical
  apply Finset.sum_nonneg
  intro k hk
  have hcoeff : 0 ≤ ‖u.a k‖^2 := sq_nonneg _
  exact mul_nonneg (laplacianWeight_nonneg k) hcoeff

lemma gradEnergyOn_le_h1 (F : Finset (ℓ2ZD.Lattice spatialDim))
    (u : DirichletSeq) :
    gradEnergyOn F u ≤
      Finset.sum F (fun k => ℓ2ZD.h1Weight k * ‖u.a k‖^2) := by
  classical
  refine Finset.sum_le_sum ?_
  intro k hk
  have hcoeff : 0 ≤ ‖u.a k‖^2 := sq_nonneg _
  have := laplacianWeight_le_h1Weight k
  exact mul_le_mul_of_nonneg_right this hcoeff

lemma gradEnergyOn_le_ball {R : ℝ} (u : DirichletSeq)
    (hH1 : ℓ2ZD.InH1Ball R u) :
    gradEnergyOn F u ≤ R^2 :=
  (gradEnergyOn_le_h1 (F := F) (u := u)).trans (hH1 F)

/-- Laplacian applied to an H¹ sequence, valued in H⁻¹. -/
noncomputable def laplacianApply (u : H1Seq) : Hminus1Seq :=
{ coeff := fun k => laplacianWeight k * u.coeff k,
  summable_hminus := by
    classical
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
        (H1Seq.summable_h1_coeff u)
    · have : 0 ≤ ℓ2ZD.hminusWeight k := ℓ2ZD.hminusWeight_nonneg (d := spatialDim) k
      exact mul_nonneg this (sq_nonneg _)
    · simpa [H1Seq.coeff] using laplacian_coeff_bound u k }

@[simp] lemma laplacianApply_coeff (u : H1Seq)
    (k : ℓ2ZD.Lattice spatialDim) :
    (laplacianApply u).coeff k = laplacianWeight k * u.coeff k := rfl

lemma laplacian_energy_le (u : H1Seq)
    (F : Finset (ℓ2ZD.Lattice spatialDim)) :
    Finset.sum F (fun k => ℓ2ZD.hminusWeight k *
        ‖(laplacianApply u).coeff k‖^2)
      ≤ Finset.sum F (fun k => ℓ2ZD.h1Weight k * ‖u.coeff k‖^2) := by
  classical
  refine Finset.sum_le_sum ?_
  intro k hk
  have := laplacian_coeff_bound u k
  simpa [laplacianApply_coeff, H1Seq.coeff] using this

lemma laplacian_pointwise_bound (u : H1Seq)
    (k : ℓ2ZD.Lattice spatialDim) :
    ℓ2ZD.hminusWeight k * ‖(laplacianApply u).coeff k‖^2
      ≤ ℓ2ZD.h1Weight k * ‖u.coeff k‖^2 := by
  have := laplacian_coeff_bound u k
  simpa [laplacianApply_coeff, H1Seq.coeff] using this

lemma laplacian_tsum_le (u : H1Seq) :
    (∑' k, ℓ2ZD.hminusWeight k * ‖(laplacianApply u).coeff k‖^2)
      ≤ ∑' k, ℓ2ZD.h1Weight k * ‖u.coeff k‖^2 := by
  classical
  have hleft := (Hminus1Seq.summable_hminus_coeff (laplacianApply u))
  have hright := H1Seq.summable_h1_coeff u
  exact
    Summable.tsum_le_tsum (by intro k; exact laplacian_pointwise_bound u k)
      hleft hright

end

end SemilinearHeat
