import Budgets.SemilinearHeat.Spaces

/-!
# Semilinear Heat PDE (1D) – Formal cubic Nemytskii interface

To keep the Galerkin/QAL pipeline modular we isolate the analytic requirements
for the cubic nonlinearity `u ↦ u^3` into a single structure.  The fields encode
exactly the quantitative control we will need later (H⁻¹ bounds and Lipschitz
behaviour on bounded H¹ sets).  A future file will provide the actual
instantiation via sine-series / interval analysis; for now, downstream modules
can work abstractly with any instance of `CubicNemytskii`.
-/

namespace SemilinearHeat

open RellichKondrachovInterval AubinLions

noncomputable section

/-- Quantitative interface for the cubic Nemytskii map on Dirichlet sequences.

* `apply` is the actual map `u ↦ u^3` (to be instantiated later).
* `bound` assigns an H⁻¹ radius to each H¹ bound.
* `bound_nonneg` ensures the radius is well-defined.
* `map_inHminus` packages the radius transfer: if `u` lies in the H¹ ball of
  radius `R`, then `apply u` lies in the H⁻¹ ball of radius `bound R`.
* `lipschitz` captures the continuity of the Nemytskii map on bounded H¹ sets
  in the weighted ℓ² metric used throughout QRK/QAL.
-/
structure CubicNemytskii : Type where
  apply : DirichletSeq → DirichletSeq
  bound : ℝ → ℝ
  bound_nonneg : ∀ R, 0 ≤ bound R
  map_inHminus : ∀ {R : ℝ} {u : DirichletSeq},
      ℓ2ZD.InH1Ball R u → ℓ2ZD.InHminusBall (bound R) (apply u)
  lipschitz : ∀ {R : ℝ} {u v : DirichletSeq},
      ℓ2ZD.InH1Ball R u → ℓ2ZD.InH1Ball R v →
      ∀ (F : Finset (ℓ2ZD.Lattice spatialDim)),
        Finset.sum F (fun k => ℓ2ZD.hminusWeight k *
          ‖(apply u).a k - (apply v).a k‖^2)
          ≤ (bound R) *
            Finset.sum F (fun k => ℓ2ZD.h1Weight k * ‖u.a k - v.a k‖^2)

namespace CubicNemytskii

variable {𝒩 : CubicNemytskii}

/-- The image of an H¹-bounded sequence automatically lies in the prescribed
H⁻¹ ball. -/
lemma image_inHminus {R : ℝ} {u : DirichletSeq}
    (hH1 : ℓ2ZD.InH1Ball R u) :
    ℓ2ZD.InHminusBall (𝒩.bound R) (𝒩.apply u) :=
  𝒩.map_inHminus hH1

lemma lipschitz_on_ball {R : ℝ} {u v : DirichletSeq}
    (hu : ℓ2ZD.InH1Ball R u) (hv : ℓ2ZD.InH1Ball R v)
    (F : Finset (ℓ2ZD.Lattice spatialDim)) :
    Finset.sum F (fun k => ℓ2ZD.hminusWeight k *
        ‖(𝒩.apply u).a k - (𝒩.apply v).a k‖^2)
      ≤ (𝒩.bound R) *
        Finset.sum F (fun k => ℓ2ZD.h1Weight k * ‖u.a k - v.a k‖^2) :=
  𝒩.lipschitz hu hv F

lemma bound_nonneg' (R : ℝ) : 0 ≤ 𝒩.bound R :=
  𝒩.bound_nonneg R

end CubicNemytskii

end

end SemilinearHeat
