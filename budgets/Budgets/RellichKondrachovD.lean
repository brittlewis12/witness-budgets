import Budgets.RellichKondrachovD.Core
import Budgets.RellichKondrachovD.TailBound
import Budgets.RellichKondrachovD.Rounding
import Budgets.RellichKondrachovD.Soundness
import Budgets.RellichKondrachovD.L2Bridge

/-
! Rellich–Kondrachov in arbitrary dimension

This convenience module re-exports the files that make up the dimension-generic
constructive Rellich–Kondrachov theorem:

* `Core` : lattice/sequence setup and witness constructors.
* `TailBound` : the dimension-free spectral estimate.
* `Rounding` : discretisation bounds for the coefficients.
* `Soundness` : the constructive compactness theorem.
* `L2Bridge` : the Fourier bridge linking the ℓ² and L² worlds.
-/
