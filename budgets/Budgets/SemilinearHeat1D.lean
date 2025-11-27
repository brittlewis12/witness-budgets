import Budgets.SemilinearHeat.Spaces
import Budgets.SemilinearHeat.SobolevSeq
import Budgets.SemilinearHeat.Operator
import Budgets.SemilinearHeat.Nonlinearity
import Budgets.SemilinearHeat.Galerkin
import Budgets.SemilinearHeat.BilinearForm
import Budgets.SemilinearHeat.CubicConvolution
import Budgets.SemilinearHeat.SobolevEmbedding
import Budgets.SemilinearHeat.Witness

/-!
# Semilinear Heat Equation (1D)

This module provides infrastructure for the semilinear heat PDE on (0,1):
  ∂ₜu - Δu = u³   on (0,1) × (0,T)
  u(0,t) = u(1,t) = 0  (Dirichlet boundary conditions)

## Main Components

- **Spaces**: Domain, measure, and Sobolev space definitions
- **SobolevSeq**: Sequence models for H¹, L², H⁻¹ spaces
- **Operator**: Dirichlet Laplacian and energy functionals
- **Nonlinearity**: Abstract interface for cubic Nemytskii operator
- **BilinearForm**: Inner products, duality pairings, Dirichlet bilinear form
- **CubicConvolution**: Concrete implementation of u³ via Fourier convolution
- **Galerkin**: Spectral projection and finite-dimensional approximations

## Extraction Strategy

Following the proven dual-track architecture from QRK/QAL:
- **Proof track**: Uses Complex/Real arithmetic (vbudget C5, xbudget C5)
- **Extraction track**: Rational variant via SeqD_Rat (xbudget C0)
- **Firewall**: Soundness theorems connect the tracks

## Usage

```lean
import Budgets.SemilinearHeat1D

-- Access submodules via namespace
open SemilinearHeat

-- Define test data
def u₀ : DirichletSeq := ...

-- Apply operators
def u_evolved := cubicApply u₀ ...
```
-/
