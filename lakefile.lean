import Lake
open Lake DSL

package «witness-budgets» where
  version := v!"0.1.0"
  keywords := #["lean", "verification", "constructive", "witness-budgets"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-print `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ]

require std from git
  "https://github.com/leanprover/std4" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib «WBudget» where
  srcDir := "wbudget"

lean_lib «Tests» where
  srcDir := "tests"

@[default_target]
lean_lib «Budgets» where
  srcDir := "budgets"

-- CLI executable for wbudget analyzer
@[default_target]
lean_exe wbudget where
  root := `Main
  srcDir := "scripts"

-- Banach fixed-point extraction demo
lean_exe banach_demo where
  root := `BanachDemo
  srcDir := "tests"

-- Newton-Kantorovich extraction demo
lean_exe newton_demo where
  root := `NewtonDemo
  srcDir := "tests"

-- Markov chain extraction demo
lean_exe markov_demo where
  root := `MarkovDemo
  srcDir := "tests"

-- Rellich-Kondrachov 1D extraction demo
lean_exe qrk1d_demo where
  root := `QRK1DDemo
  srcDir := "tests"

-- Rellich-Kondrachov 2D extraction demo
lean_exe qrk2d_demo where
  root := `QRK2DDemo
  srcDir := "tests"

-- Rellich-Kondrachov 3D extraction demo
lean_exe qrk3d_demo where
  root := `QRK3DDemo
  srcDir := "tests"

-- Rellich-Kondrachov D (dimension-generic) extraction demo
lean_exe qrkd_demo where
  root := `QRKDDemo
  srcDir := "tests"

-- Quantitative Aubin-Lions extraction demo
lean_exe qal_demo where
  root := `QALDemo
  srcDir := "tests"

-- Interval arithmetic semilinear heat 1D PDE demo
lean_exe heat_demo_interval where
  root := `HeatDemoInterval
  srcDir := "tests"

-- FFT extraction demo
lean_exe fft_demo where
  root := `FFTDemo
  srcDir := "tests"

-- Multi-dimensional FFT test
lean_exe fft_multidim_test where
  root := `FFTMultiDimTest
  srcDir := "tests"

-- Spectral ops validation (compare vs direct method)
lean_exe spectral_validation where
  root := `SpectralValidation
  srcDir := "tests"

lean_exe fft_comprehensive_test where
  root := `FFTComprehensiveTest
  srcDir := "tests"
