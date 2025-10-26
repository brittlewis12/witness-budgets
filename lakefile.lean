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

lean_lib «Budgets» where
  srcDir := "budgets"

-- CLI executable for wbudget analyzer
lean_exe wbudget where
  root := `Main
  srcDir := "scripts"

-- Banach fixed-point extraction demo
lean_exe banach_demo where
  root := `BanachDemo
  srcDir := "tests"
