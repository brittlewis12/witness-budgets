# Week 0 Day 1: Classical Banach Proof Analysis

**Date:** 2025-10-25
**File:** `Mathlib.Topology.MetricSpace.Contracting` (320 lines)
**Target theorem:** `exists_fixedPoint` (lines 90-99) and `fixedPoint` (line 269)

---

## Key Observations

### 1. Proof Structure (Classical Version)

**Main existence theorem (lines 90-99):**
```lean
theorem exists_fixedPoint (hf : ContractingWith K f) (x : α) (hx : edist x (f x) ≠ ∞) :
    ∃ y, IsFixedPt f y ∧ Tendsto (fun n ↦ f^[n] x) atTop (𝓝 y) ∧
      ∀ n : ℕ, edist (f^[n] x) y ≤ edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K)
```

**Key features:**
- Uses `CauchySeq` to prove convergence (line 93-94)
- Relies on `cauchySeq_tendsto_of_complete` to get limit point (line 96)
- **Already has explicit rate:** `edist (f^[n] x) y ≤ edist x (f x) * K^n / (1 - K)` (line 92)
- Returns existential (`∃ y`) not a concrete witness

**Classical choice usage (lines 106-107, 269-270):**
```lean
noncomputable def efixedPoint (hf : ContractingWith K f) (x : α) (hx : edist x (f x) ≠ ∞) : α :=
  Classical.choose <| hf.exists_fixedPoint x hx

noncomputable def fixedPoint : α :=
  efixedPoint f hf _ (edist_ne_top (Classical.choice ‹Nonempty α›) _)
```

**This is the classical witness extraction** - turns `∃ y` into concrete `y` via `Classical.choose`.

### 2. Dependencies

**Imports (lines 6-9):**
1. `Mathlib.Analysis.SpecificLimits.Basic` - limit theorems
2. `Mathlib.Data.Setoid.Basic` - setoid (equivalence relations)
3. `Mathlib.Dynamics.FixedPoints.Topology` - fixed point definitions
4. `Mathlib.Topology.MetricSpace.Lipschitz` - Lipschitz continuity

**Key typeclasses used:**
- `EMetricSpace α` (extended metric space)
- `CompleteSpace α` (Cauchy sequences converge)
- `MetricSpace α` (for the non-extended version)

### 3. Budget Analysis Prediction

**Where classical axioms appear:**

1. **`Classical.choose`** (lines 107, 168): Used to extract witness from existential
   - This will trigger **C5 (full choice)** in vBudget
   - Appears in Type position → will also trigger xBudget

2. **`Classical.choice`** (line 270): Used to get initial point from `Nonempty α`
   - Also C5

**Expected budgets:**
- **vBudget:** C5 (uses Classical.choose and Classical.choice)
- **xBudget:** C5 (classical choice appears in Type-level definitions: `efixedPoint` and `fixedPoint`)

**The constructive core is already there!**
The proof of `exists_fixedPoint` (lines 93-99) is essentially constructive:
- Uses Cauchy sequences (constructive)
- Uses geometric series convergence (constructive)
- Has explicit rate formula (constructive)

**What makes it classical:**
Only the witness extraction (`Classical.choose`) makes it non-constructive. The existence proof itself is fine!

### 4. Proof Technique

**The proof works by:**
1. Show `f^[n] x` is Cauchy using geometric convergence (line 93-94)
2. Use completeness to get limit `y` (line 96)
3. Show `y` is a fixed point via continuity (line 97)
4. Prove convergence rate bound (line 98-99)

**This is exactly the iterative construction we want for C0!**

### 5. Explicit Rate Formula (Already Present!)

**A priori estimate (line 92):**
```
edist (f^[n] x) y ≤ edist x (f x) * K^n / (1 - K)
```

**This directly gives us N(ε):**
```
N(ε) = ⌈log(d(x₁,x₀) / ((1-K)ε)) / log(1/K)⌉
```

Setting `edist x (f x) * K^n / (1 - K) ≤ ε` and solving for `n`.

**Mathlib already has the math!** We just need to:
1. Remove `Classical.choose`
2. Return the limit directly as a computable witness
3. Package the iteration count formula

### 6. Line Count Analysis

**Total file:** 320 lines

**Main theorem breakdown:**
- `exists_fixedPoint`: 10 lines (lines 90-99)
- `efixedPoint` definition: 2 lines (106-107)
- `fixedPoint` definition: 2 lines (269-270)
- Supporting lemmas: ~50 lines for uniqueness, estimates, convergence

**Core proof is compact!** Most of the file is:
- Infrastructure (ContractingWith definition, lemmas)
- Extended metric space version
- Restricted domain version
- API lemmas

### 7. Verification Time & Budget Measurement

**Measured via `./scripts/baseline_module.sh`:**
- **Wall-clock time:** 2:59.34 (179.21s total)
- **Declarations analyzed:** 43

**Budget results (validates Week 0 findings!):**

```
vBudget distribution:
  C0:   1 ( 2.3%)
  C5:  42 (97.7%)

xBudget distribution:
  C0:  41 (95.3%)
  C5:   2 ( 4.7%)
```

**Key finding:** 97.7% vBudget C5 but 95.3% xBudget C0!

**Declarations with xBudget C5 (only 2):**
1. `ContractingWith.efixedPoint` - uses `Classical.choose` to extract witness
2. `ContractingWith` - the namespace/definition itself

**All other theorems have xBudget C0!** Including:
- `exists_fixedPoint` (the existence theorem)
- `fixedPoint` (references `efixedPoint` but doesn't expose choice in type)
- All the convergence rate theorems
- All the uniqueness theorems

**This perfectly demonstrates the vBudget/xBudget separation:**
- Classical reasoning appears throughout (vBudget C5)
- But is confined to `Prop` and doesn't leak into computational types (xBudget C0)
- Only the witness extraction functions (`efixedPoint`) have extractable classical debt

### 8. Constructive Opportunity Analysis

**What needs to change for C0:**

1. **Remove `Classical.choose`:**
   - Don't use `Classical.choose` to extract from `∃ y`
   - Return the limit directly as a Σ-type: `{y : α // IsFixedPt f y}`

2. **Make completeness constructive:**
   - Instead of `CompleteSpace α` (abstract convergence)
   - Use explicit Cauchy modulus or constructive completeness

3. **The core proof is already constructive!**
   - Lines 93-99 build Cauchy sequence iteratively
   - Lines 92 give explicit convergence rate
   - Convergence uses geometric series (computable)

**What we gain:**
- Iteration function that computes fixed point to tolerance ε
- Explicit N(ε) = ⌈log(...)/log(1/K)⌉
- Extractable algorithm (currently blocked by `Classical.choose`)

**Estimated complexity:**
- **Classical version:** 10 lines (core theorem)
- **Constructive version:** ~20-30 lines (need to:
  - Define Σ-type return
  - Explicit Cauchy construction
  - Iteration count computation
  - Avoid `Classical.choose`)

**Trade-off:** More explicit in construction, but yields executable content.

### 9. Comparative Analysis Summary

| Aspect | Classical (Mathlib) | Constructive (Planned) |
|--------|---------------------|------------------------|
| **Lines of proof** | ~10 (core theorem) | ~20-30 (estimated) |
| **vBudget** | C5 (uses classical in proofs) | C0 (no classical axioms) |
| **xBudget** | C0 for theorems, C5 for `efixedPoint` | C0 (fully extractable) |
| **Verification time** | 179s (43 declarations) | TBD |
| **Dependencies** | Analysis, Dynamics, Topology | Will reuse MetricSpace |
| **Witness extraction** | `Classical.choose` | Direct Σ-type |
| **Convergence rate** | ✅ Already explicit | ✅ Will preserve |
| **Extractable?** | ❌ No (uses choice) | ✅ Yes (goal) |

### 10. Next Steps (Week 0 Day 2)

**Tomorrow's tasks:**
1. Define constructive scope:
   - Metric space: use `MetricSpace` with constructive completeness
   - Contraction record: `f`, `K < 1`, decidable distance
   - Return type: `{x : X // f x = x}` + iteration count certificate

2. Draft comparison template:
   - Side-by-side proof structure
   - Line count tracking
   - Budget tracking protocol
   - Verification time measurement

3. Identify extraction target:
   - Decide: Lean native (`lake exe`) vs external
   - Define CLI harness specification
   - Test suite structure (6 cases from plan)

**Key insight from today:** Mathlib's Banach proof is 95% extractable already! The only barrier is `Classical.choose` in 2/43 declarations. Our constructive version should achieve similar structure but with xBudget C0 throughout.

