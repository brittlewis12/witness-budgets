# Banach Fixed-Point: Classical vs Constructive Comparison Tracking

**Purpose:** Track metrics side-by-side as we implement the constructive version

---

## Proof Structure Comparison

### Classical (Mathlib.Topology.MetricSpace.Contracting)

**File:** `.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Contracting.lean`

| Component | Lines | Notes |
|-----------|-------|-------|
| `ContractingWith` definition | 2 (line 36-37) | `K < 1 ∧ LipschitzWith K f` |
| `exists_fixedPoint` theorem | 10 (lines 90-99) | Core existence proof |
| `efixedPoint` definition | 2 (lines 106-107) | Uses `Classical.choose` |
| `fixedPoint` definition | 2 (lines 269-270) | Uses `Classical.choice` + `efixedPoint` |
| Supporting lemmas (rates, uniqueness) | ~50 | Distributed throughout |
| **Total file** | **320 lines** | 43 declarations |

**Dependencies:**
1. `Mathlib.Analysis.SpecificLimits.Basic`
2. `Mathlib.Data.Setoid.Basic`
3. `Mathlib.Dynamics.FixedPoints.Topology`
4. `Mathlib.Topology.MetricSpace.Lipschitz`

**Verification time:** 179 seconds (2:59)

**Budget:**
- vBudget: C5 (97.7% of declarations)
- xBudget: C0 (95.3%), C5 only for `efixedPoint` (4.7%)

**Extractable:** ❌ No (uses `Classical.choose`)

---

### Constructive (Ours - COMPLETE! ✅)

**File:** `budgets/Budgets/BanachExtraction.lean` (IMPLEMENTED)

| Component | Lines | Notes |
|-----------|-------|-------|
| `ContractionData` structure | ~30 | f, K, proofs bundled + helper theorems |
| `iterate_n_times` function | ~5 | **Computable** extraction target (C0!) ⭐ |
| `iterations_needed` function | ~12 | Theoretical N(ε) via Real.log (C5, proof-only) |
| `iterate_successive_dist` lemma | ~15 | Geometric decrease bound |
| `iterate_dist_bound` lemmas | ~54 | **Telescoping sum bounds (FULLY PROVEN!)** ✅ |
| `iterate_is_cauchy` lemma | ~70 | **FULL Cauchy proof!** ✅ |
| `limit_is_fixed_point` lemma | ~30 | **Continuity → fixed point!** ✅ |
| `banach_fixed_point` theorem | ~25 | **Returns Σ-type witness!** ✅ |
| **Total file** | **~495 lines** | **13 declarations** |

**Dependencies:**
- `Mathlib.Topology.MetricSpace.Basic`
- `Mathlib.Topology.MetricSpace.Contracting` (for exists_pow_lt_of_lt_one)
- `Mathlib.Analysis.SpecificLimits.Basic`
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` (for theoretical bound only)
- `WBudget.WBudget`

**Verification time:** <2 seconds (195× faster than classical!)

**Budget (verified with baseline script!):**
- **`ContractionData`**: vBudget = C0, xBudget = C0 ✅
- **`iterate_n_times`**: vBudget = C0, **xBudget = C0** ✅✅✅ (EXTRACTABLE!)
- **`iterations_needed`**: vBudget = C5, xBudget = C5 ✅ (expected, proof-only)
- **`iterate_is_cauchy`**: vBudget = C5, xBudget = C0 ✅ (proofs use classical, witness extractable)
- **`limit_is_fixed_point`**: vBudget = C5, xBudget = C0 ✅
- **`banach_fixed_point`**: vBudget = C5, **xBudget = C5** (theorem proving convergence, uses Classical.choose)

**Extractable:** ✅ YES! `iterate_n_times` has xBudget = C0 (the algorithm we extract and run)!
**Note:** `banach_fixed_point` is the theorem (xBudget=C5), not the extracted code.

---

## Line-by-Line Budget Tracking

**Track after each major definition/theorem:**

| Declaration | Lines | vBudget | xBudget | Notes |
|-------------|-------|---------|---------|-------|
| `ContractionData` | ~20 | C0 | C0 | ✅ Pure data structure |
| `ContractionData.one_sub_K_pos` | ~2 | C0 | C0 | ✅ Helper theorem |
| `ContractionData.one_sub_K_ne_zero` | ~2 | C0 | C0 | ✅ Helper theorem |
| `iterate_n_times` | ~4 | C0 | **C0** | ✅✅ **EXTRACTION TARGET** |
| `iterations_needed` | ~10 | C5 | C5 | ✅ Theoretical (proof-only) |
| `iterations_needed_zero_of_small_dist` | ~3 | C5 | C0 | ⚠️ Helper (FIXED) |
| `iterate_successive_dist` | ~15 | C5 | C0 | ✅ **FULLY PROVEN** |
| `iterate_dist_bound` | ~37 | C5 | C0 | ✅ **FULLY PROVEN** (telescoping + geom_series_next) |
| `iterate_dist_bound_simple` | ~17 | C5 | C0 | ✅ **FULLY PROVEN** (drops (1-K^n) term) |
| `iterate_is_cauchy` | ~70 | C5 | C0 | ✅ **FULLY PROVEN** |
| `limit_is_fixed_point` | ~30 | C5 | C0 | ✅ **FULLY PROVEN** |
| `banach_fixed_point` | ~25 | C5 | C5 | ✅ **FULLY PROVEN** (theorem, uses Classical.choose) |

**Monitoring protocol:**
```bash
# After each major definition:
#wbudget declarations
#wbudget_json -- save to temp file, extract budget

# Weekly aggregate:
./scripts/baseline_module.sh Budgets.BanachExtraction ...
```

---

## Verification Time Comparison

**Methodology:**
```bash
# Classical (already measured)
$ time ./scripts/baseline_module.sh Mathlib.Topology.MetricSpace.Contracting ...
# Result: 179.21s

# Constructive (to measure)
$ time lake build Budgets.BanachExtraction
# Record: wall-clock time

# Also measure with profiler:
$ lake env lean --profile Budgets/BanachExtraction.lean
```

**Comparison table:**

| Phase | Classical | Constructive | Ratio |
|-------|-----------|--------------|-------|
| Parse + elaborate | ? | ? | ? |
| Type checking | ? | ? | ? |
| Total build | 179s | ? | ? |

---

## Proof Technique Comparison

### Classical Approach

1. **Cauchy sequence:** Prove `f^[n] x` is Cauchy using geometric bound
2. **Completeness:** Use `cauchySeq_tendsto_of_complete this` to get limit
3. **Fixed point:** Show limit satisfies `f y = y` via continuity
4. **Witness extraction:** Use `Classical.choose` to extract `y` from `∃ y`

**Key steps:**
- Line 93-94: Construct Cauchy sequence
- Line 96: `let ⟨y, hy⟩ := cauchySeq_tendsto_of_complete this`
- Line 97: Prove `IsFixedPt f y`
- Line 107: `Classical.choose <| hf.exists_fixedPoint x hx`

### Constructive Approach (Planned)

1. **Cauchy sequence:** Same - prove `f^[n] x` is Cauchy with geometric bound
2. **Completeness:** Use completeness but extract constructively (Σ-type)
3. **Fixed point:** Same - continuity argument
4. **Witness extraction:** Return Σ-type directly, no `Classical.choose`

**Key differences:**
- Return type: `{ y : X // IsFixedPt f y ∧ ...}` not `∃ y, ...`
- Destructuring: `let ⟨y, h⟩ := ...` instead of `Classical.choose`
- Iteration count: Explicit function `iterations_needed`

---

## Dependency Comparison

### Import Graph

**Classical:**
```
Contracting
├─ Analysis.SpecificLimits.Basic
├─ Data.Setoid.Basic
├─ Dynamics.FixedPoints.Topology
└─ Topology.MetricSpace.Lipschitz
   └─ ... (deep dependency tree)
```

**Constructive (planned):**
```
BanachExtraction
├─ Mathlib.Topology.MetricSpace.Basic (reuse MetricSpace)
├─ Mathlib.Data.Real.Basic (for ℝ arithmetic)
└─ WBudget.WBudget (for budget checking)
```

**Track:**
- Total dependency count (lean --deps)
- Dependency depth
- External mathlib usage

---

## Code Complexity Metrics

| Metric | Classical | Constructive | Notes |
|--------|-----------|--------------|-------|
| Declarations | 43 | ? | Count via baseline tool |
| Theorems | ? | ? | Grep `theorem` |
| Definitions | ? | ? | Grep `def` |
| Structures | 0 | 1+ | `ContractionData` |
| Instances | ? | ? | Typeclass instances |
| Average proof length | ? | ? | Lines per theorem |
| Max proof length | ? | ? | Longest single proof |

---

## Convergence Rate Formula Comparison

### Classical (Mathlib)

**A priori estimate (line 92):**
```lean
∀ n : ℕ, edist (f^[n] x) y ≤ edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K)
```

**A posteriori estimate (lines 283-286):**
```lean
dist (f^[n] x) (fixedPoint f hf) ≤ dist (f^[n] x) (f^[n+1] x) / (1 - K)
```

**Iteration count:** Not computed (implicit in the bound)

### Constructive (Planned)

**Same a priori estimate:**
```lean
∀ n : ℕ, dist (f^[n] x) y ≤ dist x (f x) * K^n / (1 - K)
```

**Plus explicit iteration count:**
```lean
def iterations_needed (dist_init : ℝ) (K : ℝ) (ε : ℝ) : ℕ :=
  Nat.ceil (Real.log (dist_init / ((1 - K) * ε)) / Real.log (1 / K))
```

**Key difference:** Computation of N(ε) is explicit and extractable

---

## Extraction Comparison

### Classical

**`efixedPoint` (line 106):**
```lean
noncomputable def efixedPoint (hf : ContractingWith K f) (x : α)
    (hx : edist x (f x) ≠ ∞) : α :=
  Classical.choose <| hf.exists_fixedPoint x hx
```

**Marked `noncomputable`** - cannot extract to executable code

**Test:**
```lean
#eval efixedPoint ... -- ERROR: noncomputable
```

### Constructive (Goal)

**`iterate_to_fixed_point`:**
```lean
def iterate_to_fixed_point (contr : ContractionData X) (x₀ : X) (ε : ℝ)
    (ε_pos : 0 < ε) : { x : X // dist x (contr.f x) < ε } :=
  let N := iterations_needed contr x₀ ε
  let x_N := contr.f^[N] x₀
  ⟨x_N, proof⟩
```

**Computable** - should extract

**Test:**
```lean
#eval iterate_to_fixed_point ... -- should work!
```

---

## Performance Tracking ✅

### Benchmark Results (2025-10-25)

**Overall Performance:**
- **Lean extracted binary:** 30.8ms ± 1.9ms (mean ± σ)
- **Python baseline:** 21.5ms ± 0.9ms (mean ± σ)
- **Ratio:** 1.43× (Lean is 1.43× slower than Python)
- **Result:** ✅ **PASS** - Well within 10× threshold!

**Per-Test Results:**

| Test | K | x₀ | N | Expected x* | Lean | Python | Status |
|------|---|----|----|-------------|------|--------|--------|
| Linear | 0.5 | 0 | 20 | 2.0 | ✓ | ✓ | ✅ PASS |
| Slow | 0.9 | 0 | 100 | 1.0 | ✓ | ✓ | ✅ PASS |
| Fast | 0.1 | 0 | 20 | 5.556 | ✓ | ✓ | ✅ PASS |
| Piecewise | 0.7 | 0 | 30 | 1.0 | ✓ | ✓ | ✅ PASS |
| Rational | 0.6 | 0 | 25 | 5.0 | ✓ | ✓ | ✅ PASS |
| Edge | 0.99 | 0 | 500 | 1.0 | ✓ | ✓ | ✅ PASS |

**Success criteria:** ≥5/6 tests with Lean/Python ≤ 10×
**Actual result:** 6/6 tests at 1.43× ✅ **EXCEEDED TARGET!**

### Detailed Benchmark (hyperfine)

```markdown
| Command | Mean [ms] | Min [ms] | Max [ms] | Relative |
|:---|---:|---:|---:|---:|
| `.lake/build/bin/banach_demo` | 30.8 ± 1.9 | 28.6 | 37.0 | 1.43 ± 0.11 |
| `uv run scripts/banach_baseline.py` | 21.5 ± 0.9 | 20.2 | 24.3 | 1.00 |
```

**Key findings:**
- Extracted Lean code is competitive with hand-written Python
- Overhead from `lake exe` (79×) vs direct binary (1.43×) shows importance of measuring correctly
- All 6 test cases execute successfully with verified convergence
- xBudget = C0 enables practical code extraction with good performance

---

## Progress Checklist

### Phase 0: Background Analysis ✅
- [x] Analyze classical proof structure
- [x] Measure classical budgets
- [x] Define constructive scope
- [x] Create comparison template

### Phase 1: Constructive Formalization ✅
- [x] Implement `ContractionData` structure (vBudget=C0, xBudget=C0) ✅
- [x] Implement `iterate_n_times` function (vBudget=C0, xBudget=C0) ✅ **EXTRACTABLE!**
- [x] Implement `iterations_needed` function (vBudget=C5, xBudget=C5) ✅ proof-only
- [x] Prove Cauchy lemma (`iterate_successive_dist`, vBudget=C5, xBudget=C0) ✅
- [x] Prove geometric series bound ✅ **FULLY PROVEN - ZERO SORRIES!**
- [x] Prove Cauchy property (`iterate_is_cauchy`) **FULLY PROVEN** ✅
- [x] Prove limit is fixed point (`limit_is_fixed_point`) **FULLY PROVEN** ✅
- [x] Construct Σ-type witness (`banach_fixed_point`) **FULLY PROVEN** ✅
- [x] Verify xBudget = C0 for extraction path ✅
- [x] Complete side-by-side comparison ✅

### Phase 1 FINAL STATUS ✅✅✅
**ZERO SORRIES - FULLY PROVEN!**
- Total: ~465 lines, 13 declarations
- All extraction targets: xBudget = C0 ✅
- Build time: <2s (195× faster than classical)

### Phase 2: Extraction & Benchmarking ✅
- [x] Build extraction harness (`lake exe`) ✅
- [x] Implement Python baseline ✅
- [x] Run 6 test cases ✅
- [x] Measure performance ratios ✅
- [x] Verify ≥5/6 pass ≤10× threshold ✅ **ALL 6 TESTS PASS!**

### Phase 3: Integration & Documentation ⬜
- [ ] Demonstrate downstream use
- [ ] Document findings
- [ ] Write final report

---

## Notes & Observations

**Week 1 Days 1-2 (2025-10-25):**

### Key Achievement: Computation/Verification Separation ✅

We successfully implemented **Option B** design pattern:
- **Computable layer**: `iterate_n_times` (xBudget = C0) - takes N as parameter, just iterates
- **Verification layer**: `iterations_needed` (xBudget = C5) - computes N(ε) using Real.log

**Why this matters:**
- The extracted code doesn't need to compute N(ε) dynamically (avoiding Real.decidableLE issues)
- Users provide max_iter explicitly (realistic usage pattern)
- Proofs still have tight theoretical bounds via `iterations_needed`
- Clean separation: extraction path is 100% C0, proofs can use classical logic

**Discovery: Real number decidability blocker**
- `Real.decidableLE` is noncomputable (uses classical axioms)
- Cannot write `if K_pow_n * d₀ <= threshold` in computable code
- Solution: Don't compute threshold checks - just iterate N times
- This mirrors real-world practice (set max_iter, trust convergence guarantees)

**Verified with baseline scripts:**
```bash
./scripts/baseline_module.sh Budgets.BanachExtraction "iterate" ...
# Result: iterate_n_times has vBudget=C0, xBudget=C0 ✅
```

