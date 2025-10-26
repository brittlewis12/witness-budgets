# Week 0 Day 2: Constructive Banach - Scope Definition

**Date:** 2025-10-25
**Goal:** Define the constructive formalization scope, data structures, and comparison framework

---

## 1. Metric Space Approach

### Decision: Reuse Lean's `MetricSpace` with Explicit Cauchy Convergence

**Why not create a custom constructive metric space?**
- Lean's `MetricSpace` typeclass is already compatible with constructive reasoning
- The issue isn't the metric space structure itself, but `CompleteSpace`
- Reusing standard typeclasses maximizes compatibility

**Completeness strategy:**

**Option A: Explicit Cauchy sequence with witness (CHOSEN)**
```lean
structure ConstructivelyComplete (X : Type*) [MetricSpace X] where
  /-- For any Cauchy sequence with a modulus, produce a limit -/
  limit : (ℕ → X) → (ℕ → ℕ → ℝ) → X
  /-- The modulus guarantees Cauchy property -/
  is_cauchy : ∀ (seq : ℕ → X) (modulus : ℕ → ℕ → ℝ),
    (∀ ε > 0, ∃ N, ∀ m n ≥ N, dist (seq m) (seq n) < ε) →
    ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (seq n) (limit seq modulus) < ε
```

**Rationale:**
- For Banach, we have an *explicit* Cauchy sequence: `f^[n] x`
- We have an *explicit* modulus: geometric convergence `K^n`
- We can construct the limit iteratively to any tolerance
- No need for abstract completeness - we build the limit directly

**Option B: Use existing `CompleteSpace` but prove convergence constructively**
- Keep `[CompleteSpace X]` assumption
- Build the fixed point iteratively, don't rely on abstract "limits exist"
- Use the Cauchy property constructively to find the stopping point

**Decision: Use Option B initially**
- Simpler to implement (works with existing mathlib infrastructure)
- The construction is explicit (iterate until convergence)
- We can prove it satisfies `CompleteSpace` properties
- If xBudget creeps, can switch to Option A

### Key Design Principle

**The iteration function IS the witness:**
```lean
def findFixedPoint (f : X → X) (K : ℝ) (x₀ : X) (ε : ℝ) :
    {x : X // dist x (f x) < ε ∧ ∀ n, dist (f^[n] x₀) x ≤ bound n}
```

This returns a *computable* fixed point approximation, not an abstract limit.

---

## 2. Contraction Record Structure

### Definition

```lean
structure ContractionData (X : Type*) [MetricSpace X] where
  /-- The contracting function -/
  f : X → X
  /-- Lipschitz constant K < 1 -/
  K : ℝ
  /-- Proof that 0 ≤ K < 1 -/
  K_nonneg : 0 ≤ K
  K_lt_one : K < 1
  /-- Lipschitz condition -/
  lipschitz : ∀ x y, dist (f x) (f y) ≤ K * dist x y
  /-- Decidability for stopping criterion (optional, may not need) -/
  -- dist_decidable : DecidableRel (λ x y : X => dist x y < ε)
```

**Comparison to mathlib:**
- Mathlib: `ContractingWith K f := K < 1 ∧ LipschitzWith K f`
- Ours: Explicit structure with proofs bundled
- Trade-off: More verbose, but all data is explicit

**Why bundle everything?**
- Makes extraction clearer (all inputs visible)
- Avoids typeclass resolution during extraction
- Explicit K value needed for iteration bound calculation

---

## 3. Return Type Specification

### Core Theorem Signature

```lean
/-- Constructive Banach fixed-point theorem with explicit convergence rate -/
def banach_fixed_point
    (X : Type*) [MetricSpace X] [CompleteSpace X]
    (contr : ContractionData X)
    (x₀ : X)
    (h_bounded : dist x₀ (contr.f x₀) < ⊤) :
    { y : X //
      contr.f y = y ∧  -- y is a fixed point
      ∀ n : ℕ, dist (contr.f^[n] x₀) y ≤
        dist x₀ (contr.f x₀) * contr.K ^ n / (1 - contr.K) }
```

**Return type breakdown:**
- `{ y : X // P y }` - Σ-type (constructive witness)
- First component: the fixed point `y`
- Second component: proof that it's a fixed point
- Third component: explicit convergence rate bound

**Alternative: Separate iteration count**
```lean
structure FixedPointWitness (X : Type*) where
  point : X
  is_fixed : f point = point
  iterations_to_ε : ℝ → ℕ  -- Given ε, how many iterations needed?
  convergence_bound : ∀ n ε, dist (f^[n] x₀) point < ε →
    n ≥ iterations_to_ε ε
```

**Decision: Use simple Σ-type for theorem, add iteration count function separately**

### Iteration Count Formula

```lean
/-- Given tolerance ε, compute required iterations -/
def iterations_needed (contr : ContractionData X) (x₀ : X) (ε : ℝ) : ℕ :=
  Nat.ceil (Real.log (dist x₀ (contr.f x₀) / ((1 - contr.K) * ε)) /
            Real.log (1 / contr.K))
```

This makes N(ε) = ⌈log(d(x₀, f x₀) / ((1-K)ε)) / log(1/K)⌉ **computable**.

---

## 4. Iteration Function (The Extractable Core)

### Signature

```lean
/-- Iterate f until convergence to tolerance ε -/
def iterate_to_fixed_point
    (contr : ContractionData X)
    (x₀ : X)
    (ε : ℝ)
    (ε_pos : 0 < ε) :
    { x : X // dist x (contr.f x) < ε }
```

**Implementation strategy:**
```lean
def iterate_to_fixed_point (contr : ContractionData X) (x₀ : X) (ε : ℝ)
    (ε_pos : 0 < ε) : { x : X // dist x (contr.f x) < ε } :=
  let N := iterations_needed contr x₀ ε
  let x_N := contr.f^[N] x₀
  ⟨x_N, by
    -- Prove: dist x_N (f x_N) < ε using convergence bound
    sorry
  ⟩
```

**Key property: This is computable!**
- Input: contraction data, initial point, tolerance
- Output: point within ε of fixed point
- Computation: iterate N times (where N is computed from the formula)

**This is what extracts to executable code.**

---

## 5. Proof Strategy Outline

### Step 1: Cauchy Sequence with Explicit Rate

```lean
lemma iterate_is_cauchy (contr : ContractionData X) (x₀ : X) :
    ∀ m n, dist (contr.f^[m] x₀) (contr.f^[n] x₀) ≤
      dist x₀ (contr.f x₀) * contr.K^(min m n) / (1 - contr.K)
```

**Proof:** Geometric series + triangle inequality (same as mathlib)

### Step 2: Convergence to Limit

```lean
lemma iterate_converges (contr : ContractionData X) (x₀ : X) :
    ∃ y, ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (contr.f^[n] x₀) y < ε
```

**Proof:** Use completeness + Cauchy property (mathlib has this)

### Step 3: Limit is Fixed Point

```lean
lemma limit_is_fixed (contr : ContractionData X) (x₀ : X) (y : X)
    (h_limit : ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (contr.f^[n] x₀) y < ε) :
    contr.f y = y
```

**Proof:** Continuity + uniqueness of limits

### Step 4: Construct Witness

```lean
def banach_fixed_point ... :=
  -- Use completeness to get limit y
  let ⟨y, h_conv⟩ := iterate_converges contr x₀
  -- Prove y is fixed point
  let h_fixed := limit_is_fixed contr x₀ y h_conv
  -- Prove convergence rate
  let h_rate := ... -- from geometric bound
  ⟨y, ⟨h_fixed, h_rate⟩⟩
```

**Critical: No `Classical.choose`!**
- Use `let ⟨y, _⟩ :=` to destructure existential
- This works because we're in `Type` (not `Prop`)
- The witness is computable (built from iteration)

---

## 6. Key Design Decisions Summary

| Aspect | Decision | Rationale |
|--------|----------|-----------|
| **Metric space** | Reuse `MetricSpace`, keep `CompleteSpace` | Compatibility + simplicity |
| **Contraction** | Explicit structure vs typeclass | Bundled data for extraction clarity |
| **Return type** | Σ-type `{x // IsFixedPt f x ∧ Rate}` | Constructive witness |
| **Iteration count** | Computable function `iterations_needed` | Makes N(ε) explicit |
| **Extraction target** | `iterate_to_fixed_point` function | Direct executable algorithm |
| **Proof strategy** | Cauchy → Complete → Fixed | Same as mathlib, but constructive witness |

---

## 7. Expected xBudget = C0 Verification

**Where we avoid classical axioms:**

1. ✅ **No `Classical.choose`** - use Σ-type destructuring
2. ✅ **No `Classical.choice`** - don't need to pick from arbitrary collection
3. ✅ **No LEM in Type positions** - keep decidability explicit where needed
4. ✅ **Computable iteration** - `f^[N] x₀` is directly executable

**Potential xBudget risks:**
- ⚠️ `CompleteSpace` might hide classical choice
- ⚠️ Distance decidability might require classical instances
- ⚠️ Real number computations might be non-computable

**Mitigation:**
- Monitor with `#wbudget` continuously
- Add explicit `Decidable` instances if needed
- Use `Rat` for test cases if `Real` causes issues

---

## 8. Comparison Template

**We'll track these metrics side-by-side:**

| Metric | Classical (Mathlib) | Constructive (Ours) |
|--------|---------------------|---------------------|
| **Lines of code** | | |
| - Core theorem | 10 | ? |
| - Supporting lemmas | ~30 | ? |
| - Data structures | ~5 | ? |
| - Total | ~45 | ? |
| **Verification time** | 179s (43 decls) | ? |
| **Dependencies** | 4 (Analysis, Dynamics, Topology, Lipschitz) | ? |
| **Budget** | | |
| - vBudget | C5 (97.7%) | C0 (target) |
| - xBudget | C0 (95.3%), C5 for efixedPoint | C0 (target) |
| **Proof technique** | Cauchy + Classical.choose | Cauchy + Σ-type |
| **Extractable?** | No | Yes (goal) |
| **Convergence rate** | Explicit | Explicit |
| **Iteration function** | None | `iterate_to_fixed_point` |

---

## 9. Test Suite Specification

**From the plan, we'll test on:**

1. **`f(x) = 0.5x + 1`** (K=0.5, ℝ)
   - Initial: x₀ = 0
   - Expected fixed point: x* = 2
   - Tolerance: ε = 0.01
   - Expected iterations: N ≈ 7

2. **`f(x) = 0.9x + 0.1`** (K=0.9, slow)
   - Initial: x₀ = 0
   - Expected fixed point: x* = 1
   - Tolerance: ε = 0.01
   - Expected iterations: N ≈ 44

3. **`f(x) = 0.1x + 5`** (K=0.1, fast)
   - Initial: x₀ = 0
   - Expected fixed point: x* = 5.556...
   - Tolerance: ε = 0.01
   - Expected iterations: N ≈ 3

4. **Piecewise on [0,1]**
   - TBD based on implementation feasibility

5. **Rational metric (ℚ)**
   - Test decidability interplay
   - May simplify if ℝ causes xBudget issues

6. **Near-edge case** (K=0.99, ε=0.001)
   - Stress test convergence
   - Expected iterations: N ≈ 460

**Success criteria per test:**
- Extracted code terminates
- Returns point within ε of true fixed point
- Iteration count ≤ theoretical bound N(ε)

---

## 10. Extraction Pipeline Specification

### Target: `lake exe banach_demo`

**CLI harness structure:**
```lean
-- In scripts/BanachDemo.lean
def main (args : List String) : IO Unit := do
  -- Parse: contraction type, K value, x₀, ε
  let contr := ... -- construct ContractionData
  let x₀ := ...
  let ε := ...

  -- Run iteration
  let result := iterate_to_fixed_point contr x₀ ε _

  -- Output: fixed point, iteration count, error
  IO.println s!"Fixed point: {result.val}"
  IO.println s!"Distance to f(x*): {dist result.val (contr.f result.val)}"
  IO.println s!"Iterations: {iterations_needed contr x₀ ε}"
```

**Build target (in lakefile.lean):**
```lean
lean_exe banach_demo where
  root := `BanachDemo
  srcDir := "scripts"
```

**Usage:**
```bash
$ lake exe banach_demo linear 0.5 1.0 0 0.01
Fixed point: 2.000
Distance to f(x*): 0.0001
Iterations: 7
Time: 0.05s
```

### Baseline: Python Reference Implementation

```python
# scripts/banach_baseline.py
def banach_fixed_point(f, K, x0, epsilon):
    """Reference implementation for benchmarking"""
    x = x0
    n = 0
    while True:
        x_next = f(x)
        if abs(x_next - x) < epsilon:
            return x_next, n
        x = x_next
        n += 1
        if n > 10000:  # safety
            raise RuntimeError("Did not converge")

# Test cases
def test_linear_half():
    f = lambda x: 0.5 * x + 1.0
    x_star, n = banach_fixed_point(f, 0.5, 0.0, 0.01)
    print(f"Fixed point: {x_star}, Iterations: {n}")
```

**Benchmarking protocol:**
```bash
# Run Python baseline
$ time python3 scripts/banach_baseline.py
# Record: iterations, time

# Run Lean extraction
$ time lake exe banach_demo linear 0.5 1.0 0 0.01
# Record: iterations, time

# Compare: ratio Lean/Python
```

**Success threshold:** ≤10× slowdown on ≥5/6 test cases

---

## 11. Next Steps (Week 1)

**Days 1-2: Interface definition**
- Implement `ContractionData` structure
- Implement `iterations_needed` function
- Set up budget monitoring infrastructure

**Days 3-5: Core theorem**
- Prove Cauchy lemma with explicit rate
- Prove convergence (use completeness)
- Construct Σ-type witness (no `Classical.choose`!)
- Verify xBudget = C0

**Days 6-7: Comparison**
- Document proof side-by-side with mathlib
- Measure verification time
- Produce comparison table

**Week 2: Extraction + benchmarking**

---

## Summary

**Constructive Banach scope:**
- ✅ Metric space approach defined
- ✅ Contraction record structure specified
- ✅ Return type: Σ-type with rate bound
- ✅ Iteration function signature clear
- ✅ Proof strategy outlined
- ✅ Test suite specified (6 cases)
- ✅ Extraction pipeline defined
- ✅ Comparison template ready

**Ready to implement Week 1!**
