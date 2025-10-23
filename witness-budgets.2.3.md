# Witness Budgets for Transparent Oversight: A Constructive Basis for Verifiable AI Math

*A synthesis connecting AI safety, formal methods, and constructive mathematics*

---

## TL;DR

**Problem:** AI systems producing mathematical proofs need both correctness (verification) and usability (executable algorithms with bounds). Classical proofs provide verification; constructive proofs provide both but aren't explicitly tracked.

**Solution:** Witness Budgets (C0–C5) - a framework to measure and track non-constructive reasoning, optimizing for AI automation and algorithm extraction, with a concrete build plan uniting AI safety, formal methods, and constructive mathematics.

---

## Executive Summary

For AI systems doing mathematical reasoning to be verifiable and alignable (per Christiano's transparent oversight framework), they must operate on foundations that provide **executable content (witnesses, bounds, and rates)** - not just correctness proofs, but concrete algorithms with certified properties.

This document argues that:
1. **Non-constructive classical mathematics** creates "oracle dependencies" that provide logical verification but resist operational extraction
2. **A graded "witness budget"** framework (C0–C5) makes oracle dependence trackable and measurable
3. **Constructive foundations with quantitative content** provide both verification and operational extractability
4. **This is testable**: Instrument proof assistants, formalize applied mathematics constructively, measure automation gains

**Critical distinction:** Classical proofs are verifiable (Lean/Coq check them successfully). Constructive proofs are verifiable AND operational (they yield executable algorithms and bounds). For oversight and automation, we need both properties.

**Scope:** This addresses AI systems producing *executable algorithms with quantitative bounds* from mathematical reasoning - a growing subset of AI capabilities including automated mathematics, certified software, and scientific computing. It does NOT address general AI alignment (value learning, deception, robustness), non-mathematical AI capabilities (vision, language, robotics), or pure theorem proving where execution isn't required.

---

## Who This Is For / What We Need From You

**AI Safety Researchers:**
- Consider: When formal verification is needed, prefer C0–C2 formulations (executable witnesses improve automation)
- Try: Budget-tracking your formal benchmarks, measure automation differences

**Formal Methods Community:**
- Try: Run the budget linter on a library subfolder, report violations and refactoring opportunities
- Contribute: Help design the instrumentation and CI integration

**Constructive Mathematics Community:**
- Help: Design quantitative API signatures (explicit moduli, rates, bounds) for applied results
- Formalize: Target C0–C2 versions of key applied theorems with extractable content

---

## Part I: The Witness Budget Framework

### 1.1 The C0–C5 Spectrum: Grading Oracle Dependence

Most mathematics isn't purely constructive or purely classical - it falls on a spectrum. The witness budget framework makes this spectrum explicit and measurable:

| Level | Name | Principles | What You Get | Typical Examples |
|-------|------|------------|--------------|------------------|
| **C0** | Fully Witnessful | Intuitionistic logic only | Witness + algorithm + bounds | Finite combinatorics; Banach fixed-point with explicit rate |
| **C1** | Existence-Only (invariants-only use; ∥∃x.P∥ in HoTT) | Propositional truncation | Logical existence; consumers must use invariant properties only | "A solution exists" where downstream uses only solution-independent facts |
| **C2** | Countable Choice | ACω, DC (sequential/countable choices) | Often extractable, works for most analysis | Cauchy subsequences; separable Hilbert spaces; completeness arguments |
| **C3** | Classical Logic | LEM (excluded middle) only | Verifiable but often non-executable | Many classical proofs that avoid choice; decidability by cases |
| **C4** | Choice Fragments | Ultrafilter Lemma ≡ Boolean Prime Ideal | Domain-specific oracles | Stone-Čech compactification; Tychonoff for compact Hausdorff spaces* |
| **C5** | Full Choice | AC ≡ Zorn's Lemma ≡ Well-Ordering Principle | Global arbitrary selection; minimal witness content | Arbitrary vector space bases; Hahn-Banach (non-separable, full generality); Tychonoff for arbitrary uncountable products*; well-ordering reals |

**Key technical notes:**
- Zorn's Lemma is equivalent to full AC (over ZF), not a weaker fragment - it belongs in C5
- Ultrafilter Lemma and Boolean Prime Ideal theorem are equivalent (over ZF) - combined in C4
- *Tychonoff's theorem has multiple formulations: arbitrary products of compact spaces requires full AC (C5); products of compact **Hausdorff** spaces requires only Ultrafilter Lemma (C4); countable products can be proven constructively or with DC (C2)

### 1.2 Budget Calculus: Compositional Tracking

**Composition rule:**
```
budget(f ∘ g) = max(budget(f), budget(g))
```

**Monotonicity:**
If theorem T uses lemma L with budget C2, then T inherits budget ≥ C2

**Refinement:**
If a consumer proves naturality/invariance, can downgrade C1 → C0 (witness-free consumption becomes witnessful reasoning)

**Effect system formalization:**
Treat non-constructive steps as effects in a type system:
```
Effect types: [Classical, Truncation, ACω, DC, ULBPI, AC]

Proof term Γ ⊢ t : A has effect row ε

Oversight cost = f(ε) (monotone in effect budget)
```

This makes witness budgets **mechanically trackable** across library composition.

### 1.3 What Budgets Tell Us

**For automation:** Lower budgets provide more handles for proof search
- C0: Can execute witnesses, verify by running
- C1–C2: Sequential structure guides search
- C3–C5: Fewer algorithmic landmarks, harder automation

**For extraction:** Only C0–C2 generally support program extraction
- C0: Direct extraction of algorithms
- C1: Extract when consumers are invariant
- C2: Extract with countable/sequential structure
- C3+: Usually no extraction possible

**For verification:** All levels are formally verifiable
- Classical proofs verify successfully in Lean/Coq
- Verification ≠ operational content
- Both matter for practical AI systems

### 1.4 Two Concrete Examples

**Example 1: Banach Fixed-Point Theorem**

**Statement (C0-capable):**
```
Given: Metric space (X, d), function f: X → X
Lipschitz: ∃L < 1. ∀x,y. d(f(x), f(y)) ≤ L · d(x, y)
Complete: X is complete
Claim: ∃!x. f(x) = x (unique fixed point exists)
```

**Constructive version with quantitative content (C0):**
```
Given: Same as above
Claim: ∃!x. f(x) = x
PLUS: Convergence bound
      d(xₙ, x*) ≤ (Lⁿ/(1-L)) · d(x₁,x₀)
      Therefore: N(ε) = ⌈ ln( d(x₁,x₀) / ((1−L)ε) ) / ln(1/L) ⌉
      Where d(x₁,x₀) is the observable distance between first two iterates
```

**What you gain:** Not just "it converges" but "it converges in exactly N iterations for tolerance ε"

This is **operational content** - the difference between knowing a solution exists and being able to compute it with certified bounds.

**Example 2: Hahn-Banach Extensions**

**The choice:** Given functional f on subspace, infinitely many norm-preserving extensions to whole space exist. Classical proof: use AC to assert "pick one."

**The observation:** For any theorem about "an extension," the proof works regardless of which extension. The specific choice doesn't matter.

**The refactoring:** Don't pick a representative. Work with:
- The **space of extensions** (forms a convex set)
- The **invariant properties** all extensions share
- Quotient/torsor structures that make "choice" irrelevant

**Budget impact:** Explicit invariance proofs can downgrade oracle dependence from C5 to C1 or even C0.

---

## Part II: Philosophical Foundations

### 2.1 Initial Skepticism: Why Does Choice Feel Wrong?

The Axiom of Choice (AC) allows selecting one element from each set in an arbitrary collection, without specifying *how* to make the selections.

**AC says:** "There exists a function that picks one element from each set"
**Without providing:** Any rule, procedure, or description of that function

**The discomfort:** If I can't construct it, describe it, or approximate it, in what sense does it "exist"?

This isn't just aesthetic squeamishness - it's about **what mathematical claims should provide**.

### 2.2 Circles vs Choice Functions: Different Idealizations

**Consider circles:** We accept them as mathematical objects despite requiring infinite precision to manifest physically. Does this mean we should accept AC-dependent objects too?

**No - they're different kinds of idealization:**

**Circles (acceptable idealization):**
- Finite definition: x² + y² = r²
- Definable procedure: "all points distance r from center"
- Approximable: polygons with n sides → circle as n → ∞
- **Rates of approximation:** Error ~ O(1/n²)
- **Rule-governed idealization of a constructive process**

**AC choice functions (problematic assertion):**
- No definition (by construction - that's the point of AC)
- No procedure whatsoever
- No approximation notion (what does "close to arbitrary choice" mean?)
- No complexity characterization
- **Assertion without specification**

**Key difference:** Circles are limits of constructive processes with measurable convergence rates. AC asserts existence without any process, even idealized.

This connects to computational complexity: For circles, you can ask "how many sides to get within ε?" For AC-dependent objects, there's no analogous question - no algorithm means no complexity.

### 2.3 The "It Doesn't Matter Which" Insight

Often, when AC is invoked, the proof works regardless of which choice is made. This is revealing.

**Key observation:** If the specific choice doesn't matter for the proof, maybe we shouldn't be "choosing" at all - we should be working with the **structure of the space of possibilities**.

**Pattern in AC usage:**
1. Collection has no distinguishing features between elements
2. Proof needs "pick one from each set"
3. But conclusion holds for ANY valid selection
4. The choice is from a **definable class** (elements satisfying some property)

**Reframing strategy:**
Instead of "arbitrary choice from unstructured set," work with:
- **Torsors** (spaces acted on freely and transitively by groups)
- **Quotients** (identifying equivalent choices)
- **Invariant properties** (what all valid choices share)
- **Structural reasoning** about equivalence classes

This turns "arbitrary selection" into "reasoning about structure that makes representatives irrelevant."

**Practical implementation:** Require consumers to prove they only use invariant properties. If choice "doesn't matter," this should be provable.

---

## Part III: The AI Safety Connection

### 3.1 Christiano's Transparent Oversight Framework

**Paul Christiano's core insight for AI alignment:**

**The problem:** As AI systems become more capable, their reasoning may exceed human ability to directly verify. A superintelligent AI might produce correct results for wrong reasons, or reasoning too complex for humans to follow.

**The solution space:**
- **Unacceptable: Black-box reasoning:** AI produces answers we can't check → unalignable
- **Required: Transparent step-by-step reasoning:** Each step is checkable, even if the search is superhuman → alignable through oversight

**The principle:** "We cannot align AI that reasons in opaque ways, but we can align AI whose reasoning process we can audit at each step."

**Key mechanisms:**
- Iterated amplification (break complex questions into verifiable sub-questions)
- Debate (adversarial verification of reasoning steps)
- Recursive reward modeling (verify stepwise, not just endpoints)

### 3.2 The Structural Connection

**How this maps to mathematical foundations:**

```
Christiano's Framework:
├─ Black-box oracle → can't inspect internal mechanism → oversight difficult
├─ Transparent reasoning → can verify each step → oversight possible
└─ Need: Stepwise verifiable and executable artifacts

Mathematical Foundations:
├─ Non-constructive proof (AC) → no witness/algorithm → can't execute/extract
├─ Constructive proof → explicit witness → can execute and verify
└─ Need: Both logical correctness AND operational content
```

**The parallel:** Both frameworks share a principle - **to use or trust a result, you need access to its internal mechanism**, not just confirmation that a correct answer exists somewhere.

**Critical nuance:** These are related but distinct concerns:
- **Christiano's problem:** Capability oversight - can humans verify superhuman reasoning?
- **Constructive math:** Operational content - can we extract algorithms and bounds?

**Where they converge:** For AI systems doing **algorithmic mathematics** (certified software, numerical methods, automated science), we need:
1. **Verification:** Each proof step is checkable (classical and constructive both provide this)
2. **Operational content:** Witnesses, algorithms, bounds extractable (only constructive provides this)

**For transparent oversight of AI producing executable mathematical artifacts, constructive foundations provide both requirements.**

### 3.3 Verification vs Operationalization: The Key Distinction

**What we mean by "verifiable":**
Classical proofs ARE verifiable - Lean and Coq successfully check their correctness. Every step can be formally verified. This is not in question.

**What we mean by "operational":**
Operational content means extractable:
- Witnesses (concrete objects satisfying existence claims)
- Algorithms (procedures to compute results)
- Bounds (explicit rates, error terms, moduli)
- Quantitative data (not just asymptotic behavior)

**The two-dimensional space:**

| | Verifiable | Operational |
|---|---|---|
| **Classical (C3–C5)** | Yes | No (usually) |
| **Constructive (C0–C2)** | Yes | Yes |

**For AI safety and automation:**
- **Verification alone:** Confirms correctness but doesn't enable execution, composition, or algorithmic search
- **Operational content:** Enables extraction, testing, composition into pipelines, and provides algorithmic "landmarks" for proof search

**One-liner:** "We track correctness with verification and usability with operational content."

### 3.4 Why This Matters for AI Mathematics

**Current state:**
- Recent systems using Lean for mathematical reasoning (including Olympiad-level problem solving)
- Success requires producing verifiable artifacts
- Proof search benefits from executable witnesses (can test candidates)
- Composition requires outputs to feed forward

**The bottleneck with high-budget proofs:**

Classical non-constructive proofs are **verifiable but not operational**:
- Can formally check correctness
- Cannot execute to test intermediate results
- Cannot extract witnesses to feed to next step
- Cannot provide algorithmic landmarks for search
- Cannot compose into computational pipelines

**For AI automation:**
- **Search over programs:** Can enumerate algorithms systematically
- **Search over oracles:** Cannot enumerate non-computable functions
- **Verify with witnesses:** Run and check concrete results
- **Verify without witnesses:** Must trust logical structure alone
- **Iterate with feedback:** Execute, measure, refine (with witnesses)
- **Iterate without feedback:** No concrete outputs to test (without witnesses)

**The effect on proof search:**
Lower witness budgets provide more structure:
- C0: Execute witnesses, verify by running, use as test cases
- C1–C2: Sequential construction guides search strategy
- C3–C5: Fewer algorithmic landmarks, must search logical space abstractly

### 3.5 Three Verification Channels

The landscape isn't binary - there are three approaches with different properties:

**1. Constructive Witness (C0–C2)**
- Provides: Executable algorithm/witness + quantitative bounds
- Properties: Verifiable AND operational
- Best for: Automation, composition, downstream computation
- Example: Banach fixed-point with convergence rate

**2. Classical Proof (C3–C5)**
- Provides: Logical correctness
- Properties: Verifiable but NOT operational
- Best for: Pure existence results where witnesses unnecessary
- Example: Excluded middle arguments, non-constructive fixed-points

**3. Interactive/PCP (Probabilistic Checkable Proofs)**
- Provides: Succinct certificates verifiable via randomness
- Properties: Efficiently verifiable, usually not operational
- Best for: Complexity-theoretic results, very large proofs
- Example: Cryptographic zero-knowledge proofs

**For AI automation and composability, constructive witnesses are optimal.** Other channels serve different purposes but don't provide the operational content needed for algorithmic extraction and pipeline composition.

### 3.6 How This Unifies Three Communities

This synthesis provides missing motivation across three traditionally siloed fields:

**AI Safety → Deeper "Why" for Formal Methods**
- Current view: "Use formal verification as a tool"
- With framework: "Need constructive foundations as paradigm"
- Explains: Why operational content matters structurally, not just practically
- Impact: Connects scalable oversight to mathematical foundations

**Constructive Mathematics → Modern Relevance**
- Current view: "Philosophically purer but niche concern"
- With framework: "Safety requirement for transparent AI"
- Explains: Century-old work suddenly has civilizational stakes
- Impact: Makes constructive research directly relevant to AI capabilities

**Formal Methods → Existential Purpose**
- Current view: "Good for critical software verification"
- With framework: "Foundation for safe superintelligent reasoning"
- Explains: Not just a tool but infrastructure for AI oversight
- Impact: Elevates from specialized application to civilizational infrastructure

**Important caveat:** These communities care about witness budgets for somewhat different reasons:
- AI safety: Extractability for oversight and algorithmic composition
- Constructive math: Ontological commitments (what exists vs what's definable)
- Formal methods: Certified algorithm extraction and complexity bounds

The framework helps all three, but through distinct mechanisms relevant to each field's concerns.

---

## Part IV: Proof Mining and Quantitative Content

### 4.1 Constructive ≠ Practical (Without Bounds)

**Critical caveat:** Constructive proofs yield algorithms, but not necessarily *good* algorithms.

**Example:**
```
Theorem: ∀x. P(x) ∨ ¬P(x)
Proof: By exhaustive search over all x, decide which holds
```
- Constructive: Yes (explicit algorithm exists)
- Practical: No (may require exponential or infinite time)

**The gap:** Constructivity gives existence of algorithm, not complexity bounds.

**Solution:** **Quantitative proof mining** - systematically extract:
- Convergence rates (not just "converges")
- Error bounds (not just "approximates")
- Moduli of continuity (not just "continuous")
- Sample complexity (not just learnable)
- Iteration counts (not just "eventually")

### 4.2 Kohlenbach's Proof Mining Program

**Core thesis:** Most classical analysis theorems have hidden constructive content - explicit bounds and rates that the classical proof obscures.

**Method:** Use logical transformations (realizability, Dialectica interpretation, functional interpretation) to systematically extract effective bounds from non-constructive proofs.

**Key results (examples):**

**Fixed-point theory:**
- Classical: "Iterates converge to fixed point"
- Extracted: N(ε) = ⌈ln(d(x₁,x₀) / ((1-L)ε)) / ln(1/L)⌉ iterations for tolerance ε
- From: Contraction constant L, observable initial iterate distance d(x₁,x₀)

**Ergodic theory:**
- Classical: "Time averages converge to space averages"
- Extracted: Metastability rates (effective convergence moduli)
- Applications: Computational ergodic theory

**Nonlinear analysis:**
- Classical: "Iterative scheme converges"
- Extracted: Explicit rates for Krasnoselski-Mann iterations
- Applications: Optimization algorithms

**Optimization:**
- Classical: "Gradient descent converges"
- Extracted: Convergence rates depending on Lipschitz constants
- Applications: Certified machine learning

**The bridge:** Proof mining connects classical applied mathematics to executable, verifiable algorithms with certified bounds. This is exactly what AI systems need for transparent algorithmic reasoning.

### 4.3 Quantitative Content as API Contract

**Make bounds explicit in type signatures:**

Instead of:
```lean
theorem exists_fixed_point (f : X → X) (contract : IsContraction f) :
  ∃ x, f x = x
```

Demand:
```lean
theorem exists_fixed_point
  (f : X → X)
  (L : ℝ) (hL : L < 1)
  (contract : ∀ x y, dist (f x) (f y) ≤ L * dist x y) :
  { x : X // f x = x } ×                    -- witness
  (ℝ → ℕ)                                    -- rate function: ε ↦ N(ε)
```

**This forces extraction of quantitative content, not just existence.**

**For practical mathematics:**
- Numerical analysts need: convergence rates to choose methods
- Software engineers need: complexity bounds to predict runtime
- AI systems need: iteration counts to plan computation

**Type-level enforcement:** If the API demands `(witness, rate)`, proofs must provide both. Can't just assert "converges" without explicit rate function.

---

## Part V: Applied Mathematics Case Studies

### 5.1 Honest Assessment: Where High Budgets Actually Matter

**Our working hypothesis:** Much of computational mathematics can be reformulated at C0–C2 with appropriate APIs and quantitative signatures. The case studies below will test this empirically.

**Tier 1: Genuinely needs high budget (C4–C5)**
- Hahn-Banach theorem (general non-separable normed spaces)
- Tychonoff theorem (arbitrary products of compact spaces need C5; compact Hausdorff products need C4)
- Every vector space has basis (infinite-dimensional, non-separable)
- Algebraic closure (general fields - uses Zorn, hence C5)
- Well-ordering reals (definitionally requires full AC)

**Tier 2: Often needs C2–C3, constructive workarounds exist**
- Functional analysis (many results, but separable spaces reduce budget significantly)
- General topology (compactness arguments, but constructive for countable/metric spaces)
- Some optimization existence theorems (classical proofs exist, but algorithms often computable)

**Tier 3: Appears to need AC, actually works at C0–C2**
- Most undergraduate analysis (completeness, sequential compactness)
- Differential equations (existence/uniqueness for nice cases)
- Probability theory (much standard work on separable spaces uses ACω/DC; some advanced results need stronger choice)
- Most numerical mathematics (inherently finite-dimensional or countable)

**The measurement challenge:** We'll formalize theorems in targeted domains (optimization, separable analysis) and measure what percentage achieve C0–C2 with explicit moduli.

### 5.2 Case Study 1: Hahn-Banach Theorem

**Classical statement (C5):**
"Every continuous linear functional on a subspace of a normed space can be extended to the whole space, preserving norm."

**Where it's used in practice:**
- Signal processing: Reconstruct full signal from partial measurements
- Convex optimization: Separating hyperplane theorem → duality theory → SVM, linear programming
- Distribution theory: Defining generalized functions (Dirac delta on test functions)
- Economics: Price theory, supporting hyperplanes for preference sets

**Why full AC is needed:**
Extension isn't canonical - infinitely many valid norm-preserving extensions exist with no rule for distinguishing them. The classical proof uses Zorn's Lemma (equivalent to AC) to construct one.

**Constructive alternatives and their scope:**

**Alternative 1: Separable spaces (C2)**
- In Hilbert spaces with countable orthonormal basis, construct extension explicitly via that basis
- Works for: Most physics applications (L² spaces in quantum mechanics, signal processing)
- Fails for: Some function spaces (L^∞, non-separable Banach spaces used in control theory)
- Budget: C2 (uses countable structure)

**Alternative 2: Explicit modulus of continuity (C0)**
- If functional comes with explicit continuity data (modulus of uniform continuity), construct extension algorithmically
- Works for: Numerical analysis (functions from approximations with error bounds)
- Fails for: Abstract functionals without explicit modulus
- Budget: C0 (fully constructive with modulus as input)

**Alternative 3: Bishop's located sets (C1–C2)**
- Work with sets having distance functions (locatedness condition)
- Get Hahn-Banach variants with additional hypotheses
- More technical conditions but covers many applications
- Budget: C1–C2 depending on exact formulation

**The gap:**
- Classical: Unrestricted generality - works for ALL normed spaces, ALL functionals
- Constructive: Works for nice enough spaces (separable, located, with moduli)
- Trade-off: Lose some generality, gain executable algorithms with bounds

**Practical impact:** Most applications in computational settings already have the structure needed for C0–C2 versions. The full generality is rarely used in practice.

### 5.3 Case Study 2: Vector Space Bases

**Classical theorem (C5):** "Every vector space has a basis (maximal linearly independent set)"

**Where it matters:**
- Quantum mechanics: Spectral theorem requires eigenbases for operators
- Fourier analysis: Function spaces need basis expansions
- Linear algebra: Coordinate systems for abstract spaces
- Control theory: State space representations

**Why full AC is needed:**
For infinite-dimensional, non-structured spaces (like ℝ over ℚ), constructing a basis requires infinitely many arbitrary choices. Even specifying one basis element may require AC.

**Constructive alternatives:**

**Alternative 1: Separable Hilbert spaces (C0–C2)**
- Orthonormal bases are countable and explicitly constructible
- Covers: Most quantum mechanics (L²(ℝ), finite-particle Hilbert spaces)
- Gram-Schmidt process constructs basis from countable dense set
- Budget: C0 if basis computable, C2 if uses countable choice
- Fails for: Non-separable Hilbert spaces, non-Hilbert Banach spaces

**Alternative 2: Schauder bases (C0–C2)**
- Weaker notion: every element is convergent series (not necessarily finite combinations)
- Constructible for: Classical function spaces (C[0,1], Lᵖ spaces)
- Works in: Many practical infinite-dimensional spaces
- Budget: C0–C2 depending on space
- Limitation: Not all spaces have Schauder bases (even classically)

**Alternative 3: Basis-free methods (categorical, C0–C1)**
- Work with vector spaces using universal properties
- Reason about dimension, span, independence abstractly
- No explicit bases needed for many theorems
- Budget: C0–C1 (structural reasoning)
- Trade-off: Less intuitive, harder for explicit computation

**The gap:**
- Classical: Always have coordinate systems for any vector space
- Constructive: Sometimes have explicit coordinates (separable cases), sometimes must work abstractly
- Practical reality: Physics and engineering overwhelmingly use separable spaces anyway

### 5.4 Case Study 3: Tychonoff's Theorem

**Classical statement (formulation-dependent):**
"Product of compact spaces is compact"
- **Arbitrary products** (uncountable, non-Hausdorff): Requires full AC (C5)
- **Compact Hausdorff spaces** (uncountable products): Requires only Ultrafilter Lemma (C4)
- **Countable products**: Constructive or uses only DC (C2)

**Where it's used:**
- Differential equations: Solution spaces as products of function values at each point
- Game theory: Strategy spaces as infinite products → Nash equilibrium existence
- Economics: Commodity spaces (infinitely many goods), preference spaces (infinitely many agents)
- Functional analysis: Weak-* compactness in dual spaces

**Why choice is needed:**
For uncountable products, showing compactness requires choosing accumulation points from uncountably many components simultaneously. Can't do this with finitely many choices or even countably many.

**Constructive alternatives:**

**Alternative 1: Countable products (C0–C2)**
- Tychonoff for countable products is constructive (or uses only DC)
- Covers: Sequence spaces, many analysis applications
- Explicit: Can construct convergent subsequences
- Budget: C0 for finite, C2 for countable
- Fails for: Uncountable parameter spaces

**Alternative 2: Metric compactness (C0–C2)**
- For compact metric spaces, use sequential compactness (constructive)
- Total boundedness + completeness characterization
- Covers: Many practical function spaces in analysis
- Budget: C0–C2 with explicit moduli
- Fails for: Non-metrizable spaces, uncountable products

**Alternative 3: Locale theory (C0–C1)**
- Pointless topology - work with open sets directly, not points
- Tychonoff holds constructively in locale/topos framework
- Covers: Theoretical topology, some computer science applications
- Budget: C0–C1 (synthetic topology)
- Trade-off: Can't extract explicit points for computation, less intuitive

**The gap:**
- Classical: Arbitrary products compact → existence theorems for equations, equilibria
- Constructive: Countable products + locale theory (abstract) OR uncountable products lose compactness
- Practical impact: Many applications can be reformulated with countable approximations

### 5.5 Case Study 4: Economic Equilibrium

**The applied problem:**
- Many agents with preferences over goods
- Want prices where supply equals demand (equilibrium)
- Classical proof: model as fixed-point problem, use compactness + Kakutani theorem

**Classical approach (C4–C5):**
1. Preferences as continuous functions on compact space (may use Tychonoff for product topology: C4–C5)
2. Use Kakutani fixed-point theorem (requires compactness, convexity)
3. Conclude: equilibrium exists

**AC dependency:** Tychonoff (C4–C5) + potentially non-constructive aspects of fixed-point theorem

**Constructive alternatives:**

**Alternative 1: Finite approximation (C0)**
- Discretize commodity space (finitely many goods or finite approximation of continuum)
- Discretize agent types (finite or countable approximation)
- Use computational fixed-point algorithms:
  - Scarf's algorithm (simplicial methods)
  - Lemke-Howson for bimatrix games
  - Continuation methods
- Get approximate equilibria with explicit error bounds
- Budget: C0 (fully algorithmic)
- Works for: Numerical simulation, practical market design
- Trade-off: Approximation errors, computational complexity

**Alternative 2: Countable approximation + reverse math (C2)**
- Many equilibrium results provably need only countable/dependent choice
- Identify minimal principles via reverse mathematics
- More general than finite, less than full AC
- Budget: C2 (countable structure)
- Covers: Many standard economic models
- Shows: Full generality often unnecessary

**Alternative 3: Constructive Brouwer (C0–C2)**
- Brouwer fixed-point theorem has approximate constructive versions
- Require modulus of continuity as input
- Yield approximation algorithms with convergence rates
- Budget: C0–C2 depending on formulation
- Works for: Compact convex domains with explicit metric
- Limitation: Get approximate fixed-point, not exact

**The gap:**
- Classical: Clean existence theorem (equilibrium exists)
- Constructive: Messier hypotheses, but actual algorithms with bounds
- Practical value: For computational economics, algorithms > pure existence

**Trade-off:** Classical elegance vs computational content. For AI systems and practical applications, the algorithmic version is more useful despite less elegant statement.

---

## Part VI: Implementation and Instrumentation

### 6.1 Proof Assistant Reality Check

**Coq/Agda:**
- Constructive by default (intuitionistic type theory)
- Can extract programs from proofs (Set/Type, not Prop)
- Classical axioms (LEM, AC) can be added explicitly if needed
- Natural fit for constructive mathematics
- Extraction gotcha: Content in Prop erases - keep algorithmic content in Set/Type

**Lean 4:**
- Classical by default (LEM and choice axioms available in logic)
- Main library (mathlib4) heavily uses classical reasoning
- Can restrict to constructive fragments with discipline:
  - Avoid `classical`, `choice`, `noncomputable` keywords
  - Mark classical content explicitly with attributes
  - Use CI rules to enforce constructive discipline in specific directories
  - Whitelist escape hatches for specific theorems
- Extraction: Requires staying out of `noncomputable` and keeping witnesses in Type (not Prop)

**Reality check:**
Most formalized mathematics today is classical (especially mathlib). Constructive formalization is **additional work** requiring:
- Different proof techniques
- Explicit moduli and bounds
- More technical conditions
- Careful tracking of choice usage

**This is the primary barrier** - not philosophical disagreement, but engineering cost.

### 6.2 Budget Instrumentation Design

**Minimal Lean 4 implementation:**

```lean
/-- Oracle effects in proof -/
inductive Eff
  | Classical   -- LEM, by_cases
  | Trunc       -- Propositional truncation ∥∃x.P∥
  | ACω         -- Countable choice
  | DC          -- Dependent choice
  | ULBPI       -- Ultrafilter Lemma / Boolean Prime Ideal (equivalent)
  | AC          -- Full Axiom of Choice / Zorn

structure Budget :=
  (effects : Finset Eff)

/-- Attribute to mark budget explicitly -/
@[witness_budget C2]
theorem my_theorem : ... := by
  -- ...

/-- Compositional join for dependencies -/
def Budget.join (b1 b2 : Budget) : Budget :=
  ⟨b1.effects ∪ b2.effects⟩
```

**Inference heuristic:**
Scanner walks compiled proof term, flags uses of:
- `classical`, `Classical.choice`, `Classical.some`, `Classical.em`
- `noncomputable` (usually indicates classical reasoning)
- `Quot.out` without `Quot.lift` (representative picking)
- Known choice lemmas from mathlib (Zorn, Ultrafilter, etc.)

**CI integration:**
```
directory_budgets = {
  "analysis/separable": C2,
  "algebra/group": C0,
  "topology/metric": C2,
  "logic/constructions": C0
}

# Fail build if:
# 1. Explicit @[witness_budget] annotation understates inferred budget
# 2. Directory threshold exceeded
# 3. PR increases budgets without justification
```

### 6.3 Invariance Linter

**Problem:** Code uses `choose`, `some`, `Classical.some` to pick representatives, but doesn't prove choice is irrelevant.

**Solution:** Enforce invariance discipline

```lean
/-- Mark consumers using only invariant properties -/
@[invariant_only]
def my_function (x : Quotient setoid) : Result :=
  Quot.lift f (proof_of_invariance)

/-- Require naturality/well-definedness proof -/
structure Invariant {X : Type} (f : X → R) (E : X → X → Prop) :=
  (respect : ∀ {x y}, E x y → f x = f y)
```

**Linter checks:**
- Flags: `choose`, `epsilon`, `Classical.some`, `Quot.out`
- Unless: Consumer marked `@[invariant_only]` with naturality proof
- Suggests: Reformulate using `Quot.lift` or prove invariance
- Tracks: Violations in dashboard, trends over time

**This enforces the doesn't matter which principle** - if choice truly doesn't matter, prove it.

### 6.4 Extraction Pipeline

**Goal:** Proof → Executable code with certified bounds

**For Coq:**
```
Proof (in Set/Type) → Extraction command → OCaml/Haskell code → Compile
```

**For Lean:**
```
Proof (avoiding noncomputable) → Lean compiler → Native executable
```

**With quantitative content:**
```
theorem banach_fp :
  { x : X // f x = x } × (ℝ → ℕ)  -- witness + rate
    ↓ extract
  (compute_fixed_point : X → ℝ → X,  -- algorithm
   iteration_bound : ℝ → ℕ)          -- certified bound
```

**Verification:** Extracted code comes with machine-checked proof that it implements the theorem correctly.

### 6.5 Badge Generation and Documentation

From budget inference, generate visible documentation:

**Example output:**
```
Theorem: banach_fixed_point
Budget: C0 (Fully Witnessful)
Effects: None
Status: Extractable
Dependencies: 12 theorems (all ≤ C0)
```

**In library docs:**
- Color-coded badges (green=C0, yellow=C2, red=C5)
- Budget distribution graphs per module
- Dependency chains showing budget propagation
- Trend tracking (budgets over time, by contributor)

**This makes witness budgets visible and trackable**, not hidden in proof internals.

---

## Part VII: Research Program and Validation

### 7.1 Success Metrics (Falsifiable)

**Coverage Hypothesis:**
≥70% of widely-used theorems in targeted domains (optimization, separable analysis, numerical methods) can be formalized at C0–C2 with explicit moduli and rates.

**Measurement:** Formalize representative sample, measure budget distribution, compare to hypothesis.

**Automation Hypothesis:**
AI theorem provers achieve measurably higher success rates on C0–C2 statements vs classical formulations of the same result.

**Measurement:**
- Proof search time (faster with witnesses?)
- Success rate (higher with executable content?)
- Verification failures (lower with constructive?)
- Composability (easier to chain C0–C2 results?)

**Performance Hypothesis:**
Extracted algorithms from constructive proofs are competitive with hand-coded implementations.

**Measurement:**
- Wall-clock time (target: within 2× of hand-coded)
- Accuracy (comparable on standard benchmarks)
- Memory usage (reasonable overhead)
- Compilation time (tractable)

**Hygiene Hypothesis:**
Measurable decline in representative-picking violations after linter adoption.

**Measurement:**
- Violations per 1000 lines of code
- Budget distributions shift leftward (toward C0–C2)
- Refactoring patterns (how are violations fixed?)

**Portability Hypothesis:**
Proofs compile in both Coq and Lean without budget escalation.

**Measurement:**
- Cross-system formalization success rate
- Budget preservation across systems
- Demonstrates genuine constructiveness, not system artifacts

### 7.2 Threats to Validity

The following risks could undermine our hypotheses and require mitigation:

**Gaming C1 (propositional truncation):**
- **Risk:** Teams might use `∥∃x.P∥` to artificially lower budgets without proving genuine invariance
- **Symptom:** C1 usage increases but consumers don't actually respect invariance properties
- **Mitigation:** Invariance linter enforcement; require explicit naturality proofs for C1 consumption
- **Detection:** Code review for truncation usage patterns; test if removing truncation breaks consumers

**Extraction in Prop:**
- **Risk:** Algorithmic content accidentally placed in `Prop` instead of `Type`/`Set`, causing silent extraction failures
- **Symptom:** Budget appears low but extraction yields trivial/erased code
- **Mitigation:** Type system discipline; CI checks for extractable content placement; linter warnings
- **Detection:** Automated extraction tests; compare extracted code size to expected algorithmic content

**Performance parity risk:**
- **Risk:** Extracted algorithms have poor constant factors, memory overhead, or compilation bottlenecks vs hand-coded implementations
- **Symptom:** Budget appears low, extraction succeeds, but performance >2× hand-coded baseline
- **Mitigation:** Benchmark suite comparing extracted vs hand-written; profiling to identify bottlenecks; allow hand-optimized shims for critical paths
- **Detection:** Continuous performance regression testing; wall-clock and memory measurements

**Cross-system hypothesis drift:**
- **Risk:** Budget classifications diverge between Lean and Coq due to library differences, implicit vs explicit classical axioms, or extraction semantics
- **Symptom:** Same theorem assigned different budgets in different systems; portability claims fail
- **Mitigation:** Parallel formalization in both systems for case studies; explicit axiom tracking; standardized budget inference rules
- **Detection:** Cross-system formalization attempts; budget comparison reports; proof term analysis

**Addressing these proactively:** Case studies will explicitly track and report on each threat, documenting mitigation effectiveness and any hypothesis adjustments needed.

### 7.3 Two High-Signal Case Studies

**Study 1: Banach Fixed-Point Theorem**

**Deliverables:**
1. Constructive formalization (C0) with explicit convergence rate
2. Extracted solver implementation in Lean/Coq
3. Certification: Rate formula N(ε) = ⌈ln(d(x₁,x₀) / ((1-L)ε)) / ln(1/L)⌉
4. Budget tracking: Explicit C0 badge, CI enforcement
5. Comparative analysis:
   - Proof complexity (lines, dependencies, concepts)
   - Verification time (classical vs constructive)
   - Extracted code performance vs hand-written solver
   - Usability in downstream optimization applications

**Application:** Use in certified numerical optimization, compare against classical proofs that give converges eventually without rates.

**Study 2: Arzelà-Ascoli in Separable Metric Spaces**

**Deliverables:**
1. Constructive proof avoiding ultrafilters
2. Method: Total boundedness + equicontinuity + dependent choice (C2)
3. Explicit subsequence constructor with modulus
4. Extraction to working subsequence-finding code
5. Comparative analysis:
   - Classical proof structure vs constructive
   - Budget assignments and dependencies
   - Practical utility for PDE compactness arguments

**Application:** Compactness arguments in numerical PDE solving, certified subsequence extraction for function spaces.

**Optional Study 3: Compact Products via Locales**

**Deliverables:**
1. Countable products of compact metric spaces
2. Gluing method avoiding ultrafilters (C0–C2)
3. Demonstration of practical utility for function spaces
4. Connection to pointless topology and constructive analysis

### 7.4 The Bootstrapping Challenge

**Honest assessment of the barrier:**

The primary obstacle isn't philosophical disagreement about foundations - it's the **engineering activation energy** of formalizing applied mathematics constructively.

**The challenge:**
- Mathlib community (rightly) focused on formalizing all mathematics
- Existing formalizations are predominantly classical
- Constructive reformulation requires:
  - Different proof techniques (no LEM, no choice)
  - Additional technical conditions (separability, locatedness, moduli)
  - Explicit quantitative content (rates, bounds, witnesses)
  - More effort per theorem

**Why this matters:**
Someone must pay the cost of constructive formalization before benefits materialize. This is a classic bootstrapping problem.

**Our strategic framing:**

This research program is a **high-leverage bootstrap experiment**. The goal is NOT to constructivize all mathematics, but to:

1. **Prove the value proposition:** Demonstrate that automation gains and extractability benefits are large enough to justify the engineering investment

2. **Build enabling tools:** Instrumentation, linters, budget tracking that lower the barrier for everyone else

3. **Establish proof-of-concept:** Two case studies showing the full pipeline (formalize constructively → extract algorithm → measure benefits)

4. **Validate measurably:** Empirical data on coverage, automation, performance - not just philosophy

**If successful, this unlocks community-scale effort.** If automation really is better with C0–C2, and extraction really does yield practical algorithms, and tooling really does make it manageable, then the community will adopt it.

**If unsuccessful, we learn what doesn't work** and can pivot or abandon the approach. Either way, we get data rather than speculation.

---

## Part VIII: Objections and Responses

### 8.1 "This is too narrow - what about general AI alignment?"

**Objection:** You're focused on mathematical reasoning, but most AI safety challenges (value learning, deception, robustness, goal misgeneralization) have nothing to do with formal proofs.

**Response:**
Correct. We're addressing a **specific but growing subset** of AI safety:
- Automated mathematics and theorem proving
- Certified software and verified algorithms
- Scientific AI doing symbolic reasoning
- AI systems producing executable artifacts from formal specifications

As AI capabilities expand into formal reasoning domains, transparent oversight becomes more important. We're building foundations now for capabilities that are emerging.

**We are NOT claiming** to solve alignment broadly. We're solving transparent oversight for mathematical/formal reasoning specifically.

### 8.2 "Classical math works fine - why do we need constructivism?"

**Objection:** Classical mathematics has served us well for centuries. Computers can verify classical proofs successfully. Why insist on constructive foundations?

**Response:**
For **human mathematics**, classical foundations are often adequate. For **AI systems producing executable artifacts**, there's a practical difference:

**Verification alone:**
- Confirms logical correctness
- Doesn't yield algorithms
- Doesn't provide bounds
- Doesn't enable extraction or composition

**Verification + operational content:**
- Confirms logical correctness
- Yields executable algorithms
- Provides quantitative bounds
- Enables extraction, testing, composition

For AI automation and certified algorithms, we need both. This isn't philosophical preference - it's an engineering requirement for specific applications.

### 8.3 "Aren't you conflating verification with extraction?"

**Objection:** Classical proofs ARE verifiable - Lean/Coq verify them fine. You keep implying non-constructive proofs can't be verified, but that's wrong.

**Response:**
You're absolutely right, and we've been careful to distinguish:

**Verification:** Can we formally check the proof is correct?
- Classical proofs: Yes
- Constructive proofs: Yes

**Operationalization:** Can we extract executable content?
- Classical proofs: Usually No
- Constructive proofs: Yes

**The claim:** For AI safety and automation in algorithmic domains, we need **both verification AND operational content**. Constructive foundations provide both. Classical foundations provide verification but often not operationalization.

This is about extractability and executability, not verifiability per se.

### 8.4 "What about interactive/PCP proofs? You're ignoring other verification approaches."

**Objection:** Probabilistically Checkable Proofs and interactive proof systems provide efficient verification without requiring witnesses. Your framework ignores an entire approach to verification.

**Response:**
Not ignoring - acknowledging as **complementary**:

**Three verification channels:**
1. Constructive witness: Execute and verify
2. Classical proof: Verify logically but don't execute
3. Interactive/PCP: Verify succinctly via probabilistic checking

**Different properties:**
- Constructive: Best for automation, composition, extraction
- Classical: Best for pure existence where execution unnecessary
- PCP: Best for complexity theory, very large proofs, cryptographic applications

**Our focus:** For AI producing **algorithmic mathematics** (certified software, numerical methods), constructive witnesses are optimal because they provide operational content needed for execution and composition.

PCP/interactive proofs serve different purposes (efficiency, succinctness) but don't provide the extractable algorithms we need for computational applications.

### 8.5 "Lean's mathlib is classical - this is impractical"

**Objection:** The main formal mathematics library (mathlib) is predominantly classical. You're asking people to redo massive amounts of work. This is impractical.

**Response:**
We're NOT proposing to replace mathlib. We're proposing:

1. **Constructive subsets:** Explicitly mark and maintain C0–C2 subsets of mathlib
2. **New formalization:** For applied mathematics (optimization, numerical analysis), target constructive from the start
3. **Parallel development:** Constructive libraries alongside classical ones, not replacing them
4. **Tooling:** Build instrumentation that makes constructive discipline enforceable
5. **Empirical validation:** Measure if benefits (automation, extraction) justify costs

**The bootstrapping challenge section** explicitly addresses this: we're not claiming "everyone should rewrite everything," we're claiming "let's test if constructive applied math provides measurable benefits, and if so, make it easier for others to adopt."

### 8.6 "Constructive algorithms might be inefficient"

**Objection:** Even if you get an algorithm from a constructive proof, it might be terribly inefficient - exponential time, impractical space usage. Just having an algorithm doesn't mean it's useful.

**Response:**
Valid concern. This is exactly why **proof mining is essential**, not optional:

**Constructive alone:** Gives algorithms, not necessarily good ones
**Constructive + proof mining:** Extracts explicit bounds, rates, complexity

**Our requirement:** Type signatures must include quantitative content:
- Not just "witness" but "witness + convergence rate"
- Not just "algorithm" but "algorithm + complexity bound"
- Not just "approximate" but "approximate with explicit error function"

**Empirical test:** Case studies will measure performance. Target: within 2× wall-clock time of hand-coded implementations. If we can't achieve this, we'll report negative results and identify what went wrong.

We're not claiming "constructive = efficient" automatically. We're claiming "constructive + quantitative bounds = practical algorithms" is achievable for important cases.

---

## Part IX: Community and Collaboration

### 9.1 Key Research Groups

**AI Safety (Scalable Oversight):**
- Paul Christiano (Anthropic): Transparent reasoning framework
- Jan Leike (Anthropic): Scalable oversight, weak-to-strong generalization
- Evan Hubinger (Anthropic): Transparency, interpretability

**Formal Methods:**
- Jeremy Avigad (CMU): Lean development, automated reasoning
- Leonardo de Moura (AWS): Lean creator, AI integration efforts
- Kevin Buzzard (Imperial): Lean evangelism, mathematical formalization
- Georges Gonthier (Inria): Coq, large-scale formalization (Four Color, Odd Order)

**Proof Mining:**
- Ulrich Kohlenbach (TU Darmstadt): Leading proof mining program
- Quantitative extraction from classical analysis

**Constructive Mathematics:**
- Andrej Bauer (Ljubljana): Constructive mathematics, realizability
- Mike Shulman (University of San Diego): Homotopy Type Theory, synthetic approaches
- Vasco Brattka (Munich): Computable analysis, Weihrauch complexity

**AI + Theorem Proving:**
- DeepMind formal reasoning team
- OpenAI mathematical reasoning efforts
- Anthropic formal verification initiatives

### 9.2 Dissemination Venues

**AI Safety:**
- Alignment Forum (immediate, technical audience)
- AI safety workshops (NeurIPS, ICML)
- Lab seminars and reading groups

**Formal Methods:**
- ITP (Interactive Theorem Proving)
- LICS (Logic in Computer Science)
- CPP (Certified Programs and Proofs)
- Lean Together community events

**Applied Mathematics:**
- SIAM conferences (computational tracks)
- Numerical analysis venues
- Optimization society meetings

**Foundations:**
- Logic colloquia
- Reverse mathematics workshops
- Philosophy of mathematics conferences

### 9.3 Funding Opportunities

**Potential sources:**
- AI safety grants (Open Philanthropy, Long-Term Future Fund)
- NSF Formal Methods programs
- Industry labs with formal verification initiatives
- Academic positions in formal methods/verification

**Pitch angles for different funders:**
- **AI safety:** Transparent oversight infrastructure for mathematical reasoning
- **Software verification:** Certified algorithm extraction from proofs
- **Automated mathematics:** Enabling AI theorem provers with operational content
- **Scientific computing:** Verified numerical methods with explicit bounds

---

## Part X: Conclusion

### 10.1 What We've Established

**Philosophical:**
- Constructive mathematics isn't just aesthetic preference - it's about operational content
- Non-constructive existence is structurally analogous to black-box oracles in oversight
- "It doesn't matter which choice" signals we should work with invariants, not representatives
- Circles vs choice functions: different kinds of idealization (process limits vs bare assertion)

**Technical:**
- Witness budget (C0–C5) makes oracle dependence measurable and compositional
- Verification ≠ operationalization - need to distinguish and provide both
- Three verification channels (constructive, classical, PCP) serve different purposes
- Proof mining extracts quantitative content, bridging classical proofs to algorithms

**Empirical (testable):**
- Hypothesis: Much of computational mathematics works at C0–C2 with appropriate APIs
- Prediction: Lower budgets improve AI automation (more structure for search)
- Claim: Extracted algorithms can be competitive with hand-coded implementations
- Method: Case studies will validate or falsify these claims

**Strategic:**
- Connects AI safety, formal methods, and constructive mathematics communities
- Each benefits for their own reasons (oversight, extraction, modern relevance)
- Provides concrete research program with measurable milestones
- Addresses emerging need as AI capabilities expand into formal reasoning

### 10.2 What This Enables

**For AI Safety:**
- Technical specification of "transparent oversight" for mathematical reasoning
- Measurable metric (witness budget) for operational extractability
- Concrete implementation path via constructive formal mathematics
- Bridge to established formal methods community

**For Formal Methods:**
- Elevated purpose beyond software verification - alignment infrastructure
- Clear value proposition for constructive discipline (automation + extraction)
- Integration with AI safety motivation and funding
- Framework for tracking and reducing oracle dependence

**For Constructive Mathematics:**
- Modern, high-stakes motivation (AI safety and automation)
- Practical applications (certified algorithms, verified software)
- Community expansion beyond foundations specialists
- Relevance to civilizational-scale technology challenges

**For Applied Mathematics:**
- Algorithmic content from proofs, not just existence
- Explicit bounds and rates, not just asymptotic behavior
- Verified implementations with certified correctness
- Bridge to computational systems and AI automation

### 10.3 The Honest Assessment

**This is NOT:**
- A solution to all AI safety problems
- A claim that all mathematics should be constructive
- A replacement for classical foundations in pure mathematics
- A proven approach (yet - needs empirical validation)

**This IS:**
- A concrete framework for a specific but growing problem
- A testable hypothesis about automation and extraction
- A practical toolkit for making oracle dependence visible
- An opportunity to validate whether operational content matters empirically

**The bootstrapping challenge is real:** Constructive formalization costs engineering effort upfront. Success requires proving the benefits justify the investment.

**The research program is strategic:** Not trying to constructivize everything, but running a focused experiment on high-value applied mathematics to measure automation gains and extraction utility.

**The timing is opportune:** AI capabilities in formal reasoning are emerging now. Building transparent, operational foundations positions us well for safe development of these capabilities.

### 10.4 The Path Forward

**This framework is ready to build.**

The conceptual work is done. The witness budget scale is coherent. The connections are validated by multiple reviewers. The scope is honest. The metrics are falsifiable.

**What remains is engineering and empirical validation:**
1. Build the instrumentation (budget tracking, linters, CI integration)
2. Formalize the case studies (Banach, Arzelà-Ascoli with explicit rates)
3. Extract and benchmark algorithms (measure performance, compare to hand-coded)
4. Measure automation differences (AI proof search on C0–C2 vs classical)
5. Report results (positive or negative - either way we learn)

**The opportunity:**
Be among the first to explicitly connect transparent oversight frameworks to constructive mathematical foundations, demonstrate measurable benefits empirically, and provide tooling that makes operational content practical and trackable.

**The question:**
Not whether witness budgets are a useful concept (they are), but whether the automation and extraction benefits are large enough to justify the engineering investment in constructive formalization.

**The answer requires empirical work.** Let's measure it.

---

## Appendix A: Technical Definitions

### A.1 Axiom of Choice and Equivalents

**Axiom of Choice (AC):**
For any collection of non-empty sets {Sᵢ}ᵢ∈I, there exists a function f such that f(i) ∈ Sᵢ for all i.

**Equivalent principles (over ZF):**
- **Zorn's Lemma:** Every partially ordered set where every chain has an upper bound contains a maximal element
- **Well-Ordering Principle:** Every set can be well-ordered
- **Tychonoff's Theorem (uncountable):** Arbitrary product of compact spaces is compact

**Weaker principles (not equivalent to AC):**
- **Countable Choice (ACω):** AC for countable collections
- **Dependent Choice (DC):** Sequential choices from non-empty sets
- **Ultrafilter Lemma ≡ Boolean Prime Ideal:** Every filter extends to an ultrafilter (equivalent to each other, weaker than AC)

### A.2 Constructive Mathematics

**Core principle:** Existence requires construction or explicit description.

**Rejected principles:**
- **Law of Excluded Middle (LEM):** P ∨ ¬P for all propositions
- **Axiom of Choice:** In its general form
- **Double negation elimination:** ¬¬P → P (except for decidable P)
- **Proof by contradiction for existence:** Proving ∃x.P(x) by showing ¬∀x.¬P(x) leads to contradiction

**Accepted principles:**
- **Intuitionistic logic:** Constructive reasoning rules
- **Dependent Choice (DC):** Sequential choices from non-empty sets
- **Countable Choice (ACω):** Choice from countable collections (sometimes)
- **Markov's Principle:** For decidable predicates, ¬¬∃x.P(x) → ∃x.P(x) (sometimes)

**Schools of constructivism differ** on exactly which principles to accept. The witness budget framework doesn't assume one school, but tracks usage of various principles.

### A.3 Proof Assistants

**Coq:**
- Based on Calculus of Inductive Constructions (CIC)
- Constructive by default (intuitionistic type theory)
- Extraction to OCaml, Haskell, Scheme
- Large libraries (Mathematical Components, Coq stdlib)
- Axioms can be added explicitly (e.g., Classical_Prop.classic)

**Agda:**
- Dependently-typed functional programming language
- Constructive foundations (Martin-Löf type theory)
- Direct program extraction (Agda code is the program)
- Smaller ecosystem than Coq/Lean but very principled

**Lean 4:**
- Dependent type theory foundation
- Classical by default (LEM and choice axioms built-in)
- Fast compilation and elaboration
- Large growing library (mathlib4: ~150k theorems)
- Can restrict to constructive fragments with discipline
- Program extraction through Lean's compiler

### A.4 Witness Budget Levels (Formal)

Let Eff = {Classical, Trunc, ACω, DC, ULBPI, AC}

For proof term Γ ⊢ t : A, define:
- effects(t) ⊆ Eff (effects used by t)
- budget(t) = level(effects(t)) where level : P(Eff) → {C0, C1, C2, C3, C4, C5}

**Level assignment:**
- C0: effects(t) = ∅
- C1: effects(t) ⊆ {Trunc}
- C2: effects(t) ⊆ {Trunc, ACω, DC}
- C3: effects(t) ⊆ {Classical, Trunc, ACω, DC}
- C4: effects(t) ⊆ {Classical, Trunc, ACω, DC, ULBPI}
- C5: effects(t) contains AC

**Composition:** budget(f ∘ g) = max(budget(f), budget(g))

**Monotonicity:** If t uses theorem s, then budget(t) ≥ budget(s)

---

## Appendix B: Resources and References

### B.1 Foundational Books

**Constructive Mathematics:**
- Bishop, E. & Bridges, D. (1985). *Constructive Analysis*
- Troelstra, A. S. & van Dalen, D. (1988). *Constructivism in Mathematics* (2 volumes)
- Bridges, D. & Vîță, L. (2006). *Techniques of Constructive Analysis*

**Proof Mining:**
- Kohlenbach, U. (2008). *Applied Proof Theory: Proof Interpretations and their Use in Mathematics*

**Type Theory and Proof Assistants:**
- The Univalent Foundations Program (2013). *Homotopy Type Theory: Univalent Foundations of Mathematics*
- Bertot, Y. & Castéran, P. (2004). *Interactive Theorem Proving and Program Development: Coq'Art*
- Nederpelt, R. & Geuvers, H. (2014). *Type Theory and Formal Proof*

**Reverse Mathematics:**
- Simpson, S. G. (2009). *Subsystems of Second Order Arithmetic*

### B.2 Key Papers

**AI Safety and Oversight:**
- Christiano, P. et al. (2018). "Supervising strong learners by amplifying weak experts"
- Leike, J. et al. (2018). "Scalable agent alignment via reward modeling"

**Proof Mining:**
- Kohlenbach, U. (2005). "Some logical metatheorems with applications in functional analysis"
- Kohlenbach, U. & Oliva, P. (2003). "Proof mining: a systematic way of analyzing proofs in mathematics"

**Constructive Analysis:**
- Bishop, E. (1967). "Foundations of Constructive Analysis"
- Richman, F. (1990). "Intuitionism as generalization"

**Computable Analysis:**
- Weihrauch, K. (2000). "Computable Analysis"
- Pour-El, M. B. & Richards, J. I. (1989). "Computability in Analysis and Physics"

### B.3 Online Communities and Resources

**Lean:**
- Zulip chat: https://leanprover.zulipchat.com/
- Documentation: https://leanprover-community.github.io/
- Mathlib: https://github.com/leanprover-community/mathlib4
- Lean 4 manual: https://lean-lang.org/documentation/

**Coq:**
- Discourse: https://coq.discourse.group/
- Documentation: https://coq.inria.fr/
- Platform: https://github.com/coq/platform

**AI Safety:**
- Alignment Forum: https://www.alignmentforum.org/
- LessWrong: https://www.lesswrong.com/

**Proof Mining:**
- Kohlenbach's research group: https://www.mathematik.tu-darmstadt.de/~kohlenbach/

### B.4 Collaboration Opportunities

For questions, collaboration, or contributions to this framework:

**Instrumentation and tooling:**
- Lean Zulip #mathlib channel
- Contribute to witness budget implementation

**Case studies and formalization:**
- Reach out to formal methods groups
- Propose specific theorems for constructive reformulation

**Empirical validation:**
- AI labs working on theorem proving
- Researchers in automated reasoning

**Funding and support:**
- AI safety grantmakers (Open Philanthropy, LTFF)
- Formal methods funding sources (NSF, industry labs)

---

## Appendix C: Glossary

**Axiom of Choice (AC):** Principle asserting existence of choice functions without providing construction method

**Budget (Witness):** Measure of oracle/non-constructive dependence on C0–C5 scale

**Constructive Mathematics:** Mathematics requiring explicit construction or definable procedure for existence claims

**Dependent Choice (DC):** Principle allowing sequential choices from non-empty sets (weaker than full AC)

**Effect System:** Type system tracking computational effects (here: oracle/classical effects in proofs)

**Executable Content:** Operational artifacts extractable from proofs: witnesses (concrete objects), algorithms (procedures), bounds (explicit rates, error terms, moduli), and quantitative data beyond asymptotic behavior

**Homotopy Type Theory (HoTT):** Foundation treating equality as paths, types as spaces, with univalence axiom

**Law of Excluded Middle (LEM):** Principle that P ∨ ¬P holds for all propositions (rejected in intuitionistic logic)

**Operational Content:** Extractable algorithmic content: witnesses, bounds, rates, moduli from proofs

**Proof Mining:** Systematic extraction of quantitative bounds and rates from classical proofs using logical transformations

**Realizability:** Semantic interpretation of logical proofs as computational programs

**Torsor:** Space acted on freely and transitively by a group (encodes "all choices equivalent under group action")

**Ultrafilter Lemma / Boolean Prime Ideal (ULBPI):** Every filter extends to an ultrafilter; equivalent to BPI over ZF; weaker than AC.

**Verification vs Operationalization:** Checking correctness (verification) vs extracting executable content (operationalization)

**Witness:** Explicit object or algorithm satisfying an existence claim (not just proof that one exists)

**Zorn's Lemma:** In a partially ordered set where every chain has upper bound, there exists maximal element (equivalent to AC over ZF)

---

*Document Version: 2.0*
*Last Updated: 2025*
*License: CC BY 4.0*

---

**This research program is open for collaboration.**

If you're interested in:
- Contributing to instrumentation and tooling
- Formalizing case studies constructively
- Running empirical validation experiments
- Providing feedback or critique

Please reach out through the communities mentioned in Appendix B.3, or engage with the formal methods and AI safety communities working on these problems.

**The question is no longer "is this worth doing?" but "what do the measurements show?"**

Let's find out.
