# Witness Budgets for Transparent Oversight: A Constructive Basis for Verifiable AI Math

*A synthesis connecting AI safety, formal methods, and constructive mathematics*

---

**Problem:** AI systems producing mathematical proofs need both correctness (verification) and usability (executable algorithms with bounds). Classical proofs provide verification; constructive proofs provide both but aren't explicitly tracked.

**Solution:** Witness Budgets (C0–C5) — a framework to measure and track non-constructive reasoning, optimizing for AI automation and algorithm extraction, with a concrete build plan uniting AI safety, formal methods, and constructive mathematics.

---

## Status and Scope

This document presents a research framework and evaluation design for operational transparency in AI mathematical reasoning. Specific empirical validations, implementations, and case studies are described to illustrate what adequate testing would require, not as commitments to particular timelines or deliverables. The framework is designed to be testable and falsifiable; validation would require the empirical work outlined in Part VII.

---

## What's New in This Paper

Rather than reiterate the existence of constructive mathematics, this paper introduces a discipline and tooling package that makes operational transparency measurable and enforceable in practice.

- **Witness Budgets (C0–C5) with inference & CI** — A compositional effect system that tracks non-constructive power per theorem/definition and enforces thresholds in CI (novel as a systematic practice in formal methods and mathlib-style workflows).
  - *Prior:* ad-hoc norms; extraction flags; no library-wide budget telemetry.

- **Quantitative type contracts** — API signatures that require witnesses + rates/bounds, turning "existence" into executable content by construction.
  - *Prior:* Coq/Lean can extract programs, but bounds/rates are rarely enforced at the type level.

- **C1 invariance discipline** — A concrete consumer contract (@[invariant_only] + linter) that lets teams use existence results safely without representative-picking, and downgrade budgets when invariance is proved.
  - *Prior:* Informal guidance; no automated check for "don't rely on which witness."

- **Tooling to operationalize the discipline** — Budget inference pass, invariance linter, badges, and CI policy (MVP spec in §6) so projects can adopt this without rewriting math.
  - *Prior:* Extraction/proof-mining exist; no integrated pipeline tying budgets, invariance, and CI together.

- **Empirical program** — Falsifiable metrics (coverage, automation success, performance, hygiene, portability) on targeted case studies to test whether lower budgets actually improve automation and composition.
  - *Prior:* Proof mining results; limited end-to-end benchmarks on automation/composability.

**Non-goals:** We are not replacing classical math, and we do not claim constructivism solves alignment broadly. This is a focused framework for AI that must produce algorithms with certified bounds.

**Building on prior work:** This framework builds on extensive work in program extraction, realizability, proof mining, and reverse mathematics. Our novelty is systematic integration + enforcement + empirical evaluation at library scale, making constructive discipline measurable and actionable in modern proof assistant workflows.

---

## Executive Summary

For AI that produces algorithms from mathematics, we need operational transparency: not only that each proof step is formally verifiable (classical and constructive both qualify), but that the result exposes **executable content (witnesses, bounds, and rates)** for composition and audit — concrete algorithms with certified properties, not just correctness proofs.

This document argues that:
1. **Non-constructive classical mathematics** creates "oracle dependencies" that provide logical verification but resist operational extraction
2. **A graded "witness budget"** framework (C0–C5) makes oracle dependence trackable and measurable
3. **Constructive foundations with quantitative content** provide both verification and operational extractability
4. **This is testable**: Instrument proof assistants, formalize applied mathematics constructively, measure automation gains

**Core hypothesis:** We hypothesize that lower witness budgets improve automation; §7 pre-registers an evaluation framework to test this claim empirically.

**Critical distinction:** Classical proofs are verifiable — Lean and Coq check them successfully. Constructive proofs are verifiable AND operational — they yield executable algorithms and bounds. For oversight and automation, we need both properties.

**Scope:** This addresses AI systems producing *executable algorithms with quantitative bounds* from mathematical reasoning — a growing subset of AI capabilities including automated mathematics, certified software, and scientific computing. It does *not* address general AI alignment (value learning, deception, robustness), non-mathematical AI capabilities (vision, language, robotics), or pure theorem proving where execution isn't required.

---

## Target Audiences & Contribution Asks

**AI Safety Researchers:**
- Consider: When formal verification is needed, prefer C0–C2 formulations — executable witnesses improve automation
- Try: Budget-track your formal benchmarks and measure automation differences

**Formal Methods Community:**
- Try: Run the budget linter on a library subfolder, report violations and refactoring opportunities
- Contribute: Help design the instrumentation and CI integration

**Constructive Mathematics Community:**
- Help: Design quantitative API signatures with explicit moduli, rates, and bounds for applied results
- Formalize: Target C0–C2 versions of key applied theorems with extractable content

---

## Part I: The Witness Budget Framework

### 1.1 The C0–C5 Spectrum: Grading Oracle Dependence

Most mathematics isn't purely constructive or purely classical — it falls on a spectrum. The witness budget framework makes this spectrum explicit and measurable:

| Level | Name | Principles | What You Get | Extractable? | Typical Examples |
|-------|------|------------|--------------|--------------|------------------|
| **C0** | Fully Witnessful | Intuitionistic logic only | Witness + algorithm + bounds | ✓ Yes | Finite combinatorics; Banach fixed-point with explicit rate |
| **C1** | Existence-Only (invariants-only use; ∥∃x.P∥ in HoTT) | Propositional truncation | Logical existence; consumers must use invariant properties only | ✓ Consumer computations (not witnesses) | "A solution exists" where downstream uses only solution-independent facts |
| **C2** | Countable Choice | ACω, DC (sequential/countable choices) | Often extractable, works for most analysis | ✓ Often | Cauchy subsequences; separable Hilbert spaces; completeness arguments |
| **C3** | Classical Logic | LEM (excluded middle) only | Verifiable but often non-executable | ✗ Usually not | Many classical proofs that avoid choice; decidability by cases |
| **C4** | Choice Fragments | Ultrafilter Lemma ≡ Boolean Prime Ideal (ULBPI) | Domain-specific oracles | ✗ No | Stone-Čech compactification; Tychonoff for compact Hausdorff spaces |
| **C5** | Full Choice | AC ≡ Zorn's Lemma ≡ Well-Ordering Principle (over ZF) | Global arbitrary selection; minimal witness content | ✗ No | Arbitrary vector space bases; Hahn-Banach (unrestricted, general non-separable normed spaces); Tychonoff for arbitrary uncountable products |

---

**Critical: C1 extractability**

**C1 provides no witness extraction.** Only consumer computations that are explicitly proven invariant under representative choice are extractable. Propositional truncation `∥∃x.P∥` cannot be eliminated into `Type` to obtain a witness without classical choice (which would bump the budget to C3+).

**What C1 allows:** If you have `∥∃x.P x∥` and a function `f` that you prove is invariant (same result for all witnesses), then you can extract the result of `f`. The witness itself remains inaccessible.

See §6.4 for precise semantics.

---

**Key technical notes:**
- Zorn's Lemma is equivalent to full AC (over ZF), not a weaker fragment — it belongs in C5
- Ultrafilter Lemma and Boolean Prime Ideal theorem are equivalent (over ZF) — combined in C4
- **Hahn-Banach theorem:** General Hahn-Banach is not provable in ZF. Many standard proofs use Zorn's Lemma (thus use C5). However, logical strength varies by variant; several Hahn-Banach forms are strictly weaker than AC. We conservatively budget unrestricted extensions as C4–C5 depending on hypotheses (base field, normed vs. locally convex spaces, separation axioms).
- **Tychonoff's theorem has three distinct formulations:**
  1. **C5 (Full AC):** Arbitrary products of compact spaces (no Hausdorff restriction) are equivalent to AC over ZF
  2. **C4 (ULBPI):** Arbitrary products of compact **Hausdorff** spaces are equivalent to ULBPI/BPI over ZF (Kelley, 1955, General Topology, Ch. 5)
  3. **C2 (Countable):** Countable products of compact metric spaces are provable constructively with modest principles (via total boundedness + completeness). In general topological spaces, AC_ω or DC is typically used for convenient formulations. We classify standard constructive analyses of the countable case under C2

### 1.2 Budget Calculus: Compositional Tracking

**Composition rule:**
```
budget(f ∘ g) = max(budget(f), budget(g))
```

**Monotonicity:**
If theorem T uses lemma L with budget C2, then T inherits budget ≥ C2

**Refinement (C1 downgrading):**
C1→C0 downgrading applies only to *consumer* definitions marked `@[invariant_only]` with an explicit `Quot.lift`/naturality proof showing representative-independence. The producer's budget remains C1; downgrading is local to the consumer and non-compositional unless all downstream uses satisfy the invariance contract.

**Effect system formalization:**
Treat non-constructive steps as effects in a type system:
```
Effect types: [Classical, Truncation, ACω, DC, ULBPI, AC]

Proof term Γ ⊢ t : A has effect row ε

Oversight cost = f(ε) (monotone in effect budget)
```

This makes witness budgets **mechanically trackable** across library composition.

**Verification vs extraction budgets:**
We compute two budgets for each theorem/definition:

- **vBudget (verification budget):** Tracks all effects anywhere in a proof, for logical oversight. This measures what non-constructive principles appear in the proof, even if confined to `Prop`.

- **xBudget (extraction budget):** Tracks only effects that flow into `Type`/computational positions, for program extraction. This measures what non-constructive principles block extraction of executable code.

**Implementation:** Compute effects over all used constants → vBudget. For xBudget, mark nodes whose eliminations target `Type` (or whose produced constants inhabit `Type`) and restrict the effect join to only those edges that flow into computational positions. CI can enforce either or both budgets; dashboards show both badges (e.g., "C2 (xBudget), C4 (vBudget)").

**Example:** A theorem using classical reasoning only in a proof obligation (confined to `Prop`) would have vBudget = C3 but xBudget = C0, indicating that extraction is unaffected even though classical logic appears in the verification.

**Important: C0–C5 as a lossy abstraction**
The underlying effects {Classical, Truncation, ACω, DC, ULBPI, AC} do *not* form a simple total order or even a lattice with a unique meet/join. For example:
- A proof using only ULBPI (no LEM) vs. a proof using only Classical (LEM, no choice) are incomparable
- Mixtures like "Truncation + ACω" don't have a canonical position relative to "Classical alone"

The C0–C5 *scale* is a **monotone abstraction** (Galois connection) from the multi-dimensional effect space into a total order for practical dashboards and CI thresholds. The mapping is conservative:
- Multiple effect combinations map to the same C-level (e.g., `{Classical, Truncation}` vs `{ACω, DC}` might both be C3 despite different extraction properties)
- The "max" composition rule over-approximates (safe but coarse)
- Finer-grained telemetry could expose multi-label budgets (e.g., "C3, uses: {Classical, Truncation}") while retaining C-badges for simplicity
- **For power users:** Tooling should provide a "view full effect row ε" option to inspect the precise effect set when dashboard badges are insufficient for understanding extraction behavior

**Concrete example of over-approximation:**
```lean
-- Classical lemma used only in Prop, doesn't affect extraction
lemma classical_helper : P ∨ ¬P := Classical.em P  -- C3

-- Algorithm that uses classical_helper only in a proof obligation, not in computation
theorem extractable_algorithm (n : Nat) : Nat :=
  let result := n + 1
  -- Proof that result satisfies some property, using classical_helper
  have h : result > n ∨ result ≤ n := classical_helper
  result  -- Computational part is C0; classical reasoning confined to Prop

-- Current vBudget: C3 (classical reasoning appears)
-- xBudget with Prop/Type flow analysis: C0 (classical reasoning confined to Prop)
-- The classical_helper flows only into Prop (the proof h), not into the extracted result
```

This example shows why the vBudget/xBudget distinction matters: computational content is extractable (xBudget = C0) even when classical reasoning appears in proof obligations (vBudget = C3).

**Design choice:** Prioritize actionability (single CI threshold, clear badge) over perfect fidelity. Users needing precise effect tracking can inspect the full effect row ε.

### 1.3 What Budgets Tell Us

**For automation:** Lower budgets provide more handles for proof search
- C0: Can execute witnesses, verify by running
- C1–C2: Sequential structure guides search
- C3–C5: Fewer algorithmic landmarks, harder automation

**For extraction:** Only C0–C2 generally support program extraction
- C0: Direct extraction of witnesses and algorithms
- C1: Extract consumer computations when they use only invariant properties (witnesses themselves not extractable without classical choice)
- C2: Extract with countable/sequential structure
- C3+: Usually no extraction possible

**For verification:** All levels are formally verifiable
- Classical proofs verify successfully in Lean/Coq
- Verification ≠ operational content
- Both matter for practical AI systems

**Connection to "soft" vs "hard" methods:**

Mathematicians often distinguish between **soft methods** (existence arguments via compactness, Zorn's Lemma, ultrafilters, topological or order-theoretic principles) and **hard/quantitative methods** (explicit constructions with rates, moduli, and computational bounds). This distinction maps cleanly onto witness budgets:

- **C3–C5 are "soft" methods:** Prove existence via non-constructive principles; elegant and general, but provide no algorithm or rate. Typical soft tools: excluded middle arguments, Zorn's Lemma for maximal elements, ultrafilter compactness arguments.

- **C0–C2 are "hard/quantitative" methods:** Explicit constructions with computable witnesses, convergence rates, and error bounds. These methods may require additional hypotheses (separability, moduli, countable structure) but deliver operational content.

The witness budget framework makes this **methodological distinction operational and enforceable**. Quantitative API contracts (§2) are not merely philosophical preference but a systematic engineering discipline: they surface the "hard" content (rates, bounds, witnesses) at the type level, making it available for composition, automation, and extraction. This perspective explains why the framework targets C0–C2 formulations in domains where both soft and hard approaches exist: not because soft methods are wrong, but because AI systems producing executable artifacts require the operational content that only hard methods provide.

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
      d(x_n, x*) ≤ (L^n/(1-L)) · d(x_1,x_0)
      Therefore: N(ε) = ⌈ ln( d(x_1,x_0) / ((1−L)ε) ) / ln(1/L) ⌉
      Where d(x_1,x_0) is the observable distance between first two iterates
```

**What you gain:** Not just "it converges" but "it converges in exactly N iterations for tolerance ε"

This is **operational content** — the difference between knowing a solution exists and being able to compute it with certified bounds.

**Practical note:** In most applied settings, the Lipschitz constant L (or a bound on it) is either known analytically, estimated numerically, or derived from problem structure — making the C0 variant directly usable without additional theoretical overhead.

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

### 2.1 The constructivist objection to choice

The Axiom of Choice (AC) allows selecting one element from each set in an arbitrary collection, without specifying *how* to make the selections.

**AC says:** "There exists a function that picks one element from each set"
**Without providing:** Any rule, procedure, or description of that function

**The discomfort:** If I can't construct it, describe it, or approximate it, in what sense does it "exist"?

This isn't just aesthetic squeamishness — it's about **what mathematical claims should provide**.

### 2.2 Circles vs choice functions: different idealizations

**Consider circles:** We accept them as mathematical objects despite requiring infinite precision to manifest physically. Does this mean we should accept AC-dependent objects too?

**No — they're different kinds of idealization:**

**Circles (acceptable idealization):**
- Finite definition: x² + y² = r²
- Definable procedure: "all points distance r from center"
- Approximable: polygons with n sides → circle as n → ∞
- **Rates of approximation:** Error ~ O(1/n²)
- **Rule-governed idealization of a constructive process**

**AC choice functions (problematic assertion):**
- No definition (by construction — that's the point of AC)
- No procedure whatsoever
- No approximation notion (what does "close to arbitrary choice" mean?)
- No complexity characterization
- **Assertion without specification**

**Key difference:** Circles are limits of constructive processes with measurable convergence rates. AC asserts existence without any process, even idealized.

This connects to computational complexity: For circles, you can ask "how many sides to get within ε?" For AC-dependent objects, there's no analogous question — no algorithm means no computational complexity analysis is possible.

### 2.3 The "it doesn't matter which" insight

Often, when AC is invoked, the proof works regardless of which choice is made. This is revealing.

**Key observation:** If the specific choice doesn't matter for the proof, maybe we shouldn't be "choosing" at all — we should be working with the **structure of the space of possibilities**.

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

## Part III: From oversight to automation — logical vs operational transparency

**Scope note:** This section concerns automation and transparency in formal proof systems and mathematical reasoning, not general AI alignment. The witness budget framework addresses a specific subset of AI capabilities: systems producing executable artifacts from mathematical specifications.

### 3.1 Christiano's transparent oversight framework

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

### 3.2 From oversight to operational transparency

Christiano's framework motivates a broader requirement: **oversight needs two kinds of transparency.**

**Logical transparency:** Every inference is checkable — each proof step can be formally verified.
- Classical proofs: ✓ (Lean/Coq verify them successfully)
- Constructive proofs: ✓ (also formally verifiable)

**Operational transparency:** Artifacts are executable and composable — witnesses, algorithms, bounds can be extracted and used.
- Classical proofs (C3-C5): ✗ (usually no extractable content)
- Constructive proofs (C0-C2): ✓ (witnesses + rates extractable)

**Witness budgets measure operational transparency.** Lower budgets → more witnesses/rates → better extraction, composition, and search structure.

**The connection to AI automation:**

In Christiano-style oversight, decomposition only becomes actionable when subclaims produce artifacts we can run or compose. For AI systems producing **algorithmic mathematics** (certified software, numerical methods, automated science), we need both forms of transparency:

1. **Logical transparency:** Each proof step is checkable (both classical and constructive provide this)
2. **Operational transparency:** Witnesses, algorithms, bounds extractable (typically requires constructive formulations)

**This isn't about replacing classical proofs generally** — it's about recognizing that for domains where AI must produce executable artifacts, operational transparency is an engineering requirement, not a philosophical preference.

### 3.3 Verification vs operationalization: the key distinction

**What we mean by "verifiable":**
Classical proofs ARE verifiable — Lean and Coq successfully check their correctness. Every step can be formally verified. This is not in question.

**What we mean by "operational":**
Operational content means extractable:
- Witnesses (concrete objects satisfying existence claims)
- Algorithms (procedures to compute results)
- Bounds (explicit rates, error terms, moduli)
- Quantitative data (not just asymptotic behavior)

**The two-dimensional space (both axes required for deployable math-to-code):**

| | Verifiable | Operational |
|---|---|---|
| **Classical (C3–C5)** | Yes | No (usually) |
| **Constructive (C0–C2)** | Yes | Yes |

**For AI safety and automation:**
- **Verification alone** confirms correctness but doesn't enable execution, composition, or algorithmic search
- **Operational content** enables extraction, testing, composition into pipelines, and provides algorithmic "landmarks" for proof search

**One-liner:** "We track correctness with verification and usability with operational content."

### 3.4 Why this matters for AI mathematics

**Hypothesis H1 (Automation):** We hypothesize that lower witness budgets (C0–C2) improve automated proof success and efficiency relative to classically equivalent statements.

This is not obvious — classical proofs can be shorter and sometimes easier for current models trained on predominantly classical corpora. A rigorous evaluation framework is outlined in §7.1 to measure this effect directly. For this approach to be credible, results would need to be reported regardless of whether they confirm or refute the hypothesis.

**Mechanistic rationale:**

1. **Execution-prunable witnesses (CEGIS-style pruning).** When existentials live in Type (C0–C2), candidate witnesses can be run and falsified locally. This adds a cheap, ground-truth rejection test at many nodes of the search tree, reducing effective branching. In dependent type theory, `∃ x, P x` at constructive levels becomes a Σ-type whose inhabitant `(x, p)` can be partially validated by computation (normalization + running x) before finishing the logical part p. This supplies a local verifier for many search nodes; in proof-search terms it's a low-cost refutation oracle that reduces branching.

   **Limitation:** This mechanism only applies when (a) the witness type is enumerable/executable (`∃ x : Nat, P x` can enumerate and test; `∃ x : Real, P x` or `∃ f : Nat → Nat, P f` generally cannot), and (b) the property is efficiently checkable. This may apply to a smaller fraction of mathematical proofs than initially expected. Additionally, current proof search in Lean doesn't actually execute candidate witnesses during search (unlike CEGIS-style program synthesis), so realizing this benefit would require modifying proof search infrastructure — a non-trivial engineering effort. The hypothesis is that this mechanism *could* improve automation if implemented, but it's not automatic from constructive structure alone.

2. **Sequential structure as search constraints.** DC/ACω yield program shape (Σ/Π structure, recursion over ℕ). This constrains the synthesis space (fewer admissible terms) and narrows tactic choices.

3. **Denser learning signal.** Constructive proofs include witness programs and quantitative terms (rates, moduli), yielding richer supervision for gradient updates than purely logical endpoints (more tokens with semantic alignment).

4. **Composable artifacts.** Witnesses/bounds create typed interfaces between lemmas, enabling pipeline assembly and reuse (fewer dead-ends, more reusable subproofs). Conversely, Prop-only existentials provide no executable handle, so search proceeds in a higher-entropy space relying on tactic heuristics alone.

**Predictions:**
- **P1 (pass@k↑):** Higher pass@k on C0–C2 formulations of the same result
- **P2 (steps↓):** Fewer backtracks / lower tactic steps per solved goal
- **P3 (exec-prune↑):** Better ablations when "execute-to-prune" is enabled
- **P4 (composition↑):** Higher success on long chains (witnesses feed forward)

**Why we expect this to matter:**
- AI systems using proof assistants for mathematical reasoning must produce verifiable artifacts
- Proof search could benefit from executable witnesses (enabling candidate testing)
- Compositional reasoning requires outputs that can feed forward into subsequent steps
- Lower budgets provide more computational "handles" for search algorithms

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

### 3.5 How this unifies three communities

This synthesis provides missing motivation across three traditionally siloed fields:

**AI Safety → Deeper "Why" for Formal Methods**
- Current view: "Use formal verification as a tool"
- With framework: "Need constructive foundations as paradigm"
- Explains: Why operational content matters structurally, not just practically
- Impact: Connects scalable oversight to mathematical foundations

**Constructive Mathematics → Modern Relevance**
- Current view: "Philosophically purer but niche concern"
- With framework: "Safety requirement for transparent AI"
- Explains: Century-old work becomes relevant to safe algorithmic reasoning at scale
- Impact: Makes constructive research directly relevant to AI capabilities

**Formal Methods → Existential Purpose**
- Current view: "Good for critical software verification"
- With framework: "Foundation for safe algorithmic reasoning at scale"
- Explains: Not just a tool but infrastructure for AI oversight
- Impact: Elevates from specialized application to core AI safety infrastructure

**Important caveat:** These communities care about witness budgets for somewhat different reasons:
- AI safety: Extractability for oversight and algorithmic composition
- Constructive math: Ontological commitments (what exists vs what's definable)
- Formal methods: Certified algorithm extraction and complexity bounds

The framework helps all three, but through distinct mechanisms relevant to each field's concerns.

---

## Part IV: Proof mining and quantitative content

### 4.1 Constructive proofs are not necessarily practical without bounds

**Critical caveat:** Constructive proofs yield algorithms, but not necessarily *good* algorithms.

**Example:**
```
Theorem: ∀x. P(x) ∨ ¬P(x)
Proof: By exhaustive search over all x, decide which holds
```
- Constructive: Yes (explicit algorithm exists)
- Practical: No (may require exponential or infinite time)

**The gap:** Constructivity gives existence of algorithm, not complexity bounds.

**Solution:** **Quantitative proof mining** — systematically extract:
- Convergence rates (not just "converges")
- Error bounds (not just "approximates")
- Moduli of continuity (not just "continuous")
- Sample complexity (not just learnable)
- Iteration counts (not just "eventually")

### 4.2 Kohlenbach's proof mining program

**Core thesis:** Most classical analysis theorems have hidden constructive content — explicit bounds and rates that the classical proof obscures.

**Method:** Use logical transformations (realizability, Dialectica interpretation, functional interpretation) to systematically extract effective bounds from non-constructive proofs.

**Key results (examples):**

**Fixed-point theory:**
- Classical: "Iterates converge to fixed point"
- Extracted: N(ε) = ⌈ln(d(x₁,x₀) / ((1-L)ε)) / ln(1/L)⌉ iterations for tolerance ε
- From: Contraction constant L, observable initial iterate distance d(x₁,x₀)
- Reference: Kohlenbach (2008), *Applied Proof Theory*, Chapter 10

**Ergodic theory:**
- Classical: "Time averages converge to space averages"
- Extracted: Metastability rates (effective convergence moduli)
- Applications: Computational ergodic theory
- Reference: Avigad, Gerhardy, & Towsner (2010), "Local stability of ergodic averages"

**Nonlinear analysis:**
- Classical: "Iterative scheme converges"
- Extracted: Explicit rates for Krasnoselski-Mann iterations
- Applications: Optimization algorithms
- Reference: Kohlenbach & Leuștean (2009), "Asymptotically nonexpansive mappings in uniformly convex hyperbolic spaces"

**Optimization:**
- Classical: "Gradient descent converges"
- Extracted: Convergence rates depending on Lipschitz constants
- Applications: Certified machine learning
- Reference: Kohlenbach (2008), Chapter 17; proof mining yields explicit moduli of convergence

**The bridge:** Proof mining connects classical applied mathematics to executable, verifiable algorithms with certified bounds. This is exactly what AI systems need for transparent algorithmic reasoning.

### 4.3 Quantitative content as API contract

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

**Coq parallel (generality beyond Lean):**
```coq
Theorem exists_fixed_point
  (f : X -> X)
  (L : R) (hL : L < 1)
  (contract : forall x y, dist (f x) (f y) <= L * dist x y) :
  { x : X & f x = x } * (R -> nat).  (* witness + rate *)
```

The same discipline applies across proof assistants: quantitative content as type-level contract, not optional documentation.

---

## Part V: Applied mathematics case studies

### 5.1 Where high budgets actually matter

**Our working hypothesis:** Much of computational mathematics can be reformulated at C0–C2 with appropriate APIs and quantitative signatures. The case studies below will test this empirically.

**Tier 1: Genuinely needs high budget (C4–C5)**
- Hahn-Banach theorem (unrestricted formulations for general non-separable normed spaces; strength varies by variant)
- Tychonoff theorem (arbitrary products of compact spaces need C5; compact Hausdorff products need C4)
- Every vector space has basis (infinite-dimensional, non-separable)
- Algebraic closure (general fields — uses Zorn, hence C5)

**Tier 2: Often needs C2–C3, constructive workarounds exist**
- Functional analysis (many results, but separable spaces reduce budget significantly)
- General topology (compactness arguments, but constructive for countable/metric spaces)
- Some optimization existence theorems (classical proofs exist, but algorithms often computable)

**Tier 3: Appears to need AC, actually works at C0–C2**
- Much of standard undergraduate analysis when reformulated with explicit moduli (completeness, sequential compactness)
- Differential equations (existence/uniqueness for nice cases with constructive inputs)
- Probability theory (on separable spaces, many standard constructions use ACω/DC; some advanced results need stronger choice)
- Most numerical mathematics (inherently finite-dimensional or countable)

**The measurement challenge:** This hypothesis could be tested by formalizing representative theorems in targeted domains (optimization, separable analysis) and measuring what percentage achieve C0–C2 with explicit moduli.

### 5.2 Case study 1: Hahn-Banach theorem

**Classical statement (typically C5, varies by formulation):**
"Every continuous linear functional on a subspace of a normed space can be extended to the whole space, preserving norm."

**Where it's used in practice:**
- Signal processing: Reconstruct full signal from partial measurements
- Convex optimization: Separating hyperplane theorem → duality theory → SVM, linear programming
- Distribution theory: Defining generalized functions (Dirac delta on test functions)
- Economics: Price theory, supporting hyperplanes for preference sets

**Why choice principles are needed:**
Extension isn't canonical — infinitely many valid norm-preserving extensions exist with no rule for distinguishing them. Standard proofs use Zorn's Lemma (equivalent to AC over ZF, thus C5). Note: Hahn-Banach is not provable in ZF, but logical strength varies by variant (some are strictly weaker than AC). This case study focuses on the unrestricted formulation.

**Important distinction:** Hahn-Banach provides *extension of linear functionals*, not vector space *bases*. These are separate AC-dependent results:
- **Hahn-Banach:** extends functionals (maps V → ℝ) from subspaces to whole space
- **Hamel basis theorem (§5.3):** asserts existence of bases (linearly independent spanning sets) for arbitrary vector spaces

Both require AC for general spaces, but for different reasons and with different constructive alternatives. Avoid conflating them.

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
- Classical: Unrestricted generality — works for ALL normed spaces, ALL functionals
- Constructive: Works for nice enough spaces (separable, located, with moduli)
- Trade-off: Lose some generality, gain executable algorithms with bounds

**Practical impact:** Most applications in computational settings already have the structure needed for C0–C2 versions. The full generality is rarely used in practice.

### 5.3 Case study 2: vector space bases

**Classical theorem (C5):** "Every vector space has a basis (maximal linearly independent set)"

**Where it matters:**
- Quantum mechanics: Spectral theorem requires eigenbases for operators
- Fourier analysis: Function spaces need basis expansions
- Linear algebra: Coordinate systems for abstract spaces
- Control theory: State space representations

**Why full AC is needed:**
For infinite-dimensional spaces without computable structure (e.g., ℝ regarded as a vector space over ℚ), constructing a basis requires infinitely many arbitrary choices. Even specifying one basis element may require AC.

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

### 5.4 Case study 3: Tychonoff's theorem

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
- Pointless topology — work with open sets directly, not points
- Tychonoff holds constructively in locale/topos framework
- Covers: Theoretical topology, some computer science applications
- Budget: C0–C1 (synthetic topology)
- Trade-off: Can't extract explicit points for computation, less intuitive

**The gap:**
- Classical: Arbitrary products compact → existence theorems for equations, equilibria
- Constructive: Countable products + locale theory (abstract) OR uncountable products lose compactness
- Practical impact: Many applications can be reformulated with countable approximations

### 5.5 Case study 4: economic equilibrium

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
- Use computational fixed-point algorithms (Scarf, Lemke-Howson, continuation methods) yielding approximate equilibria with explicit error bounds ⇒ C0 (fully algorithmic)
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

## Part VI: Implementation and instrumentation

### 6.1 Proof assistant reality check

**Coq/Agda:**
- Constructive by default (intuitionistic type theory)
- Can extract programs from proofs (Set/Type, not Prop)
- Classical axioms (LEM, AC) can be added explicitly if needed
- Natural fit for constructive mathematics
- Extraction consideration: Content in Prop erases — keep algorithmic content in Set/Type

**Lean 4:**
- Classical by default (LEM and choice axioms available in logic)
- Main library (mathlib4) heavily uses classical reasoning
- Can restrict to constructive fragments with discipline:
  - Avoid `classical`, `choice`, `noncomputable` keywords
  - Mark classical content explicitly with attributes
  - Use CI rules to enforce constructive discipline in specific directories
  - Allowlist escape hatches for specific theorems
- Extraction: Requires staying out of `noncomputable` and keeping witnesses in Type (not Prop)

**Reality check:**
Most formalized mathematics today is classical (especially mathlib). Constructive formalization is **additional work** requiring:
- Different proof techniques
- Explicit moduli and bounds
- More technical conditions
- Careful tracking of choice usage

**This is the primary barrier** — not philosophical disagreement, but engineering cost.

### 6.2 Budget instrumentation design

**Minimal Lean 4 implementation (proposed design):**

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

**Inference approach (design specification):**

The budget tracker walks the compiled environment, computing `effects(c)` for each constant by examining its `usedConstants` closure post-elaboration.

**Lean 4 detection targets:**
- **`Classical.*` namespace:** `Classical.em`, `Classical.choice`, `Classical.some`, `Classical.choose`
- **Decidability without instances:** `Classical.decEq`, `Classical.dec`, `Classical.decPred`, etc. (common source of silent classicality)
- **`by_cases` without `Decidable` instance in scope** (implies classical case split)
- **`noncomputable` markers:** `noncomputable def`, `noncomputable section` blocks (indicator but not definitive - requires term inspection)
- **Choice/epsilon operators:** `Classical.epsilon`, Hilbert choice if introduced, any mathlib `choose`/`obtain` sugar resolving to classical choice
- **Skolemization helpers:** Detection of choice-dependent witnesses
- **Curated axiom lists:** Zorn's Lemma (`Zorn.zorn`), Ultrafilter Lemma (`Filter.ultrafilter`), AC-dependent mathlib constants

**Important caveat:** `noncomputable` is a useful heuristic but not a proof. It can indicate extraction blockage due to non-decidability without implying classical reasoning (e.g., real arithmetic may be `noncomputable` for computational reasons). Budget inference relies primarily on proof-term scanning for explicit classical/choice artifacts; `noncomputable` alone does not bump the budget.

Implicit classical reasoning is detected via typeclass-synthesized `Classical.propDecidable` instances and tactic-inserted classical lemmas visible in the compiled term. Composition is handled via transitive closure: if `f` calls `g`, `effects(f)` includes `effects(g)`. The inference is conservative — may over-approximate — and can be refined via explicit `@[witness_budget]` annotations.

**Implementation status:** This describes the intended design. Actual implementation would need to handle edge cases such as classical reasoning hidden in imported definitions, universe polymorphism interactions, and tactic-generated proof terms. The algorithm would require validation and refinement during a proof-of-concept phase. A complete empirical study would include published implementation details. An MVP implementation as an open-source Lean 4 plugin would be a natural first proof-of-concept.

**Technical details (effect semantics):**
- Effects compose via union (max in the C0–C5 lattice): `effects(f ∘ g) = effects(f) ∪ effects(g)`
- Higher-order: `effects(λx.b)` includes effects of `b` and any captured terms; `effects(f a) = effects(f) ∪ effects(a)`
- Transitive dependencies: budget computed over `usedConstants` closure (post-elaboration)
- Model-theoretic principles: Łoś's theorem, ultraproducts, compactness, and saturation are curated as C4/C5 (ULBPI/AC) via explicit axiom lists
- Budgets are cached per module; imported modules contribute their cached budgets to local inference

**Future work:** A full formalization of the effect system semantics requires addressing (see Part X for extended discussion):
- Soundness/completeness lemmas relating syntactic budget inference to semantic extractability
- Precise handling of impredicative Prop vs Type distinctions in dependent type theory
- Effect polymorphism and universe polymorphism interactions
- Tactic-generated proof terms (where classical reasoning may be introduced implicitly)
- Budget inference for metaprogramming and elaboration-time computation

**Impredicativity note:** Lean and Coq's impredicative `Prop` universe introduces non-constructive aspects orthogonal to witness budgets. Impredicative quantification (defining a proposition by quantifying over all propositions including itself) can hide computational content even without LEM or AC. For example, `∀ P : Prop, P → P` is impredicative and erases during extraction. The witness budget framework focuses on oracle effects (LEM, AC variants); full constructive discipline would also require predicative foundations or explicit tracking of impredicative definitions. This represents a separate axis of constructive content beyond the C0–C5 scale, potentially addressable via universe level tracking or predicativity linters in future work.

**Linter behavior for impredicativity:** The current budget linter *does not* demote or penalize a proof that merely quantifies over `Prop`; we conservatively treat impredicative definitions as budget-neutral (neither bumping nor reducing budget). A proof using impredicative `Prop` receives the same budget as it would in a predicative formulation, unless it also invokes LEM/AC/etc. This is a pragmatic choice; a stricter discipline would flag impredicativity separately.

The pragmatic inference algorithm described here is conservative (may over-approximate budgets) and refinable via explicit `@[witness_budget]` annotations. It provides actionable telemetry for library-scale adoption while these theoretical questions are resolved.

**Inference heuristic (summary):**
Scanner walks compiled proof term, flags uses of:
- `classical`, `Classical.choice`, `Classical.some`, `Classical.em`
- `noncomputable` (usually indicates classical reasoning)
- `Quot.out` without `Quot.lift` (representative picking)
- Known choice lemmas from mathlib (Zorn, Ultrafilter, etc.)
- Implicit `Classical.propDecidable` via typeclass synthesis

**Tactic-level budget enforcement (proposed):**

To handle tactics that implicitly insert classical reasoning, the framework would need:

**Allowlist of budget-safe tactics:**
- `intro`, `apply`, `exact`, `constructor`, `cases`, `induction` (when applied to decidable types)
- `rfl`, `rw`, `simp` (when restricted to constructive lemmas)
- `ring`, `omega`, `linarith` (decision procedures for decidable domains)
- Tactics guaranteed not to invoke `Classical.choice` or LEM

**Denylist of tactics that always bump budget:**
- `by_contra`, `push_neg` (require LEM or double-negation elimination)
- `classical` (explicitly invokes classical reasoning)
- `by_cases` without explicit `Decidable` instance (inserts `Classical.propDecidable`)
- `choose`, `obtain` without witnesses (may use AC implicitly)

**Tactic linter (design specification):**
- Monitor elaborated proof terms for unexpected classical axiom usage
- Flag when tactics insert `Classical.propDecidable` or choice axioms without explicit annotation
- Suggest constructive alternatives: `by_cases (decidable_of ...)` instead of bare `by_cases`
- Track "budget surprise" metrics: cases where inferred budget exceeds user expectation

**Limitation:** This requires tactic-level instrumentation and may have false positives. The current post-elaboration approach is conservative (over-approximates) but avoids needing to instrument every tactic. A full implementation would need both approaches: post-elaboration scanning (conservative baseline) + tactic-level linting (precise but more invasive).

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

### 6.3 Invariance linter (proposed)

**Problem:** Code uses `choose`, `some`, `Classical.some` to pick representatives, but doesn't prove choice is irrelevant.

**Solution:** Enforce invariance discipline

**Invariance enforcement (design specification):**

The linter would flag raw representative-picking (`Classical.some`, `Quot.out`, `choose`) unless the consumer factors through `Quot.lift`/`Quotient.lift` with a supplied congruence proof, or is marked `@[invariant_only]` with an explicit invariance lemma. This makes the "doesn't matter which" principle mechanically checkable: if the choice truly doesn't matter, the naturality proof should exist.

```lean
/-- Mark consumers using only invariant properties -/
@[invariant_only]
def my_function (x : Quotient setoid) : Result :=
  Quot.lift f (proof_of_invariance)

/-- Require naturality/well-definedness proof -/
structure Invariant {X : Type} (f : X → R) (E : X → X → Prop) :=
  (respect : ∀ {x y}, E x y → f x = f y)
```

**Linter checks (proposed behavior):**
- Would flag: `choose`, `epsilon`, `Classical.some`, `Quot.out`
- Unless: Consumer marked `@[invariant_only]` with naturality proof
- Would suggest: Reformulate using `Quot.lift` or prove invariance
- Would track: Violations in dashboard, trends over time

**This would enforce the doesn't matter which principle** — if choice truly doesn't matter, prove it.

### 6.4 Extraction pipeline

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

**C1 (Truncation) consumption semantics:**

**Critical distinction:** C1 is **consumable by invariant clients**, not **extractable for witnesses**. Propositional truncation `∥∃x.P∥` does **not** permit extracting a witness into Type without classical choice. What C1 enables is computing results that don't depend on *which* witness exists.

**System-specific C1 mappings:**

| System | Truncation representation | Extraction behavior | Invariance mechanism |
|--------|---------------------------|---------------------|----------------------|
| **Lean 4 / mathlib** | `Nonempty α : Prop` (truncation proxy) | Consumers must not eliminate to `Type` without choice | Require `Quot.lift` proofs for invariance; flag `Quot.out` usage |
| **Coq (CIC)** | `exists x, P x` in `Prop` (or explicit squash types) | Extraction erases `Prop`; content must be in `Set`/`Type` | Use `sig` for witnesses; no eliminator from `Prop` truncation to `Set` without classical principles |
| **Agda** | Propositional truncation (postulate or HIT) | Same `Prop`/`Set` separation as Coq | No eliminator from propositional truncation to `Set` without postulates |

**Key constraint across all systems:** Eliminating truncation into computational types requires choice principles, which would bump the budget to C3+.

**In Coq/Agda detail:** Propositional truncation `∥∃x.P∥` erases to unit during extraction. Consumers cannot extract a witness, but can:
1. Compute results that use only invariant properties (properties true for all witnesses)
2. Factor computations through quotients via `Quot.lift` with a congruence proof
3. Extract the consumer's result (not the witness) because it doesn't depend on representative choice

**What extraction yields:**
- ✗ Cannot extract: a specific witness satisfying P
- ✓ Can extract: a result computed from invariant properties only
- The extracted code runs *without* choosing/computing any witness

**Example: Invariant consumption (not witness extraction):**
```coq
(* Producer: C1 budget - provides truncated existence *)
Axiom exists_root : ∥{x : R | x * x = 2}∥.

(* Consumer computes a result using ONLY the existence, not the value *)
Definition root_exists_bool : bool := true.  (* just witnesses the existence *)

(* This is extractable because it doesn't need the witness value *)
(* Extraction yields: let root_exists_bool = true *)

(* Invalid example: trying to extract the witness itself *)
(* Definition get_root : R := ... exists_root ...  -- Cannot eliminate ∥·∥ into Type! *)
```

**Concrete Lean 4 example:**
```lean
-- Producer: provides truncated existence (C1)
axiom exists_midpoint : ∀ (a b : ℝ), a < b → Nonempty {x // a < x ∧ x < b}

-- Consumer: proves result is invariant under choice of midpoint
def interval_width (a b : ℝ) (h : a < b) : ℝ := b - a

theorem width_independent_of_midpoint (a b : ℝ) (h : a < b)
  (x y : {x // a < x ∧ x < b}) :
  interval_width a b h = interval_width a b h := rfl

-- Extraction succeeds: width is computable WITHOUT picking a specific midpoint
#eval interval_width 0 10 (by norm_num : (0 : ℝ) < 10)  -- 10

-- Key: invariant_only means we CAN'T do this (would bump budget to C3):
-- def bad_use (a b : ℝ) (h : a < b) : ℝ :=
--   (Classical.choice (exists_midpoint a b h)).val  -- ✗ blocked by linter
```

This example shows:
1. Producer provides `Nonempty` (truncation), asserting existence without constructing a witness
2. Consumer (`interval_width`) computes a result using *only* invariant data (a, b, h) — never references the midpoint
3. Extraction succeeds: extracts `interval_width`, *not* any midpoint witness
4. Linter blocks attempts to extract witnesses directly (would require classical choice and bump budget to C3+)

**Key insight:** C1 "extractability" means *the consumer's computation is extractable*, not *the witness is extractable*. The truncated existence serves as a logical precondition (proof obligation) but contributes no runtime data.

**Metatheorem (informal):** If a consumer function `f` factors through a quotient (via `Quot.lift` or equivalent) with a proof that the result is independent of representative choice, and `f`'s return type is in `Type` (not `Prop`), then `f` is extractable with budget ≤ max(producer's budget with truncation treated as neutral, other dependencies). The witness itself is never extracted; only `f`'s computed result.

**Mechanization status:** This discipline is enforceable via the invariance linter (§6.3) requiring explicit `Quot.lift` + congruence proofs. A full semantic model (e.g., PER semantics relating syntactic C1 annotations to extractability properties) remains future work. The pragmatic implementation treats C1 as "consumable under invariance contract" rather than claiming witness extraction.

---

**Formal statements (for future mechanization):**

**No-elimination lemma (Truncation → Type):**
In the absence of classical choice axioms, propositional truncation `∥∃x:A. P x∥ : Prop` cannot be eliminated into `Type` to yield a computational witness of type `{x : A // P x} : Type`. Any such elimination requires invoking `Classical.choice` or equivalent, which bumps the witness budget to ≥ C3.

*Precise formulation (Lean 4):*
There exists no term `extract : ∀ {A : Type} {P : A → Prop}, Nonempty {x // P x} → {x // P x}` that is definable without using `Classical.choice`, `Classical.inhabited_of_nonempty`, or equivalent axioms. Any implementation of such a term necessarily increases the witness budget.

*Analogue in HoTT:* The propositional truncation modality `∥-∥ : Type → Prop` does not admit an eliminator into `Type`; the universal property only permits eliminations into `Prop`. See HoTT Book §3.7 for the formal statement.

---

**Invariant-consumption metatheorem (informal):**
Let `E` be an equivalence relation on type `A`, and let `f : A → R` be a function with return type `R : Type`. If:
1. There exists a truncated existence claim `h : Nonempty A` (C1), and
2. `f` is defined via `Quot.lift g respect_proof` where `respect_proof : ∀ x y, E x y → g x = g y`, and
3. The result type `R` is in `Type` (not `Prop`),

then the consumer function `f` is **extractable with the truncation treated as budget-neutral**. That is:
```
budget(f) ≤ max(budget(dependencies of g), C0)
```

The witness itself from `h : Nonempty A` is never extracted; only the invariant computation `g` (proven independent of representative choice) is extracted.

*Mechanization requirement:* To enforce this discipline, the invariance linter must recognize `Quot.lift` applications and verify the accompanying congruence proof. Functions consuming truncated existence without an explicit invariance proof must retain the producer's C1 budget or higher.

---

### 6.5 Badge generation and documentation (proposed)

From budget inference, the system would generate visible documentation:

**Example output:**
```
Theorem: banach_fixed_point
Budget: C0 (Fully Witnessful)
Effects: None
Status: Extractable
Dependencies: 12 theorems (all ≤ C0)
```

**In library docs (envisioned features):**
- Color-coded badges (green=C0, yellow=C2, red=C5)
- Budget distribution graphs per module
- Dependency chains showing budget propagation
- Trend tracking (budgets over time, by contributor)

**This would make witness budgets visible and trackable**, not hidden in proof internals.

### 6.6 Practical adoption path

**How does this land in mathlib without a fork?**

The framework is designed for incremental adoption without breaking changes to existing formalization efforts:

**Dual-rail strategy:**
- Keep classical lemmas in place (no breaking changes to existing mathlib)
- Add budgeted constructive variants with quantitative signatures
- Both versions can coexist; users choose based on application needs
- Classical → constructive via added hypotheses (rates/moduli as inputs)
- Constructive → classical by erasing witnesses (always possible, loses operational content)
- **Maintenance overhead mitigation:** Link theorems via `@[witness_of classical_lemma]` attribute; share statements via wrappers/instances; prioritize "constructive islands" (optimization, separable analysis) rather than library-wide duplication

**Assessment of dual-rail burden:** Even with linking attributes and shared infrastructure, maintaining both classical and constructive variants will increase maintenance costs. **API drift** is inevitable — when classical lemmas are refactored, constructive variants must be updated in sync, or the pairing breaks.

**Concrete drift scenario:** Developer refactors classical `continuous_function_has_max` to add a new `Bounded` hypothesis. They update all downstream classical proofs but don't know/care about the constructive variant. The constructive version lags, automated statement-sync checks flag the divergence, but nobody prioritizes fixing it for weeks. Eventually, someone must reconcile diverged APIs, often requiring non-trivial proof adjustments. Multiply this across dozens of theorem pairs and the coordination overhead compounds.

Conservative estimate: **~1.3–1.5× maintenance overhead** per theorem pair based on similar dual-API systems in other libraries (e.g., sync/async Rust APIs, typed/untyped Python). This overhead is **only justifiable** if automation gains, extraction benefits, or application value exceeds the engineering cost. **Pilot testing** the dual-rail approach on a small module (e.g., `Mathlib.Topology.MetricSpace.Contracting`) with explicit tracking of maintenance friction (PR conflicts, update lag, contributor complaints) is essential before scaling. If pilot data shows unsustainable overhead, the framework should pivot to **constructive-only sublibraries** rather than library-wide dual-rail.

**Budget overlays:**
- Per-directory thresholds configured in `witness_budget.toml`
- PRs can exceed thresholds with `budget:justify` label + explanation
- CI blocks increases without justification, but allows local overrides
- Gradual tightening as constructive alternatives become available

**Constructive islands:**
- Start in well-scoped domains: separable analysis, optimization, numerical methods
- Publish badges & dashboards showing coverage and trends
- Create "extractable" subcollections that guarantee operational content
- Build proof-of-concept applications (certified solvers, verified algorithms)

**Gradualism and interoperability:**
- Allow `@[witness_budget]` annotations on individual theorems (opt-in)
- Local lints can be enabled per-file or per-directory
- Strict CI enforcement can be phased in after community buy-in
- Classical dependencies don't block constructive downstream use (budget inheritance tracks accurately)

**Community incentives:**
- Badge systems reward low-budget contributions
- Extraction showcases demonstrate practical value
- Automation benchmarks provide empirical validation
- Grant/funding opportunities for constructive formalization work

**Key principle:** The framework should make constructive discipline *visible* and *rewarded* without making classical formalization *impossible* or *penalized*. Both approaches serve different purposes; the tooling helps users make informed choices.

---

**Adoption costs and risks:**

Introducing this framework at scale involves real engineering costs and risks:

1. **Dual-rail maintenance burden:** Maintaining both classical and constructive variants increases library surface area and contributor workload
2. **Invariance-proof engineering:** Proving that choice "doesn't matter" (for C1 downgrading) requires substantial additional proof effort
3. **Contributor retraining:** Community members must learn constructive proof techniques, explicit modulus construction, and quantitative API design
4. **CI friction:** Budget enforcement may block PRs or create friction in contribution workflows
5. **Scope boundary risks:** Without clear delineation of "constructive islands," the dual-rail approach may expand beyond tractable boundaries

**Mitigations:**
- Link paired theorems via `@[witness_of]` attributes for coordinated maintenance — the attribute would link constructive variants to their classical counterparts, enabling automated checks that theorem statements remain synchronized (e.g., when classical version gains a new hypothesis, constructive version is flagged for review) and providing bidirectional navigation in documentation
- Target high-value "constructive islands" (optimization, separable analysis) rather than library-wide duplication
- Opt-in per-directory enforcement with explicit justification mechanisms for budget overruns
- Badge incentives and extraction showcases to demonstrate value
- Publish PR-friction metrics alongside coverage data to track adoption costs empirically

**Success thresholds:** For this approach to be viable, we should observe:
- ≥70% C0–C2 coverage in targeted domains
- <15% PR rejection rate due to budget violations (after initial adoption period)
- Measurable automation improvements (pass@k, tactic steps) justifying the dual-rail overhead
- Extraction success rate >80% for C0–C2 formalized theorems
- **Contributor engagement:** ≥3 new active contributors to constructive formalization in first year (measured by merged PRs to constructive variants or budget-tracked modules), indicating community buy-in beyond mere compliance

If these thresholds aren't met, honest documentation of adoption costs vs. benefits would inform whether the framework should be recommended for broader use.

---

## Part VII: Research program and validation

### 7.1 Success metrics (falsifiable)

**Coverage Hypothesis:**
≥70% of widely-used theorems in targeted domains (optimization, separable analysis, numerical methods) can be formalized at C0–C2 with explicit moduli and rates.

**Measurement:** Formalize representative sample, measure budget distribution, compare to hypothesis.

**Automation Hypothesis:**
AI theorem provers achieve measurably higher success rates on C0–C2 statements vs classical formulations of the same result.

**Evaluation Design:**

*Dataset:* 30–50 theorem pairs with matched statements: (A) classical form (C3–C5), (B) constructive/quantitative form (C0–C2). Domains: Banach FP with rates, sequential compactness vs. general compactness, basic optimization lemmas with moduli.

*Systems:* A fixed Lean auto-tactic baseline and an LLM-driven prover (same model/settings across conditions). Optional flag: `execute_to_prune` that runs candidate witnesses where available.

*Metrics (with precise validation thresholds):*
- **(i) pass@k:** **Threshold:** ≥15% relative improvement in pass@10 for C0–C2 vs classical formulations — e.g., 50% → 57.5%
- **(ii) median tactic steps:** **Threshold:** ≥10% reduction in median tactic steps for successful proofs
- **(iii) wall-clock time:** **Threshold:** ≥10% reduction in median proof-search time for successful attempts
- **(iv) proof length:** **Secondary metric** — may increase due to explicit witnesses; not a validation criterion
- **(v) composition success:** **Threshold:** ≥20% relative improvement on 2–3-step pipelines where witnesses feed forward — e.g., 40% → 48%
- **(vi) extraction success:** **Threshold:** ≥80% of C0–C2 proofs yield compilable, executable code; extracted algorithms run without errors on test inputs

**Validation outcome:** H1 is supported if **at least 3 of 5** primary metrics (i, ii, iii, v, vi) meet their thresholds on the evaluation dataset. If fewer than 3 meet thresholds, report as "insufficient evidence for automation benefits" and analyze failure modes.

**Statistical methodology:**

*Sample size and power:* With N = 40 theorem pairs, we can detect a 15% relative improvement in pass@10 (e.g., 50% → 57.5%) with 80% power at α = 0.05 using a paired bootstrap test. Power calculation assumes typical variance observed in theorem proving benchmarks (standard deviation of paired differences ≈ 0.15 on [0,1] scale). For smaller effect sizes (e.g., 10% relative improvement), N ≈ 60–70 pairs would be needed for adequate power.

*Paired comparisons:* Each theorem is represented by a matched pair (classical formulation, constructive formulation). All metrics are computed as **paired differences** within each theorem. Primary analysis uses paired tests (Wilcoxon signed-rank test for median tactic steps and wall-clock time; paired bootstrap test for pass@k proportions). This controls for theorem-specific difficulty and yields higher statistical power than independent-samples comparisons.

*Reporting:* For each metric, report:
- Median paired difference with 95% bootstrap confidence interval (10,000 bootstrap resamples)
- Percentage of pairs showing improvement (directional consistency)
- Per-topic stratified analysis (e.g., optimization vs. analysis vs. compactness theorems)
- Full distribution of paired differences (violin plots or histograms)

*Reproducibility:* Fix random seeds for all stochastic components:
- Proof search: seed per theorem + condition (enables exact reproduction)
- LLM sampling: temperature, top-p, and seed specified in published config
- Bootstrap resampling: seed for reproducible CI computation
All configurations, seeds, theorem pairs, and raw results will be published in a public repository alongside the evaluation.

*Stratification:* Pre-register theorem pairs by topic (optimization, compactness, fixed-point theory, etc.) to enable subgroup analysis. If overall effects are weak but concentrated in one domain, this isolates where structural benefits appear.

*Multiple comparisons:* With 5 primary metrics, we apply Bonferroni correction (α/5 = 0.01 per test) or report uncorrected p-values with explicit multiple-testing caveat. The "3 of 5 thresholds met" rule provides robustness against false positives from multiple testing.

*Ablations:*
- A1: Disable `execute_to_prune` on C0–C2 to isolate the execution benefit
- A2: Strip explicit moduli/rates from signatures to test the "quantitative types" effect
- A3: Force decidability via `Classical.propDecidable` to see impact of implicit classicalization
- A4: Force vBudget == xBudget (conflate verification and extraction budgets) to demonstrate the value of the Prop/Type flow distinction

**Critical confound: training data distribution**

Current LLMs are trained on existing mathematical corpora, which are overwhelmingly classical. This creates a significant risk of confounding intrinsic searchability benefits with mere distributional familiarity.

**The confound:**
- **Training bias:** Models see 95%+ classical proofs in training data (arXiv, textbooks, mathlib)
- **Familiarity vs. structure:** Constructive proofs may be less familiar, not inherently harder to find
- **Distribution shift:** Lower success on C0–C2 could reflect unfamiliarity rather than disconfirm H1

**Primary validation experiment:**
To address this confound head-on, a **controlled fine-tuning experiment on a balanced corpus** should be a core component of the validation plan, not merely a mitigation:
1. **Controlled fine-tuning:** Pre-train or fine-tune a model on a balanced mix of classical and constructive mathematics from constructive analysis textbooks (Bishop, Bridges), constructive type theory sources, and extracted mathlib constructive variants
2. **A/B comparison:** Run the automation metrics (pass@k, steps, time) on this balanced-corpus model vs. the standard classical-trained baseline
3. **Causal inference:** If the balanced model shows equal or improved performance on C0–C2 formulations, this isolates intrinsic structural benefits from distributional familiarity

**Additional mitigation strategies:**
1. **Cross-domain transfer:** Test on domains where classical and constructive formulations are equally represented in training (finite mathematics, basic analysis)
2. **Prompt engineering:** Provide constructive lemma libraries in context to reduce distribution gap
3. **Decomposition analysis:** Measure whether *specific constructive structures* (Σ-types, explicit moduli, sequential choice) provide search benefits when isolated, controlling for overall proof style familiarity

**Reporting requirement:** Evaluation must explicitly separate:
- **(a) Intrinsic structural benefits** of C0–C2 (execute-to-prune, typed interfaces, sequential constraints)
- **(b) Distribution effects** (model has seen more classical proofs)

If H1 fails due to (b), that's a negative result about current model training, not about the framework. If H1 succeeds despite (b), that's stronger evidence for intrinsic benefits.

**Deeper confound: Architectural suitability**

Even with balanced fine-tuning, transformer architectures trained predominantly on classical mathematics may develop representational structure (embedding space geometry, attention patterns, internal representations) that encodes classical proof strategies as primary axes of variation. If so, constructive proofs could remain "off-manifold" even after exposure to balanced data — not because they're harder in principle, but because the architecture is constitutively unsuited to exploit their structure.

**Implication:** If balanced-corpus fine-tuning fails to close the performance gap, this doesn't necessarily invalidate H1's structural hypothesis. It might instead indicate that **architectural interventions** are needed: proof-state encoders that explicitly represent Σ-types, execution traces for witnesses, sequential/compositional proof representations, etc. Exploring alternative architectures (graph neural networks over proof DAGs, neuro-symbolic hybrids with explicit witness tracking) could be necessary to test the structural hypothesis fairly.

**Methodological requirement:** A credible evaluation requires publishing negative results. If H1 were to fail, analysis of where constructive structure didn't translate into search gains would be essential. Training data confounds must be analyzed and reported transparently. If architectural limitations are suspected, this should be flagged as a direction for future investigation rather than evidence against the framework's core claims.

**Performance Hypothesis:**
Extracted algorithms from constructive proofs are competitive with hand-coded implementations.

**Measurement (with precise thresholds):**
- **Wall-clock time:** ≤10× slowdown vs hand-coded baseline (stretch goal: ≤3×)
- **Accuracy:** Bit-identical or within 1 ULP (unit in the last place) on floating-point outputs
- **Memory usage:** ≤5× overhead vs hand-coded (absolute: <1GB for benchmark problems)
- **Compilation time:** <60 seconds for extracted code compilation (per theorem)

**Validation outcome:** Performance hypothesis is supported if extracted implementations meet wall-clock (≤10×) and accuracy thresholds on ≥80% of test cases. Report detailed profiling for outliers to identify optimization opportunities.

**Realistic expectations:** The ≤10× slowdown target is aspirational. For context, Coq extraction to OCaml typically yields 2–5× slowdown for simple algorithms, but can be significantly worse (10–50×) for heavily dependently-typed code with complex term representations. Lean extraction similarly varies widely depending on type complexity and optimization opportunities. Extracted code from dependent type theory often exhibits higher constant factors, memory overhead, and compilation costs compared to hand-optimized implementations. For performance-critical applications, **hand-optimized shims** for hot paths may be necessary, and some extracted algorithms may not be competitive with carefully tuned hand-coded baselines. The value proposition is strongest for: (a) rapid prototyping with correctness guarantees, (b) domains where bugs are more costly than performance penalties (safety-critical systems, verified science), and (c) applications where the certified bounds themselves are the primary deliverable. Honest reporting of performance characteristics — including cases where extraction underperforms — is essential for establishing realistic expectations about when extracted code is deployment-ready versus when it serves primarily as a verified specification.

**Hygiene Hypothesis:**
Measurable decline in representative-picking violations after linter adoption.

**Measurement (with precise thresholds):**
- **Violations per 1000 LOC:** ≥30% reduction within 6 months of linter deployment
- **Budget distribution shift:** ≥10 percentage point increase in C0–C2 coverage — e.g., 40% → 50%
- **Refactoring patterns:** Document whether fixes use `Quot.lift`, add invariance proofs, or provide explicit moduli

**Validation outcome:** Hygiene hypothesis is supported if violation rate decreases by ≥30% and budget distribution shifts toward C0–C2 by ≥10pp in instrumented modules.

**Portability Hypothesis:**
Proofs compile in both Coq and Lean without budget escalation.

**Measurement (with precise thresholds):**
- **Cross-system formalization success:** ≥70% of case study theorems successfully formalized in both Lean and Coq
- **Budget preservation:** Budget classifications agree within ±1 level in ≥80% of cross-formalized theorems
- **No system artifacts:** If budgets diverge, root cause analysis documents whether difference is due to library dependencies, axiom availability, or genuine semantic differences

**Validation outcome:** Portability hypothesis is supported if cross-system success rate ≥70% and budget agreement ≥80%.

### 7.2 Threats to validity

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

**Design requirement:** Case studies should explicitly track and report on each threat, documenting mitigation effectiveness and any needed hypothesis adjustments.

### 7.3 Two high-signal case studies

**Selection criteria:** Initial case studies should target theorems that are:
1. **High-impact:** Widely used in applications (numerical methods, optimization, PDE solving)
2. **Budget-reducible:** Classical formulations exist, but C0–C2 versions are achievable with explicit moduli
3. **Mathlib-present:** Already formalized classically in mathlib, enabling direct comparison
4. **Extraction-testable:** Yield executable algorithms suitable for performance benchmarking

**Target mathlib modules for initial instrumentation:**
- `Mathlib.Topology.MetricSpace.Contracting` (Banach fixed-point theorem)
- `Mathlib.Analysis.NormedSpace.BanachSteinhaus` (Separable analysis)
- `Mathlib.Topology.Compactness.Compact` (Sequential compactness in metric spaces)
- `Mathlib.Analysis.Calculus.MeanValue` (Mean value theorem with explicit bounds)

---

**Study 1: Banach fixed-point theorem**

**Mathlib target:** `Mathlib.Topology.MetricSpace.Contracting.efixedPoint_of_contracting_nonneg`

**Proposed scope:**

Complete validation would include:
1. Constructive formalization (C0) with explicit convergence rate
2. Extracted solver implementation in Lean/Coq
3. Certification: Rate formula N(ε) = ⌈ln(d(x₁,x₀) / ((1-L)ε)) / ln(1/L)⌉
4. Budget tracking: Explicit C0 badge, CI enforcement
5. Comparative analysis:
   - Proof complexity (lines, dependencies, concepts)
   - Verification time (classical vs constructive)
   - Extracted code performance vs hand-written solver
   - Usability in downstream optimization applications

**Application context:** Certified numerical optimization, compared against classical proofs that give convergence eventually without rates.

**Study 2: Arzelà-Ascoli in separable metric spaces**

**Mathlib target:** `Mathlib.Topology.UniformSpace.Ascoli` (restrict to separable metric case)

**Proposed scope:**

Complete validation would include:
1. Constructive proof avoiding ultrafilters
2. Method: Total boundedness + equicontinuity + dependent choice (C2)
3. Explicit subsequence constructor with modulus
4. Extraction to working subsequence-finding code
5. Comparative analysis:
   - Classical proof structure vs constructive
   - Budget assignments and dependencies
   - Practical utility for PDE compactness arguments

**Application context:** Compactness arguments in numerical PDE solving, certified subsequence extraction for function spaces.

**Optional study 3: Compact products via locales**

**Proposed scope:**

Complete validation would include:
1. Countable products of compact metric spaces
2. Gluing method avoiding ultrafilters (C0–C2)
3. Demonstration of practical utility for function spaces
4. Connection to pointless topology and constructive analysis

### 7.4 The bootstrapping challenge

**Assessment of the barrier:**

The primary obstacle isn't philosophical disagreement about foundations — it's the **engineering activation energy** of formalizing applied mathematics constructively.

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

This research program is a **high-leverage bootstrap experiment**. The goal is not to constructivize all mathematics, but to:

1. **Prove the value proposition:** Demonstrate that automation gains and extractability benefits are large enough to justify the engineering investment

2. **Build enabling tools:** Instrumentation, linters, budget tracking that lower the barrier for everyone else

3. **Establish proof-of-concept:** Two case studies showing the full pipeline (formalize constructively → extract algorithm → measure benefits)

4. **Validate measurably:** Empirical data on coverage, automation, performance — not just philosophy

**If successful, this unlocks community-scale effort.** If automation really is better with C0–C2, and extraction really does yield practical algorithms, and tooling really does make it manageable, then the community will adopt it.

**If unsuccessful, we learn what doesn't work** and can pivot or abandon the approach. Either way, we get data rather than speculation.

---

## Part VIII: Objections and responses

### 8.1 "This is too narrow — what about general AI alignment?"

**Objection:** You're focused on mathematical reasoning, but most AI safety challenges (value learning, deception, robustness, goal misgeneralization) have nothing to do with formal proofs.

**Response:**
Correct. We're addressing a **specific but growing subset** of AI safety:
- Automated mathematics and theorem proving
- Certified software and verified algorithms
- Scientific AI doing symbolic reasoning
- AI systems producing executable artifacts from formal specifications

As AI capabilities expand into formal reasoning domains, transparent oversight becomes more important. We're building foundations now for capabilities that are emerging.

**We are not claiming** to solve alignment broadly. We're solving transparent oversight for mathematical/formal reasoning specifically.

### 8.2 "Classical math works fine — why do we need constructivism?"

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

For AI automation and certified algorithms, we need both. This isn't philosophical preference — it's an engineering requirement for specific applications.

### 8.3 "Aren't you conflating verification with extraction?"

**Objection:** Classical proofs ARE verifiable — Lean/Coq verify them fine. You keep implying non-constructive proofs can't be verified, but that's wrong.

**Response:**
This concern is well-founded, and we maintain this distinction carefully throughout. See §3.3 for the full explanation, but in summary:

**Verification** (logical correctness): Both classical and constructive proofs are verifiable
**Operationalization** (extractable content): Typically only constructive proofs provide this

For AI safety and automation in algorithmic domains, we need **both** properties. This framework tracks operational content (via witness budgets) while taking verification as a baseline requirement for all formalized mathematics.

### 8.4 "What about interactive proofs/PCP (Probabilistically Checkable Proofs)? You're ignoring other verification approaches."

**Objection:** Probabilistically Checkable Proofs and interactive proof systems provide efficient verification without requiring witnesses. Your framework ignores an entire approach to verification.

**Response:**
Not ignoring — acknowledging as **complementary**. See Appendix D for detailed comparison of verification channels (constructive witnesses, classical proofs, PCPs).

**In brief:** Different approaches serve different purposes. For AI producing **algorithmic mathematics** (certified software, numerical methods), constructive witnesses are optimal because they provide the operational content needed for execution and composition. PCP/interactive proofs excel at efficient verification and succinctness but don't provide extractable algorithms for computational applications.

### 8.5 "Lean's mathlib is classical — this is impractical"

**Objection:** The main formal mathematics library (mathlib) is predominantly classical. You're asking people to redo massive amounts of work. This is impractical.

**Response:**
We're not proposing to replace mathlib. We're proposing:

1. **Constructive subsets:** Explicitly mark and maintain C0–C2 subsets of mathlib
2. **New formalization:** For applied mathematics (optimization, numerical analysis), target constructive from the start
3. **Parallel development:** Constructive libraries alongside classical ones, not replacing them
4. **Tooling:** Build instrumentation that makes constructive discipline enforceable
5. **Empirical validation:** Measure if benefits (automation, extraction) justify costs

**Acknowledging the overhead:** Yes, dual-rail increases maintenance surface area. This could be mitigated by linking paired theorems via attributes so they're maintained together, sharing implementations via wrappers, and targeting "constructive islands" like optimization and separable analysis where most value concentrates — not library-wide duplication. If benefits don't justify costs in practice, honest documentation of this trade-off would be essential.

**The bootstrapping challenge section (§7.4)** explicitly addresses this: we're not claiming "everyone should rewrite everything," we're claiming "let's test if constructive applied math provides measurable benefits, and if so, make it easier for others to adopt."

### 8.6 "Constructive algorithms might be inefficient"

**Objection:** Even if you extract an algorithm from a constructive proof, it might be highly inefficient — exponential time, impractical space usage. Just having an algorithm doesn't mean it's useful.

**Response:**
Valid concern. This is exactly why **proof mining is essential**, not optional:

**Constructive alone:** Gives algorithms, not necessarily good ones
**Constructive + proof mining:** Extracts explicit bounds, rates, complexity

**Our requirement:** Type signatures must include quantitative content:
- Not just "witness" but "witness + convergence rate"
- Not just "algorithm" but "algorithm + complexity bound"
- Not just "approximate" but "approximate with explicit error function"

**Empirical test:** Case studies should measure performance. Reasonable target: within an order of magnitude of hand-coded implementations, with constant-factor optimization as an explicit workstream. Credible evaluation requires reporting performance characteristics and identifying bottlenecks.

We're not claiming "constructive = efficient" automatically. We're claiming "constructive + quantitative bounds = practical algorithms with certifiable correctness" is achievable for important cases, and the performance trade-offs are empirically measurable.

### 8.7 "Why not classical proof + manual algorithm implementation?"

**Objection:** Many applied mathematicians already do this successfully: prove existence classically, then separately implement an algorithm by hand. Why is automatic extraction better than careful human translation from proof to code?

**Response:**
Extraction provides guarantees that manual translation cannot:

**Spec-to-code conformance:**
- Extracted code is *provably* correct with respect to the theorem statement
- Manual implementations can introduce bugs during translation
- Gap between "paper proof" and "running code" is a known source of errors in scientific computing

**Compositional reuse:**
- Extracted algorithms automatically compose via typed interfaces (witness budgets)
- Manual implementations require hand-written glue code and compatibility checks
- Budget tracking ensures composed pipelines maintain extraction guarantees

**Maintainability:**
- When theorem statement changes, extraction stays synchronized automatically
- Manual implementations require separate updates and re-verification
- Refactorings propagate correctly through extraction pipeline

**Certified bounds:**
- Quantitative content (rates, moduli, complexity) is mechanically verified
- Manual claims about performance often lack formal justification
- Extraction makes "algorithm with certified bounds" a single artifact

**However:** For mature, performance-critical numerical codes, hand-optimized implementations may outperform direct extraction. The value proposition is strongest for: (a) rapid prototyping with correctness guarantees, (b) compositional pipelines where interface conformance matters, and (c) domains where bugs are costly — safety-critical systems and verified science. The performance gap is an empirical question requiring measurement.

---

## Part IX: Community and collaboration

### 9.1 Key research groups

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

### 9.2 Dissemination venues

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

### 9.3 Funding opportunities

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

## Part X: Limitations and open questions

This framework presents a research program, not a finished solution. Several significant limitations and open questions require explicit acknowledgment:

### Technical gaps requiring formalization

**1. C1 Consumption Semantics**
- **Gap:** Precise semantics for when consumer computations using truncated existence are extractable remain incompletely specified
- **Current state:** Pragmatic discipline (Quot.lift + invariance proofs) is mechanically enforceable but lacks full semantic model
- **Clarification:** C1 enables extracting *consumer computations* that use only invariant properties, NOT extracting witnesses themselves
- **Future work:** Formalize extraction relation: `truncated(∃x.P) + invariance(f) → extractable(f_result)`; prove soundness/completeness via PER semantics or similar

**2. Effect System Compositionality**
- **Gap:** Simple composition rule `budget(f ∘ g) = max(budget(f), budget(g))` doesn't handle proof-irrelevant classical use
- **Example:** Classical proof used but result doesn't depend on which witness — should downgrade like C1
- **Future work:** Refine effect system to track proof irrelevance; add downgrading rules for "doesn't matter" classical steps

**3. Impredicativity and Universe Levels**
- **Gap:** Lean/Coq have impredicative `Prop` which introduces non-constructivity orthogonal to C0–C5 scale
- **Issue:** Impredicative quantification can hide computational content even without LEM/AC
- **Current approach:** Pragmatic - budget tracker flags impredicative definitions conservatively
- **Future work:** Develop unified account of impredicativity + oracle effects; correlate with predicativity hierarchies

**4. Universe Polymorphism Interactions**
- **Gap:** Budget inference must track universe levels to avoid false negatives in universe-polymorphic definitions
- **Challenge:** A proof appearing C0 at the term level may use `Type u` in ways that interact with impredicative `Prop`, blocking extraction
- **Example:** Universe-polymorphic `Quotient.lift` may behave differently depending on whether the codomain is in `Prop` vs `Type`
- **Current state:** Budget inference operates post-elaboration on monomorphized instances; universe-generic budget tracking is not implemented
- **Future work:** Extend effect system to track universe parameters; formalize budget preservation under universe instantiation; develop linters for universe-level extractability violations

**5. Tactic-Generated Proof Terms**
- **Gap:** Budget inference must handle tactic-generated proofs where classical reasoning may be implicit
- **Challenge:** Tactics can insert classical lemmas invisibly; elaboration may add `Classical.propDecidable`
- **Current mitigation:** Walk compiled proof terms post-elaboration; flag typeclass-synthesized classical instances
- **Limitation:** Conservative over-approximation; may mis-classify some proofs

**6. Prop/Type Flow Sensitivity**
- **Gap:** Current budget inference does not distinguish Prop-only uses of classical axioms from Type-level uses that block extraction
- **Issue:** A proof may use `Classical.choice` in a Prop-only subproof (verification only, doesn't affect extraction) vs. using it to produce computational content in Type (blocks extraction)
- **Example:** Classical proof of `P : Prop` used only in correctness argument → budget could be lower; classical choice producing `x : Type` → must bump budget
- **Current state:** Inference conservatively flags all uses of classical axioms regardless of whether they flow into Type or remain in Prop
- **False positives:** Proofs marked C3+ even when classical reasoning is Prop-confined and extraction succeeds
- **Future work:** Add elimination-context tracking (does classical artifact flow into Type?); distinguish Prop-only vs Type-affecting uses; refine budget assignment based on extraction relevance

### Empirical uncertainties

**7. Training Data Distribution Confound**
- **Limitation:** Current LLMs overwhelmingly trained on classical mathematics
- **Risk:** H1 automation results confound intrinsic structure with distributional familiarity
- **Addressed in:** §7.1 with mitigation strategies, but remains major validity threat
- **Open question:** How much of automation benefit persists after controlled fine-tuning on balanced corpora?

**8. Performance of Extracted Code**
- **Uncertainty:** Will extracted algorithms be competitive with hand-coded implementations?
- **Current target:** ≤10× slowdown threshold
- **Risk:** Constant factors, memory overhead, compilation time may be prohibitive for practical use
- **Mitigation:** Hand-optimized shims for critical paths; profiling and optimization as explicit workstream
- **Open question:** What percentage of real applications can tolerate extraction overhead?

**9. Dual-Rail Maintenance Burden**
- **Uncertainty:** Is maintaining both classical and constructive variants sustainable at library scale?
- **Risk:** Contributor fatigue; version drift; coordination overhead
- **Mitigation strategies proposed:** `@[witness_of]` linking; "constructive islands" targeting
- **Open question:** At what coverage percentage does maintenance burden exceed value?

### Scope boundaries

**10. Not a General Alignment Solution**
- **Explicit non-goal:** This framework addresses mathematical reasoning, not value learning, deception, or robustness
- **Scope limitation:** Useful for AI systems producing executable artifacts from formal specs; irrelevant for most AI safety challenges
- **Honest assessment:** Even perfect success wouldn't solve alignment broadly

**11. Limited to Applicable Domains**
- **Works well:** Optimization, separable analysis, numerical methods, finite mathematics
- **Works poorly:** Pure set theory, category theory, non-separable functional analysis, general topology
- **Fundamental limitation:** Some mathematics genuinely requires high budgets; framework doesn't change this

**12. Classical Mathematics Remains Essential**
- **Not proposing:** Replacement of classical foundations
- **Reality check:** High choice budgets (C4-C5) needed for algebraic closure, unrestricted Hahn-Banach formulations, arbitrary Tychonoff, etc.
- **Framework position:** Dual-rail coexistence, not constructive monopoly

### Alternative architectures not addressed

**13. Classical Metalanguage + Refinement Types**
- **Alternative approach:** Use classical logic with explicit refinement types for computational content
- **Potential advantage:** Avoids bootstrapping problem; works with existing mathlib
- **Not explored:** This framework focuses on constructive discipline, not refinement type approach
- **Open question:** Would refinement types provide equivalent benefits with lower adoption cost?

**14. Proof-Carrying Code Without Full Formalization**
- **Alternative:** Generate proof certificates for extracted code without formalizing full theorem
- **Trade-off:** Less trustworthy but more practical for legacy code
- **Framework stance:** Prioritizes full formalization; PCC approach complementary but different

### Validation requirements

**13. Negative Results Must Be Published**
- **Commitment:** If H1 fails, publish failure analysis
- **Scientific integrity:** Framework's value depends on honest empirical evaluation
- **Risk:** Community may not adopt if automation benefits don't materialize
- **Mitigation:** Design falsifiable experiments; report regardless of outcome

**14. Cross-System Portability Unproven**
- **Hypothesis:** Budgets should agree across Lean/Coq formalization of same theorem
- **Reality:** Haven't validated this empirically
- **Risk:** System-specific axiom availability may cause budget drift
- **Validation needed:** Parallel formalization case studies

**15. Extraction Success Rate Unknown**
- **Target:** ≥80% of C0–C2 proofs yield compilable code
- **Reality:** This is aspirational, not demonstrated
- **Risks:** Prop/Type discipline violations; impredicativity; performance issues
- **Validation needed:** Systematic extraction attempts on formalized theorems

### Summary: what we don't know

This document presents a **framework and research program**, not validated conclusions. The core claims — that witness budgets matter for automation and that C0–C2 formulations improve extraction — are **hypotheses requiring empirical validation**.

**We honestly don't know:**
- Whether automation improvements will be large enough to justify engineering costs
- Whether extracted code will perform acceptably
- Whether dual-rail maintenance is sustainable
- Whether training data confounds will dominate intrinsic effects
- Whether the framework will be adopted by formal methods community

**We do know:**
- The conceptual framework is coherent
- The metrics are falsifiable
- The tooling is implementable
- The case studies are tractable
- The questions are answerable through empirical work

**The path forward:** Build, measure, report honestly.

---

## Part XI: Conclusion

### 11.1 What we've established

**Philosophical:**
- Constructive mathematics isn't just aesthetic preference — it's about operational content
- Non-constructive existence steps lack operational handles for extraction and composition
- "It doesn't matter which choice" signals we should work with invariants, not representatives
- Circles vs choice functions: different kinds of idealization (process limits vs bare assertion)

**Technical:**
- Witness budget (C0–C5) makes oracle dependence measurable and compositional
- Verification ≠ operationalization — need to distinguish and provide both
- Three verification channels (constructive, classical, PCP) serve different purposes (see Appendix D for details)
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

### 11.2 What this enables

**For AI Safety:**
- Technical specification of "transparent oversight" for mathematical reasoning
- Measurable metric (witness budget) for operational extractability
- Concrete implementation path via constructive formal mathematics
- Bridge to established formal methods community

**For Formal Methods:**
- Elevated purpose beyond software verification — alignment infrastructure
- Clear value proposition for constructive discipline (automation + extraction)
- Integration with AI safety motivation and funding
- Framework for tracking and reducing oracle dependence

**For Constructive Mathematics:**
- Modern, high-stakes motivation (AI safety and automation)
- Practical applications (certified algorithms, verified software)
- Community expansion beyond foundations specialists
- Relevance to safe algorithmic reasoning at scale

**For Applied Mathematics:**
- Algorithmic content from proofs, not just existence
- Explicit bounds and rates, not just asymptotic behavior
- Verified implementations with certified correctness
- Bridge to computational systems and AI automation

### 11.3 The honest assessment

**This approach is not:**
- A solution to all AI safety problems
- A claim that all mathematics should be constructive
- A replacement for classical foundations in pure mathematics
- A proven approach (yet — needs empirical validation)

**This approach is:**
- A concrete framework for a specific but growing problem
- A testable hypothesis about automation and extraction
- A practical toolkit for making oracle dependence visible
- An opportunity to validate whether operational content matters empirically

**The bootstrapping challenge is real:** Constructive formalization costs engineering effort upfront. Success requires proving the benefits justify the investment.

**The research program is strategic:** Not trying to constructivize everything, but running a focused experiment on high-value applied mathematics to measure automation gains and extraction utility.

**The timing is opportune:** AI capabilities in formal reasoning are emerging now. Building transparent, operational foundations positions us well for safe development of these capabilities.

### 11.4 The path forward

**This framework is ready to prototype and validate.** The instrumentation would itself be a research contribution; §6 specifies the core mechanisms. A complete empirical study would publish implementation details alongside the design validation.

The conceptual framework is established. The witness budget scale is coherent. The connections are validated by multiple reviewers. The scope is honest. The metrics are falsifiable.

**A complete validation program would include:**
1. Building the instrumentation (budget tracking, linters, CI integration)
2. Formalizing the case studies (Banach, Arzelà-Ascoli with explicit rates)
3. Extracting and benchmarking algorithms (measuring performance, comparing to hand-coded)
4. Measuring automation differences (AI proof search on C0–C2 vs classical)
5. Reporting results (positive or negative — either way we learn)

**The opportunity:**
Be among the first to explicitly connect transparent oversight frameworks to constructive mathematical foundations, demonstrate measurable benefits empirically, and provide tooling that makes operational content practical and trackable.

**The question:**
Not whether witness budgets are a useful concept (they are), but whether the automation and extraction benefits are large enough to justify the engineering investment in constructive formalization.

**The answer requires empirical work.** Implementation of a budget tracker in Lean 4 and formalization of Banach fixed-point with explicit convergence rates would provide concrete proof-of-concept validation. These are tractable first steps for anyone motivated to test the framework.

---

## Part XII: Related work

This work sits at the intersection of program extraction, Curry-Howard/realizability, proof mining, computable analysis, reverse mathematics, program synthesis, formal libraries, and AI for theorem proving. Prior efforts establish the foundations and many powerful techniques; what's missing is a library-scale discipline with metrics and CI that ties constructive content to automation and extraction outcomes. We position our contribution as integration + enforcement + empirical validation. For a summary of our contributions vs prior work, see the "What's New in This Paper" section at the document opening.

### 12.1 Landscape overview

| **Area** | **Representative work** | **Gap we address** | **What we add** |
|----------|------------------------|-------------------|-----------------|
| **Program extraction** | Coq extraction; Agda compilation; Lean codegen; Nuprl | No quantitative contracts; no budget telemetry; no CI; little data on automation | Budgets + type-level bounds/rates + CI enforcement + automation metrics |
| **Curry-Howard / Realizability** | CH isomorphism; (modified) realizability; Dialectica | Foundations, not library-scale discipline | Operational discipline (budgets, invariance, contracts) at scale |
| **Proof mining** | Kohlenbach; functional interpretations | Manual, post hoc; bounds can be huge; no AI automation link | Upfront quantitative APIs + budget diffs + automation eval |
| **Computable analysis / Weihrauch** | Weihrauch reducibility; TTE | Classifies difficulty, not usage in libraries; orthogonal focus | Oracle-usage telemetry in proof assistants; potential cross-analysis |
| **Reverse mathematics** | Simpson's subsystems | Provability strength, not engineering guidance | Budgets to guide refactoring and CI policies |
| **Program synthesis / CEGIS** | Sketch; SyGuS; exec-guided search | Synthesis, not formal proof libraries; no axiom tracking | Execute-to-prune witnesses in proof search; budget-aware eval |
| **Formal math libraries** | mathlib, MathComp, Coq stdlib, Isabelle/HOL | No budget tracking; constructive vs classical is binary | Graded budgets, badges, and dual-rail adoption path |
| **AI for theorem proving** | Neural provers/tactics | No distinction by budget; no extraction guarantees | Budget-aware benchmarks; compositional interfaces via witnesses |

### 12.2 Program extraction from proofs

**Existing work:**
- Coq's extraction mechanism (Letouzey, 2002) extracts OCaml/Haskell from Set/Type; Prop erases during extraction
- Lean's code generation compiles executable code but only from computable definitions (non-`noncomputable` terms)
- Agda's direct compilation treats code as proof; Nuprl's computational content semantics (Constable et al., 1986)

**Gap our framework addresses:**
- Existing extraction yields code but rarely enforces explicit bounds/rates at the type level; no systematic budget tracking to measure which axioms block extraction; no CI integration or automation metrics

**Our contribution:**
- Systematic budget tracking + quantitative type signatures requiring witnesses and rates + CI enforcement + empirical automation evaluation (see §6, §7)

### 12.3 Curry-Howard correspondence and realizability

**Existing work:**
- Curry-Howard isomorphism (proofs as programs, propositions as types); Kleene realizability and modified realizability (Kreisel, 1959); Dialectica interpretation (Gödel, 1958) for functional interpretation of proofs

**Relationship to our work:**
- These provide the *foundational* connection between proofs and algorithms; witness budgets operationalize this at the *library engineering* level; we're not introducing new semantics, but engineering discipline for existing foundations

**Our contribution:**
- Practical tooling and metrics that make Curry-Howard principles trackable at scale in modern proof assistant libraries (see §6.2–6.5)

### 12.4 Proof mining (Kohlenbach's program)

**Existing work:**
- Kohlenbach (2008): *Applied Proof Theory* — systematic extraction of quantitative bounds from classical analysis using Dialectica and bounded functional interpretation
- Applications: Fixed-point theory, ergodic theory (Avigad et al., 2010), nonlinear analysis (Kohlenbach & Leuștean, 2009), optimization

**Gap our framework addresses:**
- Proof mining is expert-driven manual analysis yielding post-hoc bounds (which can be impractically large); we seek *automated* budget tracking and advocate *stating* quantitative APIs upfront
- No integration with AI automation or compositional pipelines

**Our contribution:**
- Combining proof mining insights with type-level quantitative contracts enforced at formalization time; budget telemetry before/after mining; automation metrics (see §4.2–4.3, §7.1)

### 12.5 Computable analysis and Weihrauch complexity

**Existing work:**
- Computable analysis (Weihrauch, 2000; Pour-El & Richards, 1989): which analysis objects/functions are computable?
- Weihrauch reducibility measures relative computational difficulty; Type-2 effectivity for continuous functions

**Relationship to our work:**
- Computable analysis classifies *what's computable*; witness budgets measure *oracle usage* (orthogonal but complementary axes)
- Weihrauch degrees are finer-grained than C0–C5 (they distinguish *within* computable problems)

**Our contribution:**
- Practical instrumentation for tracking oracle usage in proof assistants, targeted at AI automation and library engineering; potential future work to correlate budgets with Weihrauch degrees (see §11.9)

### 12.6 Reverse mathematics (Simpson's program)

**Existing work:**
- Simpson (2009): *Subsystems of Second Order Arithmetic* — classifying theorems by minimal axiom strength needed to prove them
- "Big Five" subsystems: RCA₀, WKL₀, ACA₀, ATR₀, Π¹₁-CA₀; measures *logical strength*

**Relationship to our work:**
- Reverse mathematics: "What axioms are *necessary*?" (proof-theoretic classification)
- Witness budgets: "What oracle effects are *used*?" (engineering telemetry with operational consequences)

**Our contribution:**
- Engineering framework that makes axiom tracking actionable for CI/CD and AI automation; budgets guide refactoring, not just classification (see §6.2, §6.6)

### 12.7 Program synthesis and CEGIS

**Existing work:**
- Counterexample-Guided Inductive Synthesis (Solar-Lezama, 2008): synthesize programs by iterative refinement
- SyGuS (Alur et al., 2013): syntax-guided synthesis; execution-guided search uses concrete evaluation to prune search space

**Relationship to our work:**
- Our "execution-prunable witnesses" mechanism (§3.4, Hypothesis H1) is conceptually similar to CEGIS: when existentials live in Type (C0), candidate witnesses can be executed and falsified

**Our contribution:**
- Bringing execution-guided search principles into theorem proving with budget tracking; measured via witness budgets; evaluation framework for automation benefits (see §7.1)

### 12.8 Formalization efforts and proof assistant libraries

**Existing work:**
- Mathlib (Lean): 150k+ theorems, predominantly classical
- Mathematical Components (Coq): Constructive by design, focus on finite group theory
- Coq standard library, Isabelle/HOL: mix of classical and constructive

**Gap addressed:**
- No systematic budget tracking across any major library; classical vs constructive is binary choice, not graded measurement; no CI enforcement of constructive discipline; limited empirical data on automation differences

**Our contribution:**
- Instrumentation to measure and track budgets in existing libraries; dual-rail adoption strategy with explicit maintenance mitigation (§6.6); empirical evaluation of automation benefits (§7.1)

### 12.9 AI for theorem proving

**Existing work:**
- Neural theorem provers and LLM-driven systems; proof search with language models; tactic prediction and auto-formalization

**Gap addressed:**
- Current systems don't distinguish budget levels; no systematic evaluation of constructive vs classical for automation; generated proofs may use unnecessary oracle steps; no extraction guarantees for AI-produced theorems

**Our contribution:**
- Framework for evaluating whether constructive formulations improve AI proof search (Hypothesis H1, §7.1); budget tracking for AI-generated proofs; compositional interfaces via witnesses

### 12.10 Summary: what's novel here

Each component exists in some form. Our contribution is **systematic integration + enforcement + empirical validation:**

**Integration:**
- Curry-Howard + proof mining + quantitative types + CI engineering + AI automation metrics
- Bridging three communities (AI safety, formal methods, constructive math) with shared framework

**Enforcement:**
- Witness budgets as *measured, tracked, CI-enforced* discipline (not just philosophy)
- Invariance linter making "doesn't matter which" mechanically checkable
- Quantitative type contracts forcing explicit bounds

**Empirical validation:**
- Falsifiable hypotheses about automation benefits (H1)
- Performance benchmarks for extracted code
- Coverage metrics for C0–C2 reformulation feasibility

In short, we don't propose new semantics; we operationalize existing ones. The novelty is a systematic practice — witness budgets, quantitative contracts, invariance discipline — backed by tooling and benchmarks so the community can measure and improve operational transparency at scale.

---

## Appendix A: Technical definitions

### A.1 Axiom of choice and equivalents

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

### A.2 Constructive mathematics

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
- **Markov's Principle (MP):** For decidable predicates, ¬¬∃x.P(x) → ∃x.P(x) (sometimes)

**Schools of constructivism differ** on exactly which principles to accept. The witness budget framework doesn't assume one school, but tracks usage of various principles.

**Budget calculus treatment of Markov's Principle:**
The current budget framework treats Markov's Principle (when used) as **C3 (Classical)** for practical dashboard simplicity. This is a **policy choice for coarse binning**: MP is logically strictly weaker than full LEM (it applies only to decidable predicates and double-negated existence), but for implementation simplicity we place it at C3.

**Rationale:** MP enables non-constructive reasoning patterns similar to classical logic, even though it's technically weaker. For teams needing finer granularity, tooling could expose a sub-tier flag "C3-mp" or track MP separately in the full effect row ε (see §1.2 on multi-dimensional effects).

Future refinements could introduce a separate budget level between C2 and C3 for "weak classical principles" (MP, limited LEM for specific decidable types), but the current C0–C5 scale treats MP-dependent proofs as C3 for simplicity and actionability.

### A.3 Proof assistants

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

### A.4 Witness budget levels (formal)

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

## Appendix B: Resources and references

### B.1 Foundational books

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

**Program Extraction:**
- Letouzey, P. (2002). "A New Extraction for Coq" (Coq extraction mechanism)
- Constable, R. et al. (1986). *Implementing Mathematics with the Nuprl Proof Development System*

**Reverse Mathematics:**
- Simpson, S. G. (2009). *Subsystems of Second Order Arithmetic*

**Topology:**
- Kelley, J. L. (1955). *General Topology*. Van Nostrand.

### B.2 Key papers

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

**AI for Theorem Proving:**
- Polu, S. & Sutskever, I. (2020). "Generative Language Modeling for Automated Theorem Proving" (GPT-f)
- Lample, G. et al. (2022). "HyperTree Proof Search for Neural Theorem Proving"
- Jiang, A. et al. (2023). "Draft, Sketch, and Prove: Guiding Formal Theorem Provers with Informal Proofs"
- Thakur, A. et al. (2024). "Language Agent Tree Search Unifies Reasoning, Acting, and Planning in Language Models" (LATS, applicable to Lean)

**Program Synthesis and CEGIS:**
- Solar-Lezama, A. (2008). "Program Synthesis by Sketching" (foundational CEGIS work)
- Alur, R. et al. (2013). "Syntax-Guided Synthesis" (SyGuS framework)

### B.3 Online communities and resources

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

### B.4 Collaboration opportunities

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

**Effect System:** Type system tracking computational effects — here, oracle and classical effects in proofs

**Executable Content:** Operational artifacts extractable from proofs — witnesses (concrete objects), algorithms (procedures), bounds (explicit rates, error terms, moduli), and quantitative data beyond asymptotic behavior

**Homotopy Type Theory (HoTT):** Foundation treating equality as paths, types as spaces, with univalence axiom

**Law of Excluded Middle (LEM):** Principle that P ∨ ¬P holds for all propositions — rejected in intuitionistic logic

**Operational Content:** Extractable algorithmic content: witnesses, bounds, rates, moduli from proofs

**Proof Mining:** Systematic extraction of quantitative bounds and rates from classical proofs using logical transformations

**Realizability:** Semantic interpretation of logical proofs as computational programs

**Torsor:** Space acted on freely and transitively by a group (encodes "all choices equivalent under group action")

**Ultrafilter Lemma / Boolean Prime Ideal (ULBPI):** Every filter extends to an ultrafilter; equivalent to BPI over ZF; weaker than AC.

**Verification vs Operationalization:** Checking correctness (verification) vs extracting executable content (operationalization)

**Witness:** Explicit object or algorithm satisfying an existence claim (not just proof that one exists)

**Zorn's Lemma:** In a partially ordered set where every chain has upper bound, there exists maximal element — equivalent to AC over ZF

---

## Appendix D: Alternative verification channels

While this document focuses on constructive witnesses for operational content, there are other verification approaches worth understanding:

**1. Constructive Witness (C0–C2) — Focus of this framework**
- Provides: Executable algorithm/witness + quantitative bounds
- Properties: Verifiable AND operational
- Best for: Automation, composition, downstream computation, algorithm extraction
- Example: Banach fixed-point with convergence rate
- Trade-offs: May require additional hypotheses like moduli or separability; proofs can be more technical

**2. Classical Proof (C3–C5) — Traditional mathematics**
- Provides: Logical correctness
- Properties: Verifiable but not *operational*
- Best for: Pure existence results where witnesses unnecessary; elegant general theorems
- Example: Excluded middle arguments, non-constructive fixed-points
- Trade-offs: No extraction; less automation support; may be shorter and more elegant

**3. Interactive/PCP (Probabilistic Checkable Proofs) — Complexity theory**
- Provides: Succinct certificates verifiable via randomness
- Properties: Efficiently verifiable, usually not operational
- Best for: Complexity-theoretic results, very large proofs, cryptographic applications
- Example: Zero-knowledge proofs, PCP theorem
- Trade-offs: No algorithmic content; specialized verification model; not compositional for algorithm synthesis

**Why we focus on constructive witnesses:**
For AI systems producing executable artifacts (certified algorithms, verified software, computational mathematics), constructive witnesses provide both verification and operational content. Other channels serve important purposes but don't enable the extraction and composition goals central to this framework.

**Complementarity:** These approaches aren't mutually exclusive. A system might use classical proofs for pure mathematics, constructive witnesses for algorithmic content, and PCPs for efficient verification of large artifacts. The witness budget framework helps make explicit which approach is being used and what properties result.

---

*Document Version: 3.0*

*Last Updated: 2025-10-24*

*License: CC BY 4.0*

---

**This research program is open for collaboration.**

If you're interested in:
- Contributing to instrumentation and tooling
- Formalizing case studies constructively
- Running empirical validation experiments
- Providing feedback or critique

Please reach out through the communities mentioned in Appendix B.3, or engage with the formal methods and AI safety communities working on these problems.

**The question is no longer whether this approach has merit, but rather what empirical evidence reveals about its efficacy.**

The validation program outlined in this document will provide those answers.
