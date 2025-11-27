# Witness Budgets Demos: Substance and Style

*A guide for future agents contributing to the witness-budgets program*

---

## Part I: The Philosophy

### What This Program Is

Witness budgets is not a research program about constructive mathematics. It's a research program about **making mathematics operational**—turning proofs into programs with certified bounds, and measuring exactly what logical machinery that requires.

The core question isn't "is the Axiom of Choice philosophically acceptable?" but rather: **"What can I extract from this proof, and what does that extraction cost?"**

### The C0-C5 Spectrum as Engineering Tool

The budget levels aren't a moral hierarchy. They're a measurement system:

- **C0**: You get executable code with no caveats
- **C1-C2**: You get code, but with some structure (quotients, sequences)
- **C3-C5**: You get logical truth, but extraction is blocked or requires oracles

A C5 proof isn't "bad" — it might be the only known proof, or the simplest, or the most general. But you should *know* it's C5, because that tells you what you can and cannot do with it downstream.

### The Dual-Track Architecture

The program's central insight: you don't have to choose between classical proofs and constructive extraction. You can have both, in parallel:

```
Proof Track (vBudget)              Extraction Track (xBudget)
─────────────────────              ────────────────────────────
• Classical reasoning OK           • Must be constructive
• Mathlib integration              • ConstructiveQ, IntervalDyadic
• Soundness theorems               • Executable witnesses
• "This bound holds"               • "Here is the bound: 47/16"
```

The **firewall** between tracks is the soundness theorem: a machine-checked proof that the constructive computation upper-bounds (or equals) the classical quantity.

### "No Computation Without Proof"

This phrase isn't marketing. It's a design principle that manifests concretely:

The semilinear heat solver has a **stability gate**. Before any time-stepping occurs, it evaluates the Lipschitz budget with exact rational arithmetic. If `dt·L ≥ 1`, the solver *refuses to run*. Not a warning, not a flag — structural prevention of meaningless output.

This is the ethos: verification isn't a post-hoc check, it's a precondition for execution.

---

## Part II: The Substance

### What Makes a Good Demo

Each demo in the series serves a specific purpose in validating the architecture. They're not isolated showcases — they're **stepping stones** on a path.

| Demo | What It Validates |
|------|-------------------|
| Banach | Basic contraction iteration, rational witness extraction |
| Newton | Quantitative convergence bounds, initial data dependence |
| Markov | Finite-state iteration, ergodic convergence rates |
| QRK-D | Spatial compactness in Fourier space, dimension-generic lattices |
| QAL | Space-time compactness, time discretization + spatial witnesses |
| FFT | Constructive O(N log N) spectral transform via algebraic recursion; validates scalability for 2D/3D |
| Heat 1D | **PDE solving** (not just metadata), stability gates, interval arithmetic |

Each demo answers: "Does the architecture handle *this* new complexity?"

### The Semilinear Heat as "Hydrogen Atom"

The 1D semilinear heat equation wasn't chosen because it's difficult. It was chosen because it's the **simplest problem containing the essential obstruction** for Navier-Stokes: controlling a nonlinearity via energy estimates.

When describing why a particular problem was chosen, explain **what obstruction it isolates**, not just what equations it solves.

### Benchmarking Integrity

Performance comparisons must be honest:

1. **Measure the right thing**: If Lean runs 4 tests and Python runs 1, say so. Use internal timing for solver-to-solver comparison.

2. **Explain the gap**: A 45× slowdown isn't shameful if you can explain *why*:
   - Interval arithmetic (2× operations + min/max)
   - GCD normalization (preventing bit explosion)
   - Immutable structures (vs mutable Python lists)
   - Bounds checking (array access verification)

3. **Context matters**: 45× is remarkable by formal methods standards. CompCert is 2-3×, typical proof-carrying code is 100-1000×. Frame the number accurately.

4. **Algorithmic parity**: If both implementations use O(N²) convolution, the comparison measures *verification overhead*, not algorithmic choices. This is valuable — say so explicitly.

5. **Engine reserve**: The Heat 1D demo benchmarks the direct method (O(N²)) to establish a baseline for verification cost. The FFT engine (O(N log N)) is verified and held in reserve for 2D/3D, where it becomes mandatory for tractable Leray projection.

### Budget Analysis: What to Report

For each demo, the budget analysis should include:

- **Total declarations** and **C0 percentage** (e.g., "576/707 = 81.5% C0")
- **Module breakdown** showing where classical dependencies concentrate
- **Explanation of C5 sources** (often structure proof fields that get erased)
- **The vBudget/xBudget distinction** when it matters

Don't just report numbers — explain what they mean for extraction.

---

## Part III: The Style

### Tone: Professional Objectivity

The work speaks for itself. Avoid:
- Superlatives ("amazing", "incredible", "breakthrough")
- Excessive validation ("You're absolutely right")
- Hedging that undermines confidence ("hopefully", "we think maybe")

Prefer:
- Factual claims with evidence ("45× slowdown, measured via internal timing")
- Direct acknowledgment of limitations ("The C5 dependencies arise from structure proof fields")
- Confident but not boastful framing ("This validates the computational architecture")

### The "Map, Not Promise" Principle

When discussing future work (especially Navier-Stokes):

**Don't say**: "We will solve NS next" / "NS is just engineering now"

**Do say**: "This architecture was designed for the obstructions in NS" / "What remains is scaling the mathematical formalization — Leray projection, H² embeddings — rather than reinventing the execution engine"

The distinction:
- **Map**: "Here's the territory, here's why our tools apply, here's what's validated"
- **Promise**: "We're definitely doing X by date Y"

Maps are intellectually honest. Promises create accountability for things outside your control.

### Formatting Conventions

From the style guide and established practice:

| Element | Convention |
|---------|------------|
| Headings | Sentence case preferred ("Design rationale" not "Design Rationale") |
| Emphasis | Bold or *italics*, never ALL CAPS (except status indicators in tables) |
| Abbreviations | Expand on first use ("Navier-Stokes (NS)"), then can use short form |
| Em-dashes | Spaced (`word — word`) for screen readability; Chicago exists, we're not writing for print |
| Emoji | None in body text. Checkmarks (✓/✗) acceptable in diagrams |
| Colloquialisms | Avoid ("rehash" → "reiterate", "gotcha" → "caveat") |
| Defensive qualifiers | Remove ("(for clarity)" is unnecessary if the text is clear) |

### Document Structure

Demo results documents should include:

1. **Header**: Date, status, classification
2. **Executive summary**: Key achievements in bullet form
3. **Architecture diagram**: ASCII art showing the flow
4. **Mathematical content**: The actual problem being solved
5. **Demo execution**: What runs, what output looks like
6. **Performance**: Internal timing (primary), hyperfine (secondary with caveats)
7. **Budget analysis**: C0 percentages, module breakdown
8. **Comparison table**: This demo vs prior demos
9. **Key insights**: What we learned
10. **Design rationale**: Why this problem, what it validates
11. **File inventory**: Where the code lives

---

## Part IV: The Ethos

### Verification Cost as "Price of Truth"

The 45× overhead isn't a failure to optimize. It's the **cost of certainty**:

> "Every arithmetic operation in the Lean solver computes the result (same as Python), updates interval bounds (additional work), normalizes representation (GCD computation), and verifies array indices (bounds checking). This overhead is the price of certainty."

In domains where correctness matters more than speed — aerospace, medical devices, financial systems, cryptography — this price is a bargain.

### Practical Constructivism

This program isn't about philosophical purity. It's about **building things that work**.

The question isn't "Is AC morally wrong?" but:
- "Does this proof give me something I can run?"
- "What are the bounds, and are they tight enough?"
- "Can I compose this with other verified components?"

A C5 proof that you understand is better than a C0 proof that you don't. But if you need extraction, you need to know you're at C5 so you can build a firewall.

### Walking the Walk

Every claim should be backed by:
- **Running code**: The demos actually execute
- **Measured performance**: Hyperfine with sufficient runs
- **Analyzed budgets**: JSON files with per-declaration classification
- **Compared baselines**: Python implementations for validation
- **Complete proofs**: Zero sorries in the dependency chain, no user-defined axioms — budget analysis requires it

Position papers are cheap. Working code with measurements is expensive. This program pays the expense.

### The Golden Path

There's a vision here, even if we don't trumpet it:

```
Banach → Newton → Markov → QRK → QAL → Heat 1D → ... → Navier-Stokes
        ↓         ↓         ↓      ↓        ↓
     iteration  bounds   finite  spatial  space-time  nonlinear
     witness    depend   state   compact  compact     evolution
                                    ↑
                                   FFT ←── scalability for 2D/3D
```

Each demo validates architecture for the next. The path is clear; the pace is determined by the mathematics, not by announcements.

---

## Part V: What Resonates

The integration of **pragmatism and principle** is what makes this program distinctive.

It's not "constructive math is philosophically superior" — it's "here's what you can extract from C0 that you can't from C5, and here's the measured cost."

It's not "you shouldn't use classical reasoning" — it's "know where you're using it, and build firewalls where extraction matters."

It's not "we're solving the millennium prize problem" — it's "here's the map, here's what's validated, here's what remains."

The stability gate is the perfect embodiment: it doesn't *advise* against unstable parameters, it *structurally prevents* execution without proof. The verification isn't in a README warning — it's in the type system.

This is what constructive mathematics looks like when it's serious about being useful: not a purity test, but an engineering discipline with measurements and trade-offs and working code.

---

## Closing

When contributing to witness-budgets, remember:

1. **You're building toward something**: Each demo is a stepping stone, not an endpoint
2. **Measure what you claim**: Performance, budgets, coverage — with numbers
3. **Explain the gaps**: Limitations honestly acknowledged build trust
4. **Map the territory**: Describe what's validated without overpromising
5. **Let the work speak**: Professional, factual, confident without hype

The framework doesn't demand perfection. It demands **honesty about where you are** on the spectrum between pure logic and executable code — and the discipline to improve that position when extraction matters.

---

*"The stability gate represents a philosophical shift: from 'trust the numerics' to 'prove the numerics.' In a world of increasingly complex simulations, this is not academic pedantry — it's engineering discipline."*
