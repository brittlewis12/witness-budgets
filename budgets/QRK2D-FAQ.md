# QRK‑2D FAQ (Constructive, Extractable Rellich–Kondrachov in 2D)

### 1. Is this *really* constructive? Which axioms are used?

Yes. The witness layer (budgets, `roundToGrid2D`, cutoff/mesh formulas) lives entirely in the constructive budget tiers (pure rational arithmetic, total functions). Classical reasoning stays inside `Prop`; no Law of Excluded Middle or Axiom of Choice appears in extracted data or control flow.

### 2. What exactly do I get out of the theorem—just existence, or a real algorithm?

A concrete algorithm. Given ε,R ∈ ℚ, we compute the cutoff  
`M = ⌈R/(π_lb·ε)⌉ + 1`, the mesh `δ = ε/(4(2M+1))`, and a rounding map `roundToGrid2D`. The Lean demo and Python baseline both run this procedure and output an explicit witness.

### 3. What conventions are we working with?

All statements are on the 2-torus 𝕋² with mean-zero functions. Frequencies are truncated in the ℓ∞ box `K_M := {k : ‖k‖∞ ≤ M}`, so there are `(2M+1)² − 1` retained modes, and the tail estimates use the ℓ² norm via `‖k‖₂ ≥ ‖k‖∞`. The rational lower bound π_lb (default defined in `budgets/Budgets/QRKConstants.lean`) keeps all arithmetic in ℚ. JSON schemas for inputs/outputs live alongside the CLI helper scripts in `io/qrk2d_schema.json`.

### 4. What inputs does the certifier expect?

(ε,R) ∈ ℚ × ℚ plus finitely supported Fourier coefficients `{a_k ∈ ℚ + iℚ}` on 𝕋² with zero mean. Workflow: subtract the mean, compute Fourier coefficients (FFT + interval rounding), package as JSON or Lean structures, and pass them to the certifier. Hooks for mesh-based projectors are planned for non-periodic domains.

### 5. How do I obtain the H¹ budget R in practice?

From your PDE/controller energy estimates. On 𝕋², an L² bound on ∇u gives R via Poincaré; for PINNs, a training loss bound or weight-norm surrogate can provide it. See `scripts/qrk2d_compute_R.py` for recipe code.

### 6. How does the L² bridge work?

`RellichKondrachov2D/L2Bridge.lean` maps mean-zero H¹ functions on 𝕋² to ℓ²(ℤ²) via orthonormal product characters. Lemmas `orthonormal_Ek`, `bessel_rect`, and `tail_bound_L2` are proved directly in Lean, so the sequence-level theorem `gridFinset_sound_2D` (in `budgets/Budgets/RellichKondrachov2D.lean`) applies verbatim; the witness is then interpreted back in L².

### 7. Do you redefine Sobolev spaces constructively?

No—we stay on the Fourier side:  
`Σ_k (1 + 4π²|k|²) |⟨u, E_k⟩|² ≤ R²`.  
That equals the classical H¹ seminorm under Parseval, avoiding constructive completion issues while keeping the computational content explicit.

### 8. How are real numbers represented?

All extracted data lives in ℚ. When the proofs mention ℝ (L², H¹), we use Lean’s standard Cauchy completion of ℚ. No extra choice principles (LPO, LLPO, fan theorem, etc.) are assumed beyond Mathlib’s foundation, and classical reasoning stays inside `Prop`.

### 9. What quantitative guarantees do I get?

- Tail bound: `Σ_{|k|>M} |a_k|² ≤ R²/(4π² M²)`.  
- Mesh: `δ = ε/(4(2M+1))`.  
- Index count: `(2M+1)² − 1`.  
These originate from `(1+4π²|k|²) ≥ 4π²M²` when `|k|>M`, so the weighted H¹ budget controls the tail. `π_lb = 3` is the certified rational bound defined in `budgets/Budgets/QRKConstants.lean`.

### 10. What is the computational content of the witness?

A single ε-approximate grid point (factored representation). We never enumerate the entire ε-net; instead we compute the rounding witness directly and log every budget (M, δ, coefficient boxes) for audit.

### 11. How competitive is the implementation?

Lean demo (50 runs): **34.1 ms ± 1.4 ms**.  
Python baseline (Fractions): **23.6 ms ± 1.2 ms**.  
Both operate on ℚ arithmetic. That’s fast enough for certification tasks and demonstrates that extraction produces usable executables.

### 12. Does this help classical analysts or FEM practitioners?

Yes—as a certifier. Run your FEM/PINN/spectral solver, map the result to Fourier coefficients, then call the QRK‑2D executable to get a formally certified ε-bound. Because the witness data is rational, auditors can check it independently without rerunning Lean.

### 13. What about AI safety / verified autonomy?

Witness budgets provide an auditable computation trace: every cutoff, tail split, and rounding choice is explicit. That blueprint generalizes to constructing interpretable, formally certified components (e.g., verified neural ODE modules).

### 14. How far are we from 3D or more complex domains?

The analytic core (dimension-free tail bound plus factored witness) scales directly. Extending to 3D is mostly index bookkeeping; moving beyond periodic domains will pair QRK with verified projectors so domain parameters explicitly feed the budgets.

### 15. What remains to be done?

- 3D torus implementation.  
- An application demo (e.g., heat-equation stabilizer or verified planner).  
- Public APIs for the L² bridge/projector layer so other teams can plug their solvers in easily.

### 16. Why “QRK”? How does this relate to Bishop/Bridges or CCA work?

QRK = **Quantitative Rellich–Kondrachov**: the proof carries explicit tail/mesh bounds all the way to executable code. Classical constructive proofs (Bishop/Bridges, computable analysis) derive moduli informally; QRK‑2D machine-checks them in Lean and exposes the computational content.

### 17. What is the cost compared to a classical proof?

About 377 lines for `Seq.lean`, 727 lines for the parent-level soundness file, and 480 lines for the L² bridge. Most of that is reusable witness-budget infrastructure; no Mathlib forks were needed.

### 18. How trustworthy is the extracted code?

Extraction targets Lean VM/C via the standard pipeline. The trusted base is Mathlib + Lean runtime. Because outputs are rational tables, you can export them (JSON/CSV) and verify them independently in any environment.

### 19. Can I use floating point or interval arithmetic downstream?

Yes. Treat the witness as an exact rational certificate. You can convert it to floats with interval guards or keep it in rationals while your main solver runs in double precision; QRK acts as the a posteriori validator.

### 20. Does QRK‑2D handle CFL/stability analysis?

Not directly. QRK proves compactness (total boundedness) with explicit constants; time-stepping stability remains the responsibility of your solver. Use QRK as the verification layer once the solver satisfies the mean-zero H¹ hypothesis.

### 21. What benchmark parameters were used, and how does performance scale?

The reported runtimes are for ε = 1/10, R = 5, giving `M = 18`, `δ = 1/1480`, and 1,368 low-frequency modes. Runtime/memory scale like O((R/ε)²) in 2D (O((R/ε)³) in 3D); no micro-optimizations have been attempted yet.

### 22. Should I treat QRK‑2D as a solver or as a certifier?

As a certifier. Keep your existing solver; QRK consumes its output and emits the witness/ε-bound. It is not meant to replace FEM/PINN solvers but to certify their outputs.

### 23. How do I package the certificate for auditors or regulators?

Export `{ε, R, M, δ, rounded coefficients}` as JSON/CSV along with a hash of the Lean proof artifact. Auditors can recompute the norms and confirm the ε-bound without rerunning Lean, matching DO‑178C/ISO 26262 evidence patterns.

### 24. What’s the roadmap beyond the torus?

Combine QRK with verified projectors (patchwise Fourier, wavelets, or FEM) so that arbitrary bounded Lipschitz domains inherit the same constructive budgets. Constants will then depend explicitly on domain diameter, chunkiness, Poincaré bounds, etc.

### 25. Can witness budgets certify PINNs or neural ODEs?

In principle, yes: once you derive an H¹ bound for the learned model, the QRK certifier supplies the ε-witness. Automating that H¹ bound for neural networks is an open engineering problem currently under investigation.

### 26. How does this compare to earlier constructive compactness proofs?

Earlier work (Bishop/Bridges, computable analysis) produced informal constructive proofs with moduli; QRK‑2D formalizes the same quantitative data in Lean, keeping every bound explicit and extracting an executable witness.

### 27. Can this run in real time?

Today it’s an offline/outer-loop tool (tens of milliseconds). To embed it in a kHz control loop you’d need WCET certification and platform-specific tuning; the rational arithmetic structure makes that feasible but it hasn’t been done yet.

### 28. What do the “C0/C2 budgets” mean?

Our witness-budget ladder (C0–C5) classifies how much classical power a result spends. C0 means “fully witnessful” (total functions, purely constructive), C1–C2 allow limited classical reasoning in Type, and higher tiers keep classical logic inside `Prop`. In QRK‑2D the data layer (witnesses, cutoffs, meshes) stays in C0, while proof-only obligations may sit in higher tiers without affecting extraction.

### 29. How do I feed data into the certifier again?

Provide the rational ε,R pair plus a finite map `k ↦ a_k` (complex rationals) with mean zero. We supply helper scripts to serialize/deserialize this data; projector adapters will land alongside the non-periodic pipeline.

### 30. What modulus or rate does QRK‑2D provide?

Modulus / rate (constructive form):
With π_lb < π a certified rational lower bound, choose
`M := ⌈R/(π_lb·ε)⌉ + 1`, `δ := ε/(4(2M+1))`.
Then `N(ε) := (2M+1)² − 1 = O((R/ε)²)` in 2D (and `O((R/ε)³)` in 3D). Metastability: for any `g : ℕ → ℕ`, there exists `N = O((R/ε)²)` so every H¹-bounded sequence has L²-diameter ≤ ε on `[N, N + g(N)]`.

### 31. Are the bounds uniform over domain families?

On 𝕋², yes. For general bounded Lipschitz domains, uniformity will come from the planned projector layer where domain parameters (diameter, chunkiness, Poincaré constant) explicitly feed the budgets.

### 32. Does QRK‑2D enumerate ε-nets?

No. We compute a selector (single witness) per input. The modulus `N(ε)` simultaneously bounds the size of any ε-net, so you *could* enumerate one by iterating the selector over the truncated lattice, but we avoid that to keep runtimes tiny.
