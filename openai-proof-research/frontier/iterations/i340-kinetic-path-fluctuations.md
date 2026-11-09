# I340 — functional hard-sphere fluctuations on a regular kinetic lifespan

2026-10-13. Pin: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

**Verdict: UNRESOLVED.** The requested D([0,T],Rᵐ), J1 limit for the actual exactly centered hard-sphere gas is neither proved nor refuted. No finding is nominated and no count increment is recommended. The supplied 15/20 count has no bearing on the evidentiary threshold.

The [analysis](../experiments/i340_kinetic_path_fluctuations/analysis.md) contains the full proofs of the paid partials and the missing operation. The [reading record](../experiments/i340_kinetic_path_fluctuations/reading-and-failures.md), [authentication](../experiments/i340_kinetic_path_fluctuations/input-authentication.json), and [literature comparison](../sources/i340_kinetic_path_fluctuations/literature.md) delimit what was actually checked. Only these five assigned deliverables were written.

## Exact scope

H denotes the pinned `Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026` manuscript. The initial law is its normalized grand-canonical product activity with pair exclusion on R³ₓ×R³ᵥ, diameter ε, μ=ε⁻², including N=0. Its smooth probability f₀ and ∇ₓf₀ have spatially summable Gaussian bounds at exponent 2β. The given nonlinear Boltzmann solution is classical, nonnegative, and uniformly Gaussian on the **entire supplied fixed** [0,T]. Tests are a fixed finite list of real C_c^∞ phase-space functions. Dynamics are deterministic elastic hard spheres, and centering uses the exact microscopic expectations at every t.

H's `thm:main` identifies all fixed finite observation laws but explicitly does not assert path-space tightness. §06 `thm:sharp-cumulants` controls fixed-order factorial cumulants and retained record weights on one pasted process. Its qualitative cycle removal and finite-record variation bounds are not automatically short-window bounds.

## What is proved here

1. **Continuous target coordinates.** The supplied parent proof was independently verified against H §02. For a fixed compact smooth φ, the Gaussian weak drift has uniformly bounded L² norm, and the Gaussian noise has fourth increments bounded by C|t−s|². Tonelli and Kolmogorov construct a continuous coordinate modification. A finite vector preserves the source's full joint backward covariance and its Poisson initial covariance.
2. **Uniform exact-centering transfer.** The parent argument was checked against H §§02,05,08. A simultaneous bound by 2||φ||∞N times the global discrepancy indicator gives sup_t|EΣφ_true−EΣφ_pasted|/√μ→0. The two exactly centered paths are uniformly close in probability. Thus a proved pasted path limit would transfer to the true gas. This is not a tightness proof.
3. **Uniform endpoint moments and a functional integral partial.** A direct examination of the partial-final-slab bounds, complexity removal, fresh-label coefficients, and merger majorant gives uniformly bounded fixed even moments of each pasted instantaneous coordinate at all deterministic times. Hence for any fixed finite tests b_j the **indefinite integrals** ∫₀ᵗζ_rᵋ(b_j)dr converge in C([0,T],R^q) to ∫₀ᵗζ_r(b_j)dr on the full lifespan. The proof uses moment convergence under a dominated time integral and a tight random Hölder constant. It does not assert the unsmoothed target.
4. **A mesoscopic fourth-increment estimate with a uniform qualitative loss.** Retained trees with trivial initial cumulants supply a short-window factor. For the pasted process the proof yields

   E|X_tᵋ−X_sᵋ|⁴ ≤ C[(t−s+rᵋ)²+μ⁻¹(t−s+rᵋ)],

   for some rᵋ→0 independent of s,t. Uniformity is derived using a fixed two-pulse graph class, bounded tests, and removal of pulse placement restrictions in absolute upper bounds. No rate or microscopic closure for rᵋ is obtained.

These are source-relative technical consequences, with old-argument and parent credit. They have not had fresh independent proof review and are not claimed substantial or worldwide new.

## Where the functional proof stops

Exact telescoping decomposes each fluctuation into its initial value, the integrated centered transport drift, and its centered collision current. The drift is paid. Collision-current C-tightness is unpaid. No martingale property is available merely from the deterministic flow and random initial law.

For a retained tree, an incident contact has a free merger time; localizing it to a window changes the ordered simplex bound by a polynomial graph-size factor times the window length. Those polynomial factors are summable with the source's factorial denominators. A redundant contact instead has a **determined** time; its coarea integral is an intersection indicator. The source's first-redundant-contact argument only makes its normalized total mass tend to zero. It does not give a shrinking-window factor, a centered maximal estimate, or an error compatible with the microscopic cutoff.

Specifically, the BGSS-style GRR argument at αᵋ=μ⁻⁷ᐟ³ and γ=7/3 amplifies an additive fourth-moment error by α^{1−γ}=μ^{28/9}. The qualitative rᵋ in the paid estimate is insufficient. Choosing another cutoff requires proving the accompanying microscopic modulus at that same scale. Small jumps, fixed-record TV bounds, and a global true/pasted coupling do not supply it.

The missing operation is a window-localized connected contact estimate preserving the μ root gain and summability for redundant marked contacts, through all restarts and normalized remainders, plus a valid microscopic closure. Alternatively one could prove an appropriate mixed-increment/Aldous/maximal estimate directly. Neither operation was completed. H §05's primitive close-pair gain includes an additional velocity-closeness condition and controls cutoff witnesses; it is not the arbitrary two-collision estimate needed for microscopic modulus control.

## Comparison and disposition

[BGSS 2008.10403v2](https://arxiv.org/html/2008.10403v2) already give nonequilibrium short-time process fluctuations and the relevant modified GRR, fourth-moment, and microscopic-cutoff mechanism. Their Theorem 10 point 3 and its actual proof were examined. The obstacle is extending its event-time localization to H's longer-time layered graph classes, not inventing GRR. [BGSS 2201.04514v1](https://arxiv.org/html/2201.04514v1) already prove the all-time equilibrium process result; their stationarity patching does not apply to this f₀. H's inventory companion for stable radial potentials and I23's unresolved potential resummation are outside the present target.

A complete unsmoothed theorem under these exact hypotheses would extend the known comparison range in an important way. This assignment establishes no such theorem and no global novelty claim. No arbitrary artificial process is offered as a counterexample to the gas. The appropriate next research task is the specific marked redundant-contact/window closure, rather than a full-target acceptance gate.
