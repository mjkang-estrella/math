# Literal Bessel series core — partial, not full analytic closure

Status: preliminary formal investment only. Credit 0; campaign counts remain 6/36. No novelty clearance, acceptance, manuscript, full source theorem or unimodality certificate is claimed. Solo work; only this assigned lane was written. No git commands, network, accounts, contact, posts or uploads.

## Import and normalization

Import `BesselInterfaces` for the complete verified component; it publicly imports `BesselAnalytic`, which publicly imports `BesselRatio`. All declarations are in namespace `BesselRatio`.

`I ν z` is literally the infinite sum of `(z/2)^((2*k:ℕ)+ν) / (k! * Real.Gamma(k+ν+1))`, using Real.rpow. There is no arbitrary ODE solution as source function. `coeff ν k = 1/(4^k*k!*Gamma(k+ν+1))`; `S ν t = Σ coeff ν k*t^k`; `F ν t = Gamma(ν+1)*S ν t`. This Gamma-normalized coefficient convention is used throughout. No Pochhammer identity is asserted. The exact identity is `I ν z = (z/2)^ν / Gamma(ν+1) * F ν (z²)` for ν>−1,z>0, and F ν 0=1. The unfactored identity with S holds for every real ν when z>0, even without assuming convergence. Every convergence/positivity assertion requires ν>−1.

## Verified content

BesselRatio: `gamma_pos`, `coeff_pos`, `coeff_succ`, `term_factor`, `I_eq_rpow_mul_S`, `I_eq_normalized`, `summable_S` (all real t), `summable_term` (positive z), `I_pos`.

BesselAnalytic: `S_eq_powerSeries`, `series_radius` (radius = top), `S_analytic` (all real t), `S_zero`, `S_hasDerivAt`, `S_hasFPowerSeries` (global convergent formal multilinear series), `F_zero`, `euler_continuousAt`, `euler_zero`, `wCoefficient_limit`, `I_hasDerivAt`.

The last derivative is the explicit closed formula

    Iν'(z) = [ν*(z/2)^(ν−1)/2]*Sν(z²)
                + (z/2)^ν * [Sν'(z²)*(2*z)].

It applies also to all negative orders >−1. Its proof differentiates the genuine convergent factored series and transfers the derivative by local equality on the positive axis.

BesselInterfaces: `scaled_hasDerivAt`, `C_pos`, `ratio_hasDerivAt`. For f=Iu(ax),g=Iv(bx), W=x(f'g−fg'), the literal quotient derivative is exactly W/(x*g²), for u,v>−1 and positive a,b,x, with no order/scale comparison hypotheses needed.

The normalized Euler expression `euler ν t = ν*Sν(t)+2*t*Sν'(t)` is continuous, including at zero. The explicit coefficient `wCoefficient` has limit `(u−v)/(Gamma(u+1)*Gamma(v+1))` at zero. This theorem has NO assumed series, ODE or endpoint hypotheses. However its identification with the literal Wronskian has NOT been proved here.

Exact full elaborated types, origin modules, safety flags and transitive axiom sets for ALL 61 declarations (including compiler generated private proof declarations) are in `audit.log`; `declaration-names.txt` is the exhaustive list, and `dependencies.txt` the actual imports. The source files themselves contain the exact readable theorem statements.

## Remaining obligations — explicitly unproved

`BesselInterfaces.lean` defines the closed propositions `ScaledODE`, `WDerivative`, `WFactorization`, `UnequalEndpoint`, `EqualEndpoint`. They are definitions of work still required, NOT asserted theorems, assumptions of a claimed endpoint, or new axioms. Each refers directly to the literal I above.

Still required: differentiated-series formulas and local uniform differentiated convergence; explicit scaled C² regularity and `(x*f')'=(a²*x+ν²/x)*f`; the literal W derivative; the W factorization; normalized literal W limit for unequal orders and eventual W>0; equal-order W→0 through the x^(2v+2) factor. The proved coefficient limit alone is NOT a proof of either literal endpoint. No false W→0 assertion for unequal negative orders is made. Global one-crossing and full ratio unimodality are outside this partial component and remain unproved here.

The coefficient recurrence and infinite convergence radius are suitable starting points for finishing termwise differentiation and the normalized ODE. The equal-order algebra must cancel the zeroth-order coefficient before estimating the singular x^(2v) factor.

## Pins, audit and reproduction

Lean absolute binary and SHA256 match the task, with mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612 and pinned dependencies in `pins.json`. `package-pins-verified.json` checks actual local reference bytes without a git command. Candidate output is rebuilt only from source. Use the source-only packet, extract into a clean directory, cd there and run `bash reproduce.sh`. Readonly pinned dependency oleans are used; no candidate prebuilt is in the archive.

`Audit.lean` imports all private data of the three component modules so theorem declarations are audited as actual theorems rather than proof-pruned public-view axiom stubs. It rejects every unsafe/partial/axiom declaration and every transitive axiom outside propext, Classical.choice, Quot.sound. All 61 pass. `fresh-replay` holds an independent source-only extraction and replay receipts.

## Provenance and candid failures

Read ancestor/campaign instructions, root adjudication, r57 discovery, independent eligibility review and supplied published source text (§4 ending) from the supplied local evidence. Source/copied inputs have before/copy/after SHA256 records in input-freeze.json and input-after.json. No live prior-art refresh or novelty inference was performed. Root's current hold remains authoritative.

Resource receipts are in runs.jsonl. Lean runs use serial -j1, warningAsError=true, autoImplicit=false, CPU210s per process and sampled group CPU210s, wall230s, sampled group RSS2800MiB at45ms, BLAS1. Three initial imports exceeded the RSS cap and were killed; switching to Lean's module format kept subsequent runs below the cap. Caps were never raised. Failed development elaborations and the initial proof-pruned audit false alarm are recorded by nonzero run receipts; final source/audit/replay pass is separate.

Protocol deviations: the first inventory helper lacked explicit resource caps; initial governance/source files were read before the frozen-copy protocol was installed. Subsequent snapshots verify exact original/copy/after equality, but cannot retroactively establish a before-first-read freeze. Early metadata helpers used AS512MiB/CPU210s/timeout230s but did not use sampled process-group RSS monitoring. This is not a claim of perfect compliance with EVERY-helper resource protocol. The final replay retains strict Lean monitoring; source-freeze and packaging operations are small bounded helpers. These deviations do not introduce proof assumptions, but root should retain them in review.
