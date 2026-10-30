# Literal Bessel ODE and zero endpoints — complete component

Status: all five inherited CLOSED propositions are now proved for the literal Gamma-series I. No analytic assumptions remain in these interfaces. Credit 0; novelty HOLD; full-source acceptance, the global one-crossing theorem, ratio unimodality and infinity asymptotics are outside this assignment. Current root ledger is 7/37; the inherited 6/36 adjudication is historical, not a worker update. Solo work; only this assigned lane was written; no git, network, browser, account, posts or children.

## Imports and exact interfaces

Import `BesselClosed` to obtain all results; it publicly imports `BesselODE`, which imports `BesselSeriesODE` and `BesselEndpoints`. Each publicly imports `BesselInterfaces`. All seven source modules live at the lane root. All declarations below are in namespace `BesselRatio`. The inherited three source modules and their definitions are byte-identical to the supplied archive. Inherited comments marking obligations UNPROVED describe the old core, not the new certificates.

The exact closed certificates are:

```
wFactorization : WFactorization
unequalEndpoint : UnequalEndpoint
equalEndpoint : EqualEndpoint
scaledODE : ScaledODE
wDerivative : WDerivative
```

Unfolded, for real parameters:

* `wFactorization`: for u,v > -1 and a,b,x > 0,
  W(u,v,a,b,x) = (a/2)^u (b/2)^v x^(u+v) wCoefficient(u,v,a,b,x).
* `unequalEndpoint`: for -1 < v < u and a,b > 0,
  W(u,v,a,b,x)/(C(u,v,a,b) x^(u+v)) tends to u-v as x → 0 from above.
* `equalEndpoint`: for v > -1 and a,b > 0, W(v,v,a,b,x) tends to 0 as x → 0 from above.
* `scaledODE`: for ν > -1 and a,x > 0, HasDerivAt (fun y => y * deriv (scaled ν a) y)
  ((a^2*x + ν^2/x) * scaled ν a x) x.
* `wDerivative`: for u,v > -1 and a,b,x > 0, HasDerivAt (W u v a b)
  (((u^2-v^2)/x - (b^2-a^2)*x) * scaled u a x * scaled v b x) x.

`W_eventually_pos {u v a b : ℝ} (hv : -1 < v) (huv : v < u) (ha : 0 < a) (hb : 0 < b)` proves
`∀ᶠ x in 𝓝[>] 0, 0 < W u v a b x`.

`scaled_second_hasDerivAt` proves genuine second differentiability of the literal scaled function on x>0, with derivative
`(((a^2*x + ν^2/x)*scaled ν a x*x - x*deriv (scaled ν a) x) / x^2)`.
Together with its explicit continuous formula and the inherited first derivative this gives the scaled C² regularity needed by the ODE. No global ContDiff declaration is claimed.

## Proof and source identity

`I ν z` is the literal sum of `(z/2)^((2*k:ℕ)+ν)/(k!*Gamma(k+ν+1))` using real powers; no arbitrary ODE solution replaces it. `coeff ν k = 1/(4^k*k!*Gamma(k+ν+1))`, `S ν t = Σ coeff ν k*t^k`. `scaled ν a x = I ν (a*x)` and W and C are the unchanged inherited definitions.

`scalarSeries_deriv` derives a globally convergent scalar series with coefficients `(n+1)c(n+1)` from HasFPowerSeriesOnBall at radius top. `S_deriv_series` and `S_second_series` apply this twice to the inherited entire literal series. The separately named `dc` and `ddc` are these differentiated coefficient sequences. `S_ode` uses the inherited Gamma coefficient recurrence and the actual convergent differentiated sums to prove
`4*t*deriv (deriv (S ν)) t + 4*(ν+1)*deriv (S ν) t = S ν t`
for ν>-1 and every real t. There is no local-uniform-convergence assumption; convergence and differentiation follow from the proved infinite power-series radius.

`scaled_euler` derives x f' from the literal first derivative. Product and chain rules, the normalized series ODE, and local equality on the positive axis prove `scaledODE`. The product-rule identity W=(x f')g−f(x g') proves `wDerivative` without an ODE premise.

The exact equal-order cancellation `wCoefficient_equal` is
`2*x^2 * (a^2*S'_v((a*x)^2)*S_v((b*x)^2) - b^2*S_v((a*x)^2)*S'_v((b*x)^2))`.
The bracket is continuous at zero; the remaining power is x^(2v+2), which tends to zero because v>-1. Unequal orders use the already proved coefficient limit and positive Gamma normalization, including u+v<0. No W→0 claim is made for unequal negative orders. Equal scales and all positive scales are included, without a≤b assumptions.

## Reproduction, provenance and audit

The input `base-component.tar.gz` has SHA256
`41a063e4a225bbce03d31eb3a5106c02ae7dcf38082e710ec125c72f4aee2d73`.
It is an own-lane readonly copy. The three inherited source files are readonly and hash-verified against the archive in `provenance.json`. Governance, ledger/context and adjudication copies, their before/copy/after hashes, actual eight package HEADs and expected revisions are recorded there. `pins.json` pins Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 and all eight packages. The actual Lean binary SHA is checked on every invocation. Dependencies are used readonly; no caches from changing worker lanes are consumed.

`bash reproduce.sh` rebuilds all seven modules serially then runs Audit.lean. The audit imports `all` private data of every component module and exhaustively records actual module origin, fully elaborated type, transitive axiom set, unsafe/partial/axiom flags. All 106 declarations pass. Only propext, Classical.choice and Quot.sound occur. `declaration-names.txt`, `dependencies.txt`, and `audit.log` are exhaustive receipts, not a handpicked endpoint list.

`component.tar.gz` is source-only: no candidate oleans or build artifacts. `component-manifest.json` hashes every packaged payload. `fresh-replay` is a new extraction of this packet and rebuilds only from extracted candidate source plus pinned upstream dependency caches. `delivery-receipt.json` records packet/replay/audit hashes and final outcomes. No formal gap remains in the five requested interfaces or eventual positivity.

## Failures and protocol limits

Development receipts retain nonzero runs for elaboration errors (algebra normal forms, implicit filter inference, function extensionality and strict linter failures); final build/audit/replay results are separate. One invocation accidentally inherited the Python-helper 512MiB virtual-address cap into Lean and exited 250; the normal 2800MiB RSS Lean guard was then restored, without raising any cap. No proof placeholders or forbidden declarations were introduced.

Lean `run.py` is inherited byte-identically: serial j1, warningAsError=true, autoImplicit=false, process and sampled group CPU210, wall230, group RSS2800MiB sampled45ms, BLAS1. Helper-run.py enforces AS512MiB/groupRSS512MiB CPU210/wall230/45ms/BLAS1 for provenance and packaging helpers. Early small edit helpers had AS512MiB/CPU210 but lacked the sampled helper-group monitor and explicit wall guard; initial shell reads/copies also preceded frozen provenance snapshots. This is not a claim of perfect every-helper protocol compliance. These deviations do not change the theorem types or audit. No novelty or live-prior-art refresh was attempted or authorized.
