# Mittag-Leffler analytic foundation — complete component, not source resolution

2026-10-28. Fresh strict source replay PASS: 12 modules,117 declarations,
standard three axioms only, all twelve module logs empty. Root read every actual
type/axiom report, including printed source definition and CM quantifiers.
No proof of SourceClaim370772 exists here. No acceptance or discovery credit.

Delivered:
- EulerMoments: actual positive finite product equals a quotient of Mathlib
  GammaSeq values, tends to the literal Gamma ratio, is nondecreasing for
  beta in[0,1], and is bounded above by that ratio for all q>=0.
- SeriesConvergence: actual complex sum z^n/Gamma(a*n+b) is summable for
  every a,b>0,z in C; no Stirling assumption. Split into residue classes
  with stepm*a>=1; Gamma monotonicity and recurrence give an eventual
  geometric ratio bound. Literal mittagLeffler and HasSum are defined/proved.
- SourceDefs: genuine even/odd decomposition; literal sourceExpression,
  completely-monotone-positive definition (C-infinity, not analytic-order
  omega), and exact SourceClaim370772 quantifiers.
- RealAnalytic: actual real series has infinite convergence radius and is
  analytic everywhere; literal sourceExpression is C-infinity globally.
- NormBridge: the source expression equals the genuine squared modulus
  |E_a(i sqrt(t))|^2 for a>0,t>=0, not an assumed formal interface.
- Approximation: actual finite-product coefficient nonnegativity, Gamma
  domination and convergence; the whole complex transforms converge to
  the literal E_a(z) by a summable majorant and Tannery's theorem.

Index convention: for n>=0, set N=n+1. momentApprox uses N+1 mixture
factors (k=1..N+1) with scaleN^(1-beta). This shift makes its GammaSeq
quotient exact. It differs from the N-factor presentation in the frozen
ordinary proof by one extra factor, which tends to1. Monotonicity and
Gamma domination for this actual shifted definition are proved in Lean;
no identity with the earlier N-factor expression is assumed.

- DifferenceCriterion: arbitrary positive mixed lower differences imply all
  alternating derivative signs for a globally C-infinity function. The
  property is preserved under positive scalar sums, interval averages and
  pointwise limits on positive arguments; exponential Laplace kernels satisfy it.
- SourceAssembly: the actual squared approximants converge to the literal
  source expression. The final assembly theorem is CONDITIONAL on positive
  mixed differences of those approximants; its premise is printed explicitly.

- BetaAverages: genuine atom/Beta-density interval operators are normalized,
  continuous and positive on nonnegative intervals, reproduce exact rpow
  moments, are norm-contractive, preserve mixed-difference positivity, and
  commute with bounded pointwise limits. The actual finite-product moment
  is their iterated average, including the chosen index shift.
- AveragingRepresentation: actual half-order Mittag-Leffler partial sums
  have a summable uniform majorant; the finite average of the literal
  E_(1/2)(z sqrt(v)) equals approxTransform, proved through dominated
  convergence. This is a closed identity, not an assumed representation.

- ComplexAnalytic: the literal complex Mittag-Leffler series is entire,
  through its actual infinite-radius formal multilinear series, hence continuous.
- SquaredAverage: continuous real-linear integral commutations identify the
  actual squared approximant with a double real average of the literal
  halfCross kernel. All kernel/averaged-kernel continuity requirements are
  discharged. sourceClaim_of_halfCross_positive supplies the full source
  conclusion under an EXPLICIT unproved two-scale kernel positivity premise.

Remaining: prove nonnegative mixed differences of the actual halfCross kernel
for both scales >=0. See CONNECTION-GAPS.md. An alternate positive one-dimensional
Laplace formula is derived in ONE-DIMENSIONAL-KERNEL.md, with20diagnostic checks;
it is not yet a Lean theorem. No unconditional source certificate is claimed.
The source question still has independent source/novelty/substantive review
running in a separate Pi lane; no PASS inferred from these components.

Run python3 verify_component.py. It asserts the exact Lean binary/version
and8packagepins, compiles a new source-only temporary copy, checks all117
names/types/axiom closures, and writes verification/audit.json and Checks.log.
No source files from the independently reviewed frozen root-r12 were changed.
