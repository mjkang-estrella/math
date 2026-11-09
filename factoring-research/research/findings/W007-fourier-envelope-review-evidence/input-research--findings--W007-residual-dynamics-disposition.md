# W007 — residual dynamics disposition

2026-10-08. Parent intake of completed Grok task D.
[Original review](W007-residual-dynamics-review.md) is preserved. All four
delivery hashes passed. The child supplied a checker and finite algebraic
tables; the parent inspected them without repeating the enumeration.
They are finite checks, not factoring runs or asymptotic evidence.
Verified end-to-end factoring improvement: **NONE**.

Accept the odd-characteristic identities E[Delta z]=v and
E[Delta v]=zR+Q-D-t, including the zero-atom cancellation and the p=5
reachable example. Accept the algebraic generic depth-1 drift and derived
root expectations through depth three. The character-sum expansion in
section 3 supports these all-prime formulas; finite tables only cross-check
them. In particular E[m_3] tends to 7, not the degree 8. No persistent
growth theorem follows from those identities.

Accept the explicit triangular acquisition count, the spent-reservoir-slot
issue, and the degree argument for at least k non-scalar multiplications
in a division-free generic polynomial evaluation of degree 2^k. This is
not a lower bound on all bit algorithms, branching algorithms, or joint
multi-input acquisition. Pre-multiplication gcd checks can recover factors
masked by an endpoint full gcd, and survival conditioning must be charged.

The following repairs limit statements in the child report:

- Fixed-horizon, UNSTOPPED histories at p and q are independent when fresh
  uniform residues modulo pq supply independent CRT tapes and the updates
  are componentwise. Merely writing both components in one integer does
  not create dependence. Conditioning on a global stopping/survival event
  generally does couple them. The conditional fresh-probe formula remains
  z_p+z_q-2z_p*z_q in either case; any subsequent averaging must use the
  actual distribution under discussion.
- The advertised minimizer k=p^(1/3) is outside a stated hypothesis
  restricted to 2^k<p. The relaxed k^2+p/k expression has that minimum,
  but it is not an attainable optimizer under the logarithmic depth
  restriction. Use the actual range or explicitly assume the root bound
  for all depths before claiming a matched Theta envelope.
- An upper bound on expected roots alone yields a lower bound on this
  implementation's success-adjusted probe bill, not a matching runtime.
  Survival, early hits and full-gcd losses remain separate obligations.
- Adaptive coefficient acquisition and batch evaluation for already-known
  generic coefficients are related problems, not established equivalent
  subquadratic tasks. Adaptive dependence can prevent using a generic
  batch evaluator to acquire the very coefficients it requires.
- The pure-power joint-zero history under this rule has exact probability
  N^(-k): at each such stage its only zero modulo a squarefree N is zero.
  It is a rare selected branch, not a typical residual-growth argument.

The review's proposed depth-four calculation is superseded as the next
parent question by a new [all-depth component factorization](W007-component-factorization.md).
That provisional identity supplies a route to the triangular fixed-depth
limit via absolutely irreducible components, plus an explicit Weil-bound
upper estimate. It has been selected for independent audit. It does not
assert a growing-depth or stopped-process factoring lower bound.

No new candidate experiment, shared source edit or Lean change accompanies
this disposition. Continue constructive work on altered acquisition or a
detector that avoids the already identified materialization costs.
