# W007 tau-acquisition disposition and parent corrections

2026-10-08. Claude Opus 5.5 review completed under the user's explicit model
authorization. Parent read the full [report](W007-tau-acquisition-review.md)
and verified its delivery hashes. Original report is preserved; this
disposition controls which claims are adopted.

**Accept the explicit conversion.** For a_j=u_j/v_j with nonzero v_j, not
necessarily reduced, A_(j+1)=A_j(v_j A_j-u_j D_j) and D_(j+1)=v_j D_j^2
give A_j=D_j P_j with leading coefficient D_j. Homogenizing at V=D_k scales
each rational root by D_k to an integer root. The short homogeneous recurrence
really computes this polynomial without listing its roots or coefficients.
Its circuit length is O(k+T), including the constant circuits T; adaptive
rational training yields O(k^2+T_training). Division-generated constant
circuits convert to numerator/denominator circuits with constant overhead
when no division is by zero. Expanded heights are not automatically the
circuit length.

Thus a family with superpolynomially many rational roots relative to these
paid constant-free circuits would contradict the integer-root tau conjecture.
This is a conditional connection, not a proved impossibility or a factoring
algorithm. A finite eight- or sixteen-root witness does not decide it. The
review did not retrieve the original Shub-Smale/BCSS text or Lipton's full
theorem; those exact literature claims remain limited to the reported read
scope. The proved weak root bounds cited do not exclude this recurrence's
degree-scale root count.

**Correct the modular-only and input-dependence statements.** A fixed N,
random tape and residue coefficient list DOES have an integer polynomial
lift. Input-dependent families can also fall under tau, which quantifies over
all integer polynomials. The relevant escape is that many roots modulo p
do not assert many rational/integer roots of the lift. No contradiction
follows from merely rich finite-field roots. Do not repeat the report's
phrases "no polynomial in Z[x] is defined" or "tau never applies" for
N-dependent constants.

**Do not adopt F2 as a universal necessity theorem.** Polynomial rational
root height and R>=p are possible sufficient ingredients for some
average-prime arguments, not necessities for every factoring use.
R>=p/poly(log p) can already permit inverse-polynomial density, and direct
modular separation certificates can replace a height-based average bound.
Denominator-bad primes, quantifiers and the actual input factor distribution
need treatment before using the report's averaging argument. Its proof is
not used as an accepted supply theorem. Also gcd(D_k,N)=N is a failed chart,
not a unit; the report's dichotomy omits this branch.

**Correct the cost threshold.** In a specified model with k^2 training work,
k work per fresh probe and actual proper-factor probability s_k, the model
cost is k^2+k/s_k. Matching sqrt(p) requires both k=O(p^(1/4)) and
s_k=Omega(k/sqrt(p)), with the actual constants/scope of that model. A strict
asymptotic improvement requires k=o(p^(1/4)) and s_k/(k/sqrt(p)) tending to
infinity, apart from other costs. The report's z_k>=k^3/p is weaker for
k<p^(1/4) and is not a sufficient matching criterion there. Nor does a
pointwise bound E[v_j]>=j^2/p follow as a necessary condition: growth may
occur unevenly. The exact success law and cumulative mass, not that proposed
derivative threshold, are the gate. Zero mass cannot replace proper-factor
probability when the other component is saturated.

Constructive priority: keep the finite rational probe bounded; pursue actual
finite-field fiber generation and the parent pair-selected update, which
has a distinct additive-energy law. Grok's existing residual audit remains
live and unchanged. No need to duplicate it to correct these supplemental
Opus claims. No numerical experiment or shared code/Lean edit was made.
Verified complete factoring complexity improvement: NONE.

