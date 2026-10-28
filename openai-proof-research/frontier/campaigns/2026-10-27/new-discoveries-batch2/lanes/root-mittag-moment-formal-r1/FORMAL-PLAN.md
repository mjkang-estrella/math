# Remaining source-level bridges, with a measure-light implementation option

Use the reviewed full ordinary proof if it survives independent screening.
The following is an implementation plan, not proved Lean mathematics.

For beta=2a in(0,1], define the positive normalized averaging operator

 T_(k,beta)(f)(x)=beta*f(x)+(1-beta)*integral_0^1 f(x*u^(1/k))du, k>=1.

For q>=0, its moment at x>=0 is
x^q*[beta+(1-beta)*k/(k+q)]=x^q*(k+beta*q)/(k+q).
Continuity at u=0 follows from positive exponents; q0 handled separately.
Iterate k=1..N+1 and evaluate x=N^(1-beta), N>=1. This realizes the exact
momentApprox currently formalized. Using finite iterated interval integrals
can avoid explicit product probability spaces, Bernoulli independence,
Gamma-distribution moments and stable-law existence altogether.

The operator preserves constants, positivity, finite sums/scalar multiples,
complex conjugation and dominated uniform series. The scale stays in[0,C]
with C=N^(1-beta), so the E_(1/2) power series is uniformly dominated by
E_(1/2)(|z|sqrt(C)), already summable by SeriesConvergence. Its moment
image is exactly approxTransform from Approximation. Prove this identity;
do not assume it as a surrogate for the literal series.

For two independent copies (or two commuting iterated averaging operators),
the squared transform norm is the double average of
Re[E_(1/2)(i sqrt(vt))*conj(E_(1/2)(i sqrt(wt)))].
The generic positive angular Laplace kernel in root-r12/PROOF.md identifies
this with an average of exp(-tL) with L>=0. Prove the half-normal/erfi
formula or a directly equivalent E_(1/2) integral identity first; currently
no such theorem is included. Mathlib has real/complex polar change-of-
variables, but restriction to a rectangle and angular split remain work.
Zero v/w are handled by continuous extension or their elementary e^(-St)
case; do not silently drop the averaging endpoints.

For formal derivative signs it is easier to strengthen the finite-difference
premise to arbitrary positive steps h1,...,hk, rather than one repeated h.
The Laplace kernel yields exp(-tL)*product_j(1-exp(-h_j L))>=0. This survives
averages and pointwise transform limits. For a C-infinity f, arbitrary mixed
lower differences imply complete monotonicity by induction: all mixed
differences of f are antitone, so their negative derivatives are nonnegative;
derivation commutes with finite shifts/differences. Equivalently prove the
standard repeated finite-difference normalized limit. sourceExpression is
already globally C-infinity, so no analytic premise needs to remain.

These generic tools and all helper declarations remain uncredited. The final
endpoint must be SourceClaim370772 with no averaging, positivity, series,
convergence or derivative-premises. Source/journal/prior-art and substantive
reviews remain separate mandatory gates before any discovery acceptance.
