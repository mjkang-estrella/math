# Full Conjecture 3.2 remains unresolved

No nomination, no acceptance authority, credit 0. This is a continuation of
sol-fresh-analysis-discovery-r7, not a new target or a new outcome. Counts read:
3/30 additional, 33/60 total. No PROOF.md or Lean file is warranted.

## Literal target, sources, and chronology

For b<2, f_b(x)=1/(1-bx+x²),
L_n=n^(-1) sum_{k=0}^{n-1}f_b(k/n),
R_n=n^(-1) sum_{k=1}^{n}f_b(k/n), n any positive integer.
Bouthat arXiv:2311.01208v2 (16 February 2024), Section 3.1 Conjecture 3.2,
and the actual published body DOI 10.1007/s43670-024-00088-8
(9 May 2024, volume 22 article 14) both assert:

* L neither increasing nor decreasing for every 1/2<b<1;
* L increasing for every beta_+<b<=2, beta_+=(3+sqrt(13))/4;
* R neither increasing nor decreasing for every 1<b<3/2;
* R decreasing for every beta_+<b<2.

Both cached actual claim bodies and their surrounding Theorem 3.1 and Remark
3.3 were read early, before this lane's diagnostics. The published statement
matches the preprint. Theorem 3.1 already proves L increasing on [1,beta_+]
and R decreasing on [3/2,beta_+]. Remark 3.3 already handles b=2 for L.
The earlier lane's Euler–Maclaurin nonmonotonicity clauses are routine partial
results and excluded. Thus the assigned missing objective is BOTH adjacent
signs for every integer n>=1 and beta_+<b<2. No fixed n or b qualifies.

Primary URLs:
https://arxiv.org/html/2311.01208v2
https://link.springer.com/article/10.1007/s43670-024-00088-8
https://mathdb.com/p/360607/conjecture-on-the-monotonicity-of-riemann-sums-for-reciproca

Fresh cached registry receipts in r7 were reused as explicitly instructed,
without new API traversals or requests to rate-limited/forbidden hosts.
Those receipts are dated 2026-10-29T04:39 UTC: omega head
67b4fae085cf19003a33f8027410c383b49e5046, count-ex-machina
 dbf673741a54c7dc9d88a6aec0e8148a538f4a3a, OpenAI math
7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. Complete relevant trees,
count registry, current CONTENTS and two actual omega Bouthat hit bodies were
reused. Those hits concern 2026 graph norms, not this 2024 Riemann-sum claim.
There is no new target proof found by that bounded screen. The caches are
recent current-head receipts, not the October 8 immutable upstream pin.
Nevertheless this lane does NOT certify that those heads have remained current,
or that all registry manuscript bodies have been searched. Earlier same-object
papers and general quadrature subsumption are not exhaustively body-compared.
Direct MathDB 403 and the reported recent GitHub API limit remain access gaps;
no requests were made to either affected host here. Cached primary bodies and
registry hashes, original retrieval times, and local inspection times are in
provenance.json. No public HTTP requests were needed in this continuation.

Prior exclusions read: campaign ledger, NEXT, prior-campaign-context, r7
SUMMARY/discovery/checks/identities/symbolic checks, r5 analysis and r6 discrete
summaries. Previous pole-CDF ordering, real-rooted numerators, m=0 expansion
about b=1, finite-n Bernstein cone and low-mesh signs are not re-presented as
solutions. No already credited, routine, or partial family is nominated.

## 1. Expansion about a source-proved base point

Set q(x)=1-(3/2)x+x² and h_m(x)=x^m/q(x)^(m+1), m>=0.
For 3/2<=b<2, put d=b-3/2. Then

    f_b(x) = sum_{m>=0} d^m h_m(x).

This is an actual uniformly convergent geometric identity on [0,1]:
q(x)/x=x+1/x-3/2>=1/2 for x>0, so 0<=d*x/q(x)<=2d<1,
and q is positive with positive minimum on the compact interval. Thus finite
Riemann sums and their adjacent differences may be interchanged with the
series. Unlike the expansion about b=1, its m=0 right sign is already known
from the primary source, with R_1(h_0)=R_2(h_0).

It would therefore SUFFICE to prove both adjacent signs for every h_m, for
all integers m>=1 and n>=1. This sufficient all-order claim is NOT proved here.
Exact rational checks cover m=0..20 and n=1..60, both signs, with no failures.
These 1260 pairs are diagnostics, not a resolution of either infinite quantifier.

An exact moment restatement is useful. Put

    phi(x)=x/(2-3x+2x²)=1/[1+2(1-x)²/x]   (x>0), phi(0)=0,
    A_n(p)=sum_{k=1}^n phi(k/n)^p/k.

For p=m+1>=2,

    R_n(h_m)=2^p A_n(p),
    L_n(h_m)=2^p [A_n(p)-1/n].

Consequently the coefficient claim is EXACTLY

    0 <= A_n(p)-A_{n+1}(p) <= 1/[n(n+1)]

for all integer p>=2,n>=1. The p=1 left formula instead includes h_0(0)=1;
it must not be silently applied there.

### Convex-order shortcut fails, exactly

Let nu_n=sum_{k=1}^n (1/k) delta_{phi(k/n)}. A proof that
integral (u-r)_+ d(nu_n-nu_{n+1})(u)>=0 for every r would imply lower
moment inequalities for powers p>=1. But n=2,r=1/2 gives -1/24:
nu_2 has atoms 1/2 (mass1),1 (mass1/2);
nu_3 has atoms 3/11 (mass1),3/4 (mass1/2),1 (mass1/3).
The stop-loss difference is (1/6)(1/2)-(1/2)(1/4)=-1/24.
This is a falsifier of the stronger convex-order route, not of the conjecture.

The source's symmetrization-concavity criterion does not settle even h_1:
if H=(h_1(x)+h_1(1-x))/2, its second derivatives at 0,1/2,1
are exactly -9,12,-9. Thus H is neither convex nor concave. Both statements
are checked symbolically in identities.py. No general theorem for the h_m
family has been established or claimed as novel.

## 2. Exact digamma interpolation of the literal sums

Let e=2-b in (0,2-beta_+), a=sqrt(e-e²/4), z=e/2+i*a, w=1-z.
For real x>0 define the genuine smooth function

    F_e(x) = Im[psi(x*w)-psi(-x*z)]/a,

where psi is the classical digamma function. Its arguments never meet a pole.
Then, for EVERY positive integer n,

    R_n = F_e(n),
    L_n = F_e(n)+(1-1/e)/n.                       (2)

This follows without approximation. Reverse the grid j=n-k, factor
j²-e*n*j+e*n²=(j-n*z)(j-n*conj(z)), and use

 n/(j²-e*n*j+e*n²)
   = [1/(j-n*z)-1/(j-n*conj(z))]/(2*i*a).

The finite digamma recurrence sums j=0..n-1. This proves (2); it is not
merely a numerical fit. identities.py checks the algebra exactly; the
50-digit evaluations in digamma_check.py only check implementation consistency.

The derivative is exactly

    F_e'(x)=Im[w*psi_1(x*w)+z*psi_1(-x*z)]/a.     (3)

A SUFFICIENT complete analytic target is the two-sided inequality

    -(1/e-1)/x² <= F_e'(x) <= 0                 (4)

for every real x>=1 and every 0<e<2-beta_+. Integrating over [n,n+1]
would give both desired signs simultaneously. The exact discrete requirement
only asks for the corresponding integrals, so (4) is stronger than necessary.
No proof of (4), nor a counterexample to it, was obtained. The diagnostics
sample six e values and 41 logarithmic x points each and find no failure;
they do not imply the real-domain inequality.

### Reflection separates an explicitly oscillating component

The digamma reflection and recurrence identities also give

 F_e(x) = 1/(e*x) + Im[psi(x*w)-psi(x*z)]/a + C_e(x),
 C_e(x) = (pi/a) sinh(2*pi*a*x) /
                    [cosh(2*pi*a*x)-cos(pi*e*x)].               (5)

Both digamma arguments on the second line have positive real part. However,
C_e is NOT itself decreasing. At x=(2k+1)/e (integer k>=0), cosine=-1 and
sine=0, so direct differentiation gives

    C_e'(x)=2*pi²/[cosh(2*pi*a*x)+1] > 0.

These x are >=1 in the assigned e range. At x=2k/e, k>=1, the derivative
is negative. Thus treating (5) as a decreasing coth term plus benign
remainders is invalid. Bounds must control cancellation with the two digamma
terms and the rational endpoint term. This obstruction is analytic and exact.

## Remaining gap and strongest objection

Neither (4), its integrated integer-mesh version, nor the all-p moment
inequality in Section 1 has been proved. A single violating original pair
(b,n) would refute a substantive source clause; none has been found. A single
violation of (4) or of the all-coefficient strategy could instead refute only
a sufficient strengthening. The convex-order and standalone-cotangent
objections already show why two plausible routes cannot be used as proofs.

No helper, partial mesh range, finite certificate, continuous interpolation,
source confirmation or route falsifier receives credit. Full source objective
is unresolved. No formalization is attempted before a substantive complete
ordinary proof. If a proof is later found, it must still undergo current
source/registry refresh, independent review and literal pinned Lean endpoint;
this lane supplies none of those acceptance claims.

## Reproduction

Run `python expansion_check.py`, `python identities.py`, and
`python digamma_check.py` from this directory. Scripts set one BLAS thread,
512 MiB address-space limits and CPU limits <=100 seconds. Expansion uses
exact fractions; identities use exact symbolic arithmetic; digamma evaluations
are explicitly numerical diagnostics. No exponential enumeration or external
state changes. All writes stay within this uniquely assigned lane.
