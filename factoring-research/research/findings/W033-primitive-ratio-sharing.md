# W033: remove repeated ratios and count actual separating events

Parent construction, 2026-10-08. **Accepted with sampling/localization
qualifications** in [the independent review](W033-ratio-sharing-review.md).
No numerical experiment.
Verified complete factoring improvement: **NONE**.

The random oblique grid has explicit pairs i*u-j, 1<=i,j<=H. A proposed
shared polynomial Q_H(U) naively has H^2 linear factors. Before paying for
its full degree, remove duplicates over the rationals, retaining the exact
separation criterion rather than only the product's zero set.

Write i=g*a, j=g*b with gcd(a,b)=1, and let

    P_H={(a,b):1<=a,b<=H, gcd(a,b)=1},
    m(a,b)=floor(H/max(a,b)),
    L_(a,b)(U)=aU-b.

The exact integer-polynomial identity is

    Q_H(U)=C_H * product_((a,b) in P_H) L_(a,b)(U)^m(a,b),
    C_H=product_(1<=i,j<=H) gcd(i,j).

For N=pq and H<p<=q, every factor of C_H and every leading coefficient
a is a unit modulo N. Each repeated edge g*(a*u-b) has the same gcd with
N as its primitive edge. Thus removing multiplicities preserves existence
of a proper edge, including when a total product has full gcd. Define the
squarefree rational-root product B_H(U)=product_(P_H)(aU-b), with tags.
Do not assume that evaluating B_H alone resolves full gcds. In the no-alias
range below, a tagged product tree gives paid localization. Outside that
range, a globally full leaf can mask useful siblings: scan all primitive
leaves, exclude all globally full leaves at paid cost, or reconstruct the
accepted H-point row consumer. An arbitrary one-path descent is insufficient.

The number of factors is

    d_H = 1+2*sum_(h=2..H) phi(h)
        = 2*sum_(h=1..H) phi(h)-1.

For the work gate one does not need a totient asymptotic. At least H^2/4
pairs are coprime: a noncoprime pair has a common divisor d>=2, so its
count is at most sum_(d=2..H)floor(H/d)^2 <= H^2*sum_(d=2..infinity)d^-2.
The latter sum is strictly less than 1/4+integral_(2..infinity)x^-2 dx=3/4.
Hence H^2/4<d_H<=H^2 (the H=1 endpoint is also valid). Removing repeated
rational ratios changes the dense degree by at most a constant factor.
An explicit gcd enumeration costs soft O(H^2*poly(log H)); a Farey-style
enumeration would still output d_H records. No hidden factor is used.

## Exact unit-slope law in the no-alias range

Assume H^2<p<=q, p!=q. Two distinct primitive pairs cannot have the same
ratio modulo p: the nonzero integer b*a'-b'*a has absolute value less
than H^2<p. The same holds at q. Consequently each component slope
u modp or u modq hits at most one primitive tag, and the d_H tagged
slopes in that component are distinct units.

For u uniform on (Z/NZ)^*, the two component slopes are independent
uniform units. Let M=(p-1)(q-1). The event of any p-edge has probability
d_H/(p-1); similarly at q. The probability of both is d_H^2/M.
Both-component hits fail to separate precisely when their primitive
tags agree, whose probability is d_H/M. In that case every hit edge is
zero modulo N and all other edges are units. With distinct hit tags,
each tag supplies a proper edge. Thus the exact proper-edge probability is

    S_H = d_H/(p-1) + d_H/(q-1) - (d_H^2+d_H)/M.       (1)

This is conditional on a uniform unit slope, not an unconditioned public
sampling law. An implementation samples raw uniform residues, gcd-tests
each, and retains every initial proper/full outcome and retry cost. A
prescribed K accepted unit slopes may take more than K raw samples; the
original union-bound derivation of K*(1/p+1/q) counts RAW samples. The
same numerical probability upper bound also holds before K accepted units,
by a separate stopping argument: raw-factor probability is
1-[(p-1)(q-1)/(N-1)]^K <= K*(p+q-2)/(N-1) <= K*(1/p+1/q).
Work still counts actual draws: the virtual sampler needs expected
K*N/[(p-1)(q-1)] raw draws. Use a cap or price this work explicitly.
Accidental repeats in iid slopes already satisfy the law; deliberate reuse
or adaptive selected slopes need a different transcript.

Formula (1) improves the old union-bound accounting by distinguishing
shared full matches from genuinely separating pairs. It does not improve
the factor-search exponent: d_H=Theta(H^2), the explicit-list consumer
costs soft H per slope, and the dense shared polynomial has Theta(H^2)
coefficients. The same KH versus H^2+K work gates persist, with generation,
radix widths, data traffic, full-gcd localization and input reading paid.

## Concrete next compression question

The exact work removed is repeated rational factors, not repeated modular
chance events. A succinct representation could still evade a dense degree
cost, so degree alone is not a circuit lower bound. But this normalization
shows that rational duplicate elimination itself cannot do so. Replacing
the pair set by a multiplicative progression can give far fewer ratios;
the local event count then uses that smaller support, not H^2 independent
chances. A viable next product computation must preserve large DISTINCT
local support while actually sharing its evaluation. W007 already studied
nested split-polynomial circuits; that old unresolved supply problem must
not be renamed as a new algorithm here.
