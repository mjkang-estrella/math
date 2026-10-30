# Proposed counterexample to the lower-dimension / Lp conjecture

EXCLUDED: the source question was already answered negatively by Hare--Hare2020, Proposition2.31. Credit0; no Lean work will be done for this known resolution. The independent parent construction below is retained as an uncredited derivation. See EXCLUSION.md.

## Exact source and scope

Fraser--Troscheit, Regularity versus smoothness of measures,
arXiv:1912.07292v1, Section 4, Question 4.3 and Conjecture 4.4 (pp.13-14).
The accepted2021 manuscript was fetched and p13 personally rendered/read; its footnote1 explicitly cites the prior negative resolution. Conjecture 4.4 says that an absolutely
continuous probability measure on [0,1] with lower dimension >1-1/p has a
density in every L^q, 1<=q<p. Question 4.3 asks whether positive lower dimension
forces any L^q with q>1. We propose ONE measure refuting both: lower dimension
at least log(2)/log(3)>1/2, but density outside every L^q, q>1.

Related MathDB344923 is the DIFFERENT Conjecture4.6, with the additional C>=1
condition. It is not the target. In the literal radii normalization r<R<1,
that additional condition is vacuous for absolutely continuous probabilities
supported on [0,1]: take an interior support point x and
max{x,1-x}<r<R<1, so both balls already have mass1 but (R/r)^(1-1/p)>1.
This observation is a normalization artifact and receives NO discovery credit.
Do not present it as the substantive counterexample below.

## Explicit finite-stage densities

Let a=log(2)/log(3), so 1/2<a<1 and 3^a=2. Let K_m be the union of the 2^m
closed level-m middle-thirds Cantor intervals in [0,1], each of length
delta_m=3^(-m). Endpoints have no relevance to the following Lebesgue densities.
Let

    h_m(x)=(3/2)^m 1_{K_m}(x),      nu_m=h_m dx.

Thus nu_m is an absolutely continuous probability measure, with equal mass
2^(-m) on each level-m interval. These objects are completely finite: no
infinite Cantor probability measure is needed to define them.

We first prove a reverse-growth bound UNIFORM in m. Define, for t>0,

    G_m(t) = (3/2)^m t     if 0<t<=delta_m,
             t^a          if delta_m<=t<=1.

The branches agree at delta_m, with value 2^(-m). For z in K_m and 0<t<=1,

    (1/2)G_m(t) <= nu_m(B(z,t)) <= 4 G_m(t).             (A)

For t<=delta_m, the level-m interval containing z contributes at least length
t inside the ball, and the full ball has length2t. The density is either
0 or (3/2)^m, proving even the stronger bounds G_m(t),2G_m(t).

For delta_m<=t<=1, choose 0<=j<=m with
3^(-j)<=t<3*3^(-j). The level-j interval containing z lies within B(z,t)
up to measure-zero endpoints; it has nu_m mass2^(-j). Since
2^(-j)=(3^(-j))^a>=(t/3)^a=t^a/2, this proves the lower bound.
Distinct level-j intervals have length l=3^(-j) and gaps at least l. An
interval of length2t<6l can meet at most four of them in positive length.
Each has mass2^(-j)<=t^a, proving the upper bound. For t=1 use j=0.

Two consequences of the definition of G_m will be used:

    G_m(v)/G_m(u) >= (v/u)^a      for 0<u<=v<=1;         (B)
    G_m(cu) <= c G_m(u)           for c>=1, cu<=1.       (C)

Indeed G_m(t)/t^a is increasing (equal to (t/delta_m)^(1-a) below delta_m,
and 1 above), proving (B). G_m(t)/t is decreasing, proving (C).
Equivalently G_m(cu)>=c G_m(u) for 0<c<=1.

For ANY center x in R and 0<r<R<=1 we claim

    nu_m(B(x,R)) >= (1/32)(R/r)^a nu_m(B(x,r)).          (D)

If the small ball has zero mass this is immediate. Otherwise choose
z in K_m intersect B(x,r). If R>=4r, then

    B(z,3R/4) subset B(x,R),    B(x,r) subset B(z,2r).

Using (A), (C), and (B), respectively, gives a ratio at least

    [(1/2)G_m(3R/4)]/[4G_m(2r)]
      >= (3/64) G_m(R)/G_m(r)
      >= (3/64)(R/r)^a >= (1/32)(R/r)^a.

Here 2r<=R/2<=1, so every use of (A)--(C) is in its domain. If R<4r,
monotonicity of ball masses gives ratio>=1, whereas
(1/32)(R/r)^a<4/32<1. This proves (D), including centers in gaps or outside
[0,1], not just centers in K_m. This center extension is load-bearing for
summing measures with different supports.

## The single counterexample

For k=1,2,... set m_k=k^2+3 and w_k=2^(-(k+1)), and define

    f(x) = (1/2)1_[0,1](x) + sum_{k>=1} w_k h_{m_k}(x),
    nu = f dx.

Tonelli gives integral f=1/2+sum w_k=1. Thus f is finite almost everywhere
and nu is an absolutely continuous probability supported on [0,1]. Its
support is exactly [0,1] because of the baseline. Any infinite point values
of the displayed series can be redefined on its null infinity set.

For x in [0,1] and 0<r<R<1, Lebesgue measure restricted to [0,1] satisfies

    lambda(B(x,R) intersect[0,1]) >= R,
    lambda(B(x,r) intersect[0,1]) <= 2r.

Consequently its ball ratio is >=(R/r)/2>=(R/r)^a/2.
Every nu_{m_k} satisfies (D) for this SAME x,r,R and the SAME constant1/32.
Multiply those inequalities by their positive mixture weights, add, and
use monotone convergence for the countable sum. This gives

    nu(B(x,R)) >= (1/32)(R/r)^a nu(B(x,r))              (E)

for all x in supp nu=[0,1] and 0<r<R<1. Therefore dim_L nu>=a>1/2.
No uniform upper-growth/doubling claim is needed or made.

Nevertheless f is in no L^q for q>1. Indeed K_{m_k} has Lebesgue measure
(2/3)^(k^2+3), and nu(K_{m_k})>=w_k. If f belonged to L^q[0,1], Holder gives

    2^(-(k+1)) <= ||f||_q (2/3)^((k^2+3)(1-1/q))       (F)

for every k. The ratio of the left side to the final exponential is
unbounded: its logarithm is

    (k^2+3)(1-1/q)log(3/2) - (k+1)log2 -> +infinity,

since q>1. This contradicts (F). In particular f is not in L^(4/3), while
dim_L nu>1/2>1/3=1-1/(3/2). Taking p=3/2 and q=4/3 explicitly contradicts
the source's Conjecture4.4, without relying on a borderline exponent.

## Orthogonal route / validation opportunity

An alternative construction starts with the Ahlfors-a Cantor probability,
whose all-center reverse-growth bound follows by the same support-point
extension. Convolution with arbitrarily narrow absolutely continuous
probabilities preserves that all-center bound by integrating it pointwise
in the translated center. A sufficiently rapidly concentrating positive
mixture again fails all L^q. The finite-stage construction above avoids
formalizing the singular measure or convolution, and is the primary claim.

The mathematical proof does not rely on numerical evidence. An independent
review should in particular check the four-interval bound, the direction of
both G_m scaling inequalities, all-center extension, the uniform constant,
countable-mixture passage, and the Lq obstruction. Formalization would need
the literal ball-ratio definition of source lower dimension and the exact
finite interval densities, not a conditional abstract mixing lemma.

## Novelty and current limitations

No novelty PASS is claimed. Uniformly perfect measures/weights and their
relation to reverse Holder bounds, A-infinity, and mixtures of regular
approximants are obvious possible predecessors. A known absolutely
continuous uniformly perfect measure outside every L^q would subsume the
source-question refutation and make this uncountable. The broad source
conjecture is not entitled to novelty merely because its label stays open.
Search later source versions, its published body, citing papers, author
follow-ups, and classical counterexample constructions before Lean work.
The C>=1 vacuity observation, finite-stage lemmas, and separate q values
must never be counted as additional outcomes.
