# Ordinary full refutation candidate — eligibility on HOLD

This is an ordinary mathematical proof, not a Lean certificate, manuscript, independent review, acceptance or priority claim. The exact source is Hoang–Levit–Mandrescu–Pham, *Unimodality of the independence polynomial of clique corona graphs*, DOI 10.26493/1855-3974.3383.3c7, journal-hosted accepted manuscript published 5 August 2026, Conjecture 6.1, printed p.20. It asserts unimodality of I(G ◦ K_p;x) for every graph G and every integer p≥1. The paper's global convention is finite simple graphs without isolated vertices (p.2). The witness below is connected and has no isolated vertices.

## The graph and its literal polynomial

Put r=100000, s=225985, n=3r+s=525985. Let G be the join of the disjoint union of r triangles with the edgeless graph on s vertices. Explicitly label triangle vertices (i,a), 1≤i≤r, 1≤a≤3, and other vertices b_j, 1≤j≤s. Edges are all pairs in each triangle and all pairs ((i,a),b_j), and no others. Let H=G ◦ K_1: append exactly one private leaf to every vertex of G. H is finite simple, connected, has 1051970 vertices, and lies literally in the source family with p=1.

An independent set of G is entirely on one side of the join. Thus

    I(G;t)=(1+3t)^r+(1+t)^s−1.

For each independent base set S in a leaf corona, its chosen base vertices exclude their private leaves; every other leaf is independently optional. Consequently, directly by counting (also source Lemma 1.3(ii) and Corollary 3.6),

    Q(x):=I(H;x)=(1+x)^n I(G;x/(1+x))=A(x)+B(x)−C(x),
    A(x)=(1+x)^(2r+s)(1+4x)^r,
    B(x)=(1+x)^(3r)(1+2x)^s,
    C(x)=(1+x)^n.

All coefficients q_k of Q are nonnegative independent-set counts. Write a=A(1), b=B(1), c=C(1). Then

    a=2^(2r+s)5^r, b=2^(3r)3^s, c=2^(3r+s).

We will use only 1<a/b<2, c<a/100, and c<b/100.

## Exact scalar bounds, without a floating-point premise

For 0<t<1, integrating the geometric series gives

    S_20(t)=2 sum_{j=0}^{19} t^(2j+1)/(2j+1),
    S_20(t)<log((1+t)/(1−t))<S_20(t)+2t^41/[41(1−t²)].

The tail inequality follows termwise from 1/(2j+1)≤1/41 for j≥20. Rational substitution t=3/7 and t=1/5 yields

    9162907318741/10^13 < log(5/2) < 9162907318742/10^13,
    4054651081081/10^13 < log(3/2) < 4054651081082/10^13.

These four rational comparisons follow by bringing the displayed 20-term sums and tail bounds to common denominators; checks.py reproduces them with exact fractions. Multiplying the first bounds by 100000 and the second by 225985 shows

    0 < r log(5/2)−s log(3/2) < 1/10.

Therefore 1<a/b<exp(1/10)<2. For the latter inequality use exp(u)=sum u^j/j!≤sum u^j=1/(1−u), at u=1/10. Independently, checks.py verifies the equivalent integer comparison 3^s<5^r 2^(s−r)<2·3^s.

Also c/a=(2/5)^r≤(2/5)^6<1/100 and c/b=(2/3)^s≤(2/3)^12<1/100, by elementary rational powers.

## Three windows and concentration

Normalized coefficients of (1+wx)^m are the law of a binomial variable with m trials and success probability w/(1+w). Products correspond to independent sums, since their probability generating functions multiply. Hence the normalized coefficients of A and B are distributions with means and variances

    μ_A=(2r+s)/2+4r/5=585985/2,
    σ_A²=(2r+s)/4+4r/25=489985/4 <126000,
    μ_B=3r/2+2s/3=901970/3,
    σ_B²=3r/4+2s/9=1126970/9 <126000.

Take the following integer intervals, each of cardinality 2001:

    L=[291993,293993], V=[295825,297825], R=[299657,301657].

They occur in the indicated strict order. The centers of L and R differ from μ_A and μ_B, respectively, by less than one. Every integer outside L is at distance greater than 1000 from μ_A, and every integer outside R is at distance greater than 1000 from μ_B. Thus Chebyshev's inequality gives

    sum_{k∈L} A_k ≥(1−126000/1000²)a =0.874a,
    sum_{k∈R} B_k ≥0.874b.

Here and below the finite decimal constants denote exact rationals. For completeness, Chebyshev follows because the indicator of |X−μ|≥d is at most (X−μ)²/d²; take expectations.

Using nonnegativity of the other positive polynomial and subtracting at most the entire overlap c, we get

    sum_{k∈L} q_k ≥0.874a−c >0.86a,
    sum_{k∈R} q_k ≥0.874b−c >0.86b.

Every integer in V is at distance greater than 2800 from BOTH means: its lower endpoint minus μ_A is 2832.5, and μ_B minus its upper endpoint is 2831+2/3. Therefore

    sum_{k∈V} q_k ≤ sum_{k∈V}(A_k+B_k)
                      ≤126000/2800² ·(a+b)
                      <0.017(a+b)<0.051 min(a,b).

The last step uses 1<a/b<2, so a+b<3b=3 min(a,b).

## A strict valley contradicts unimodality

Some index ℓ∈L has q_ℓ>0.86a/2001, and some index h∈R has q_h>0.86b/2001, by averaging. If (q_k) were unimodal, then every coefficient between ℓ and h would be at least min(q_ℓ,q_h): before the mode use nondecrease, after the mode use nonincrease. In particular,

    sum_{k∈V} q_k ≥2001 min(q_ℓ,q_h)>0.86 min(a,b).

This contradicts the strict upper bound 0.051 min(a,b). Thus Q is not unimodal. The graph H is a genuine in-scope source counterexample, not a counterexample merely to a proof route or auxiliary strengthening. A single p=1 witness refutes the entire universal Conjecture 6.1. No assertion is made about all p, minimal order, exact modes, or the distinct tree conjecture.

## Strongest objections and falsifiers

Mathematical falsifiers are: a discrepancy in the join/corona counting identity; an erroneous total-mass balance; an incorrect Bernoulli variance; or violation of any interval-distance bound. All are explicit above and have exact arithmetic controls. The proof does not infer nonunimodality from non-log-concavity or from plots. The 525985-degree polynomial is never expanded.

The strongest substantive objection is that separated-phase joins could be a routine application of a known nonunimodality construction. Old join constructions and Chebyshev are classical; no novelty is claimed for either tool. The closest read old construction (Levit–Mandrescu math/0309151, Section 3/Theorem 3.2) produces well-covered graphs but explicitly says its graphs are NOT very well-covered. It supplies no transfer of nonunimodality through a single leaf corona. Here the overlap subtraction, entropy balance, and post-corona separated means are necessary. No complete classical subsumption bridge was found in the bounded bodies read; this is not worldwide clearance. The 2016 corona full body and 2017 clique-corona survey remain access/coverage gaps. Independent root substantive and novelty adjudication is required before any Lean/manuscript investment.
