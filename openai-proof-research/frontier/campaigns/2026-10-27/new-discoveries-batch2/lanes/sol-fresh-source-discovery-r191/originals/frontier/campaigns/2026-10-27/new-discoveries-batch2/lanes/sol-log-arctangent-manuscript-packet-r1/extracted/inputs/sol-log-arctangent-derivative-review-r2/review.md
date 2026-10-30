# Independent review of the finite 24th-derivative replacement

2026-10-29 UTC. **Ordinary replacement lemma PASS.** The certificate proves E(t)>0 for every t>0 for the literal candidate functions. It closes the proposed shorter route without any infinite-coefficient or asymptotic-tail premise. No mathematical defect found. No acceptance authority, Lean claim, discovery credit, or source/novelty clearance is asserted. Counts remain 3/30 additional and 33/60 total; candidate credit 0.

The supplied freeze identifiers are a92ad4bf2b (review freeze), 6825c748df (mathematical files), and 88eb1b426c (original candidate). These are supplied identifiers, not independently authenticated commit ancestry: no git command was run. All six SHA256 values in review-freeze.json matched before and after. All files in both input lanes were additionally hashed before and after and remained unchanged, including originals and existing cache files. Only this assigned review lane was written.

## Independent validation and exact claim

Let d=√17, α=(5+d)/2, β=(5-d)/2. Define

A=(cosh(4t)−cosh(t)cosh(dt)+(5/d)sinh(t)sinh(dt))/2,
B=sinh(t)(cosh(5t)−cosh(dt))/2,
U=B′A−BA′−A², V=−4BA, E=(1+2t²)U+tV.

The checked assertion is ∀t∈ℝ, t>0 ⇒ E(t)>0, including arbitrarily small and large t. It is a helper for one source family and receives zero independent discovery credit.

I wrote exact_review.py without reading, importing, or executing either root checker or the previous review checker. It uses standard-library Fraction arithmetic in Q[d]/(d²−17), with sparse polynomial-exponential maps indexed by (rational exponent coordinate, radical exponent coordinate, t-degree). It starts from

B=sinh(t)sinh(αt)sinh(βt),
A=cosh(t)sinh(αt)sinh(βt)
  −(sinh(t)/d)[αcosh(αt)sinh(βt)−βsinh(αt)cosh(βt)].

These formulas arise from B(coth(t)−f′(t)) for the actual source-centered comparison below. Exact multiplication checks they equal the displayed A,B. The checker constructs E independently as B′D−BD′−(1+2t²)A² with D=(1+2t²)A, before checking E=(1+2t²)U+tV. Only after reconstruction does it read the frozen U,V table to compare every coefficient and exponent. Both tables agree exactly. All generated A,B,U,V,E terms are in exact-results.json.

Differentiation uses the direct Leibniz formula

Dⁿ[tᵏ exp(λt)]=exp(λt) Σ_{j=0}^{min(k,n)} binom(n,j) k!/(k−j)! t^(k−j) λ^(n−j).

This is a polynomial identity, not a numerical diagnostic. An independent integer convolution from the A,B hyperbolic derivatives cross-checks E^(n)(0) through n=24. No candidate code is trusted as proof.

## Finite certificate and proof

The twelve strictly descending positive frequencies are

7+d, 2+2d, 10, 5+d, 2d, 8, 3+d, −2+2d, 7−d, 2, −3+d, 5−d.

The exact rational bounds (41/10)²<17<(21/5)² prove 41/10<d<21/5. The checker bounds every adjacent difference and the last frequency strictly below by a positive rational; thus this ordering has no floating-point dependency. There are no other nonzero frequencies. U is even and V odd, checked coefficientwise, and E is even. In particular u_{−λ}=u_λ and v_{−λ}=−v_λ. The constant U coefficient is −87/68, while V has zero constant coefficient. Its E contribution is −(87/68)(1+2t²), killed by 24 derivatives. This constant is not silently dropped before differentiation.

For each positive frequency λ with coefficients u,v define

c₀=λ²²(uλ²+24vλ+1104u),
c₁=λ²²(vλ+94u), c₂=2λ²²u.

Every prefix sum of each of these three ordered arrays is positive. All 36 exact pairs and their rational positive lower bounds are generated independently in exact-results.json and then compared against all frozen checks.json prefixes and verification.json lower bounds. For a+b d the lower bound is a+(41/10)b if b≥0, and a+(21/5)b if b<0. Every bound is strictly positive. The three final sums are respectively

355707128874106034847744,
46479400985961399582720,
1463704104369024663552.

For completeness, finite Abel summation is the algebraic identity

Σᵢ cᵢwᵢ = Sₘwₘ + Σ_{k<m} Sₖ(wₖ−wₖ₊₁),   Sₖ=Σ_{i≤k}cᵢ.

Positive prefixes and descending nonnegative weights imply a nonnegative sum; if wₘ>0 the sum is positive. Individual cᵢ need not be positive.

Direct differentiation of the complete reconstructed E, with every polynomial degree and every positive and negative frequency retained, gives exactly

E^(24)(t)/2 = Σᵢ [cᵢ₀ cosh(λᵢt)
 + t(cᵢ₁+cᵢ₂)λᵢ sinh(λᵢt)
 + t²cᵢ₂λᵢ² cosh(λᵢt)].

This is checked as an equality of sparse polynomial-exponential maps, not inferred from moment positivity. The factor 2 comes from pairing exp(λt) and exp(−λt). Explicitly the positive-frequency derivative coefficients at t⁰,t¹,t² are

λ²⁴u+24λ²³v+1104λ²²u,
λ²⁴v+96λ²³u,
2λ²⁴u.

Here 1104=2·24·23; the linear coefficient has 96=4·24, whereas the moment polynomial has 94=2(24+23). The c₂ addition is essential. An adversarial mutation replacing c₁+c₂ by c₁ is rejected by exact comparison. Oddness of V accounts for the sinh signs at the negative frequencies.

For t≥0 the functions of λ>0

cosh(λt), λsinh(λt), λ²cosh(λt)

are nonnegative and increasing. Their λ derivatives are t sinh(λt), sinh(λt)+λt cosh(λt), and 2λcosh(λt)+λ²t sinh(λt), respectively, all nonnegative. The first weight is strictly positive even at t=0. Apply Abel to c₀, c₁+c₂, and c₂. Prefix positivity for c₁+c₂ follows by addition of its two checked positive prefixes. Multiply the last two sums by t and t², both nonnegative. The first sum is strictly positive. Therefore E^(24)(t)>0 for all t≥0. This is the missing bridge that positivity of moments alone would not establish.

The independently checked derivatives E^(n)(0), n=0,…,23, are zero except

| n | E^(n)(0) |
|---|---:|
| 10 | 37847040 |
| 12 | 19891322880 |
| 14 | 5550283554816 |
| 16 | 1162696473968640 |
| 18 | 206947471161556992 |
| 20 | 33226670114812723200 |
| 22 | 4978839848478924865536 |

E is smooth as a finite sum of polynomial-exponential functions. For each j=23,…,0,

E^(j)(t)=E^(j)(0)+∫₀ᵗ E^(j+1)(s) ds.

Starting with E^(24)>0, continuity makes the integral strictly positive for every t>0, and the initial value is nonnegative. Descending induction proves E^(j)(t)>0 for t>0, including E itself. This supplies the full ordinary proof of the replacement lemma. The optional all-order moment identity is unnecessary; 1104+94h+2h²=2(24+h)(23+h) is nevertheless algebraically consistent with it.

## Connection to the literal primary statement

I independently read the cached primary arXiv:2405.13618v2 body: equation (1.5), the resultant definition and Definition 1.1, equation (1.7), Example 4.6, and Conjecture 4.7. Exact source fragments are retained in source-excerpts.json. The source defines

M(a,b)=(b−a)/(√2 arctan((log b−log a)/√2)),
R(Bp,M,Bq)(a,b)=Bp(M(a,Bq(a,b)),M(Bq(a,b),b)).

Conjecture 4.7 asks M−R<0 for p=5−2q, q=(5±√17)/2. Equation (1.7) explicitly interprets strict mean comparison off the diagonal. Hence the literal displayed target is, for both (p,q)=(d,β),(−d,α), every distinct a,b>0:

M(a,b)<Bp(M(a,Bq(a,b)),M(Bq(a,b),b)).

Here Br(x,y)=((xʳ+yʳ)/2)^(1/r); the relevant exponents are nonzero. Diagonal values are continuous extensions, with equality. This review confirms the connection for the cached arXiv version only, and makes no journal-source clearance.

Here is the analytic assembly, rechecked independently rather than inferred from the previous review verdict. Put S(a,b)=[(β/α)(b^α−a^α)/(b^β−a^β)]^(1/d), and

f(t)=log S(e^(−t),e^t)=(1/d)log[βsinh(αt)/(αsinh(βt))],
g(t)=log M(e^(−t),e^t)=log[√2 sinh(t)/arctan(√2t)].

The independently constructed A,B satisfy B>0 and A/B=coth(t)−f′(t). Also A>0 for t>0: for even n≥2,

2A^(n)(0)=4ⁿ+((5/d−1)/2)(d+1)ⁿ−((5/d+1)/2)(d−1)ⁿ>0.

Indeed 4<d<17/4, (5/d+1)/2<9/8, d−1<13/4, and (16/13)²>9/8. The first term dominates the negative term for every even n≥2; the middle term is positive. A is entire and even with A(0)=0, so its Taylor expansion proves the assertion. A=2t²+O(t⁴), B=2t³+O(t⁵).

Set T=1+2t² and J=√2 B/(TA). Exact quotient differentiation yields

J′−√2/T=√2 E/(T²A²)>0.

J has zero limit at 0. Integrating the strictly positive derivative of J−arctan(√2t), using that zero limit, yields J>arctan(√2t). Since A,B,T and arctan(√2t) are positive, this is equivalent to

(f−g)′=√2/[T arctan(√2t)]−A/B>0.

For a<b let c=Bq(a,b), t=log(b/a)/2, x=log(c/a)/2 and y=log(b/c)/2. Because q>0, a<c<b, x,y>0 and x+y=t. Homogeneity and strict increase of k=f−g give M(a,c)>exp(−k(t))S(a,c), and similarly M(c,b)>exp(−k(t))S(c,b).

For r=p+q, {q,r}={α,β}, the exact identity S(a,b)^p=(q/r)(bʳ−aʳ)/(b^q−a^q) proves Bp(S(a,c),S(c,b))=S(a,b), since the two q-power denominator increments equal half the full increment. This works also for p<0 by injectivity of positive real powers. Bp is homogeneous and strictly increasing in both arguments: its partial derivative is (1/2)u^(p−1)Bp(u,v)^(1−p)>0 for either sign of p. Applying it to the two strict comparisons gives R(Bp,M,Bq)>exp(−k(t))S(a,b)=M(a,b). Symmetry handles b<a. Thus the finite derivative replacement really supplies the E-positivity step of the literal two-branch displayed source proof.

The separate Definition 1.1 requirement that M lie between the outer and inner means is not established here. The stronger terminology “super-stabilizable” must retain that qualification.

## Objections, boundaries, and formalization interface

The strongest local falsifier was a mismatch between the moment polynomial and the actual derivative: positive prefixes of c₀+h c₁+h²c₂ alone are not the displayed derivative identity. This review closes it by full independent differentiation, detecting the incorrect 94-only linear coefficient. Other concrete falsifiers would be an unlisted frequency, a nonpositive prefix, an incorrect parity sign, an unsuppressed constant, or a negative initial derivative. Exact reconstruction rules each out for these frozen bytes. Any future edits require checking again.

The strongest remaining external objection is substantive: an existing full ratio-monotonicity or specialized stabilizable-mean theorem could subsume the result routinely. The Stolarsky identity, Abel summation and derivative ladder are classical helpers and carry no separate credit. This focused review makes no fresh prior-art clearance, current-registry claim or published-journal equality claim, and does not duplicate the separate source-access lane. Previous substantive/novelty/journal HOLDs persist. Formal, paper, packet and extracted replay gates also remain open.

Only after the ordinary PASS above, the minimal standalone formalization obligations are:

1. Define the literal real A,B,U,V,E; prove their smoothness and the two source-centered product identities. Establish d²=17 and its rational interval, not an abstract unexplained coefficient field premise.
2. Prove the explicit 12-frequency U,V expansion (including u₀=−87/68 and v₀=0), parity, and exact descending order. Encode exact coefficients as rational pairs interpreted in ℝ.
3. Prove a generic finite Abel identity and its nonnegative/strict weighted variants. Prove the 36 explicit prefix inequalities by rational interval bounds on √17.
4. Prove the literal iteratedDeriv 24 E identity with c₁+c₂ and the seven nonzero jets; prove all other jets below 24 vanish. The identity must be connected to derivatives of the defined E, not merely an asserted moment sequence.
5. Prove monotonicity/nonnegativity of the three real weight functions and derive iteratedDeriv 24 E>0 on [0,∞). A generic smooth descending-derivative lemma with nonnegative jets then gives ∀t>0, E(t)>0.

That standalone endpoint is only E positivity. A full source endpoint additionally needs actual A,B positivity and zero limits, quotient and arctangent differentiation, monotone logarithmic ratio, the literal S stabilizing identity for both signs, positive-power and Bp monotonicity, and the homogeneous transfer for every distinct positive pair. No placeholder SourceClaim, opaque unproved bridge or unrelated coefficient proposition may substitute for these obligations. No Lean implementation was undertaken.

## Reproduction and limits

Run from any directory:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 timeout 45s python3 /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-log-arctangent-derivative-review-r2/exact_review.py
```

The checker enforces hard 512 MiB address space, hard 35 CPU seconds, and thread limits of one; limits were never raised. Completed bounded runs passed in under one second. No diagnostic/resource failure occurred. run.log preserves the final output; the deliberately rejected 94 mutation is an expected negative control, not a failed proof run. No numerical evidence, external requests, browser tabs, account actions, messages, uploads, children, git commands, candidate edits or count changes occurred. provenance.json records dated source reuse, hashes and explicit clearance limits.
