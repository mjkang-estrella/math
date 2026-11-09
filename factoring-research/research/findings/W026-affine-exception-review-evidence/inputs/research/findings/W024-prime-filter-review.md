**W024 independent review: public prime/sign filtering**

2026-10-08 local / 2026-10-09 UTC. **Accept the sign filter as a replacement for W022's magnitude guard, with the explicit uniformity and boundary completions below. Verified new complete factoring improvement: NONE.** Every retained leaf has a nonzero integer exponent. For at least one publicly scheduled base, a covered witness survives in its actual root sign, including the case p≡−1 modulo that base. The filtered domains remain ordinary boxes and support the accepted W020 localization contract. No counterexample to this correctly scoped claim was found. No fast evaluator or improved complete factoring bound follows.

The audited W024 snapshot has SHA-256 `6f012b2ef84607349db60e412baf646458db18e892c4ccb897ad0ded5609f258`. The [full verbatim brief](W024-prime-filter-review-evidence/brief.txt) and [freeze manifest](W024-prime-filter-review-evidence/freeze-manifest.json) preserve eleven inputs and their hashes. The review imports W022 A/A2/A3, the signed-endpoint correction in its parent disposition, and W020's accepted extractor; it does not re-audit their historical certificates. STATE was consulted only at frozen lines 1–160 for operating context. W022 §B and the binomial portion of the parent disposition were read as adjacent text but supply no premise here. No experiment, solver run, Lean edit/build, install, commit, or delegation occurred. The parent continues computation independently.

**The constant residue and both signs.** Fix a legal odd prime ℓ with gcd(N,ℓ)=1 and a nonempty primitive stratum with h≥1. Write Q=ℓ^(2h), H=ℓ^ceil(2h/5), u=u₀+Hx, v=v₀+Hy, with unit canonical residues u₀,v₀. The accepted quartic has integer coefficient representatives and R(x,y)≡r₀ (mod ℓ), with r₀²≡4Nu₀v₀ (mod Q). Consequently, on the entire integer chart, not only its covered points,

```
E(x,y,τ) = u+Nv−σR(x,y)−Qτ
         ≡ u₀+Nv₀−σr₀ = εσ  (mod ℓ).
```

Retain a chart/sign exactly when εσ≠0. Then E is a nonzero integer for every retained leaf, for arbitrary signed τ and regardless of |R| or |E|. This does not say E is coprime to N, which is neither required nor desirable. It also does not preserve W022's old assertion sign(E)=sign(v); recovery only needs the actual signed nonzero E.

Both ε values cannot vanish: their difference is 2r₀, a unit modulo the odd prime. More precisely,

```
ε₊ ε₋ ≡ (u₀+Nv₀)²−r₀² ≡ (u₀−Nv₀)² (mod ℓ).
```

Thus both signs survive off u₀=Nv₀ modulo ℓ; exactly one survives on that line. The test has a constant number of modular operations per sign, not constant bit cost. Reduction and arithmetic must use the actual operand widths.

**Coverage after every common-weight valuation.** Let N=pq, with p prime and q an integer, and let a covered original pair have common weight valuation s. The accepted W022 decomposition divides both integer weights by r=ℓ^s and gives

```
m_s=M/r=ℓ^h,   h=k−s≥1,
1≤u≤U_s=floor(U/r),  1≤|v|≤V_s=floor(V/r),
ℓ∤uv,  m_s | up−vq,
S=up+vq=σR(x,y)+Qτ,  |S|≤W_s=ceil(W/r).
```

Here u and v already mean the divided, primitive weights. Direct integer algebra gives the two identities requested in the brief:

```
u+Nv−S = u+pqv−up−vq
        = (p−1)(vq−u)
        = u(p−1)²−(p−1)(up−vq).
```

Since h≥1, the final term is divisible by ℓ, and therefore

```
E ≡ u(p−1)² (mod ℓ).
```

The primitive u is a unit. The true leaf is retained **if and only if p≠1 (mod ℓ)**. This is valid in every nonempty stratum, including the last h=1 stratum, and for negative v. Applying the test to the original unstripped weights would not justify this conclusion: their residue can be zero. The algorithm must construct and filter the primitive chart in each stratum as specified.

There is a useful exact comparison with whole-chart exclusion. At a covered point, Nv≡up² and S≡2up modulo ℓ. The actual and opposite sign residues are respectively u(p−1)² and u(p+1)². When p≡−1, the actual sign has residue 4u≠0 and the opposite sign has residue zero. A rule deleting every chart with u₀=Nv₀ would delete this witness. When p≡1 the situation is reversed: the actual leaf is deleted even though the chart's opposite sign survives. Thus “at least one sign survives” alone is not a coverage proof; the scheduled good base is essential. These are symbolic counterexamples to stronger interpretations, not failures of W024.

**A fully public, bounded prime schedule.** Put n=bitlen(N). On the unresolved composite-input path, sieve odd primes in increasing order, multiply them until their product P first exceeds N, and gcd each prime with N. Since ℓ is prime and N composite, gcd(N,ℓ)>1 is a proper factor. If no such factor is found, every listed prime is legal; none has been deleted from the product. It would be incorrect to drop primes dividing N and then reuse the original product argument, but the proposed algorithm returns their factor immediately instead.

There are at most n scheduled odd primes, because 3^n>2^n>N. This is slightly stronger than the brief's bound. Size is a separate issue. The following elementary argument gives the explicit sieve ceiling

```
X = 16(n+1)².
```

For an integer a≥1, every factor in binomial(2a,a)=∏_{j=1}^a(a+j)/j is at least 2, so this binomial is at least 2^a. For every prime t, its valuation in that binomial is

```
Σ_{j≥1} (floor(2a/t^j)−2 floor(a/t^j)).
```

Each summand is 0 or 1, and only j≤floor(log_t(2a)) can contribute. Hence the contribution t^valuation is at most 2a, and

```
2^a ≤ binomial(2a,a) ≤ (2a)^π(2a),
π(x) ≥ x/(2 log₂ x)                 for every even integer x≥2.
```

Set b=n+1. The elementary inequality log₂ b≤b−1 gives log₂ X=4+2log₂ b≤4b. Therefore π(X)≥2b. Even after excluding 2, there are at least n odd primes below X. This proves a polynomial bound on the **numerical sizes** of all scheduled primes without iterating Bertrand's postulate or assuming an asymptotic threshold. The large binomial is only a proof device; the algorithm never computes it.

For completeness, a sequential implementation can sieve a tape of X flags, scanning it for every integer d≤sqrt(X) and crossing multiples of d starting at d². Composite d values may be processed redundantly. This is still a correct sieve, and uses O(X^(3/2) log(X+1)) elementary bit work with counters and O(X+log X) working bits, up to a fixed multitape implementation overhead. A looser O(X² log²(X+1)) bound suffices if bookkeeping is implemented less carefully. Both are polynomial in n. Ordinary array sieving is faster but is unnecessary for this uniformity proof. The at-most-n product updates, comparisons and gcds act on O(n+log n)-bit integers: before the last multiplication P≤N, and afterwards P≤NX. Schoolbook arithmetic and Euclid give, conservatively, another O(n^4) bit operations.

On the no-factor path, fix any prime divisor p of N. If every scheduled ℓ divided p−1, their pairwise coprime product P would divide p−1. But P>N>p−1. Thus some scheduled legal ℓ has p≠1 modulo ℓ. The algorithm processes all bases and does not know which is good. It must retain a covering range schedule at each base; it cannot discard large scheduled primes just because a desired chart parameter is smaller than ℓ.

This bound is intentionally elementary and loose. As narrow primary context, Rosser and Schoenfeld give x/log x<π(x) for x≥17, equation (3.5), printed p. 69, which also suffices for a constructive polynomial sieve ceiling. Only that stated estimate is imported as context; their proof and full paper were not audited, and this review's bound does not depend on it. [Rosser–Schoenfeld, *Approximate formulas for some functions of prime numbers*](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf). The [retrieval record](W024-prime-filter-review-evidence/source-retrieval.json) records the bounded read scope and source hash. No novelty claim follows from this source check.

**Rounding, small targets and admissible ranges.** Use exact integer comparisons, not floating logarithms, to choose the least positive power M=ℓ^k with M≥T for a public target T≥1. Repeated multiplication suffices. Then

```
k≥1,  T≤M≤ℓT,
```

with the upper inequality strict except possibly at T=1. For an integer target, O(1+log(T+1)) multiplications suffice. Rational targets can be compared by cross multiplication; a target such as a fixed rational power of N can be specified by exact integer power comparisons. Its own computation is paid.

If T<ℓ, take k=1 and M=ℓ. This case can occur for arbitrarily large N and is not automatically a finite-small-input exception. Rebuild the public range data for this M. The imported cover requires

```
2≤U≤M−1,  V=ceil(M/U)<M.
```

These inequalities hold for every such U when M≥3. One universally admissible choice is U=2; thus no prime needs to be discarded because M is small. If a proposed rounded U is outside this interval, an explicit coverage completion is to clamp it into [2,M−1], recompute V, and use the public bound W=N(U+V) unless a tighter bound has been proved for the changed range. Indeed |up+vq|≤Up+Vq≤N(U+V). This is a correctness fallback with its actual cost, not a preservation theorem for the desired optimized W or the unbalanced factor-range schedule. That optimized schedule and its small-factor screen remain inherited, paid obligations.

For k=1 all legal U,V are less than ℓ, so only s=0 occurs and H=ℓ. Positive-u charts are singletons; a combined signed-v residue chart can have one or two values (y=−1 and/or 0), with Z=1. Chart/pair acquisition is polynomial in ℓ, but the carry width still contains W/ℓ². A small target therefore does not make the whole product polynomial in n. In particular, expanding carries under the fallback W can be expensive.

Even inputs and exact prime powers retain W020's polynomial-bit preprocessing. For an entirely explicit finite-input convention, composites N≤16 can be split by trial divisors through 4 before any charts are made. No size-bound or chart argument here relies on an unspecified “sufficiently large N”; primality/termination on prime inputs is outside the composite-input contract.

**Uniform chart acquisition, including growing ℓ.** For every admitted rectangle, enumerate exactly

```
0≤s≤floor(log_ℓ(min(U,V)))≤k−1,
r=ℓ^s, m_s=M/r, h=k−s, Q_s=m_s²,
H_s=ℓ^ceil(2h/5),
m_s^(2/5)≤H_s<ℓ m_s^(2/5),  H_s≤m_s.
```

The index bounds can be found by integer multiplication. A stratum with U_s or V_s zero is absent. Unit residue representatives are 1,…,H_s−1 excluding multiples of ℓ; the exact endpoints are

```
xlo=ceil((1−u₀)/H_s),   xhi=floor((U_s−u₀)/H_s),
ylo=ceil((−V_s−v₀)/H_s), yhi=floor((V_s−v₀)/H_s).
```

Use mathematical floor and ceiling for negative integers. Reject empty intervals. Because v₀ is a unit, v=0 does not occur inside a retained y interval, so no puncture is introduced. H_s>V_s alone does not imply a singleton combined signed-v chart; H_s>2V_s suffices. Both signs of the root are constructed or tested separately after the chart is found to be rooted.

Let C_s count nonempty residue charts before the root/sign filter. Uniformly,

```
C_s≤min(H_s,U_s) min(H_s,2V_s),
Σ_s C_s=O(ℓ² M^(4/5)),
Σ_s H_s=O(ℓ M^(2/5)).
```

The constants can be chosen independent of ℓ≥3, since the corresponding geometric sums are bounded by their values at ℓ=3. The second sum charges even a simple full residue scan in each stratum. There is no assumption that scanning chart representatives is free, nor a need to scan all original coordinate values.

For each candidate chart, brute-force b=0,…,ℓ−1 to test b²≡D modulo ℓ, where D=4Nu₀v₀. This costs at most ℓ trials. A nonsquare chart has no roots and is legitimately absent. A rooted chart has two unit roots; choose one and obtain the other by negation. Lift the chosen root by the public digit formula

```
a_(j+1)=a_j+ℓ^j d_j,
d_j=((D−a_j²)/ℓ^j) (2a_j)^(−1) mod ℓ,
1≤j<2h.
```

Division is exact, and the inverse exists. Its value modulo ℓ can be computed once because a_j has a constant residue modulo ℓ. There are O(h) lift steps, not O(1). Extended Euclid modulo Q supplies the unit inverses of u₀,v₀ and powers of 2 needed for the 15 coefficients. Use the reduced binomial coefficients (1,1/2,−1/8,1/16,−5/128); inverting an unreduced i! would be invalid for ℓ=3. Integer coefficient representatives retain their stated sizes. The fixed-degree construction has no factorization or square-root oracle modulo N.

Put B=n+ceil(log₂(M+1))+ceil(log₂(W+1))+3. All these operands have O(B) bits. A conservative per-chart bit bound using schoolbook arithmetic is

```
O(ℓ B²+B³),
```

including the root trials, O(h) lift steps, a constant number of Euclidean inverses, the fixed coefficient array, endpoints, envelope, and both residue tests. A safe total acquisition bound per base/range is

```
O((k+Σ_s H_s) B³ + Σ_s C_s (ℓ B²+B³)).
```

For example O((1+ℓ³ M^(4/5)) B³) is a coarser sufficient bound. It is not claimed optimal. Since ℓ≤16(n+1)², k=O(log M), and M≤ℓT, this is only a polynomial-in-n overhead on the displayed fixed-degree chart exponent model when T,W=N^O(1). Sum it over every scheduled prime and every public factor range. Stored chart records and residue lists use at most O((k+Σ_s H_s+Σ_s C_s)B) bits per base/range in a direct implementation; caching across bases/ranges sums these quantities. Alpha-independent acquisition may be reused across trials, with storage and its one-time cost charged. An eventual evaluator whose hidden constants depend exponentially on ℓ would **not** inherit this conclusion; its own uniformity still needs proof.

**The unchanged carry cost and widths.** For a nonempty chart use the accepted enclosure

```
Z=max(1,|xlo|,|xhi|,|ylo|,|yhi|),
Rmax=15Q_s Z^4,  K=ceil((W_s+Rmax)/Q_s),
−K≤τ≤K.
```

Keep this same interval for each retained sign. The residue test is independent of x,y,τ. There is no reason to shorten the interval or select a carry per point, and doing so would require a separate coverage argument. Every represented exponent obeys

```
|E|≤U_s+NV_s+W_s+2Rmax+Q_s.
```

Thus E, its sign and its binary encoding have O(B) bits. This remains O(n) for polynomially bounded M,W, even when Rmax>N. Exponents are integers, not residues modulo Q_s or an unknown group order. Negative powers use a checked inverse of the original unit alpha and binary powering. Paying for O(n) exponent bits does not pay for the number of carries.

There is an explicit uniform occurrence bound. Write A=max(U,V). Since M≤UV<2M,

```
P_s≤2UV/r²=O(M/r²),
Z_s≤1+A/(M^(2/5) r^(3/5)),
2K_s+1=O(1+Wr/M²+A^4/(M^(8/5)r^(12/5))).
```

Here P_s counts primitive signed pairs, and a uniform stratum envelope is used for the chart-dependent K_s. Summing the pair counts times the carry lengths, with two root signs allowed, gives

```
L≤O(M+W/M+A^4/M^(3/5)),
```

with constants uniform over ℓ≥3. Balanced A=O(sqrt M) gives the accepted O(M+W/M+M^(7/5)); thin A=Θ(M) gives the conservative extra term O(M^(17/5)). For fixed small ℓ the original thin-family enclosure still has Rmax=Θ(M^(22/5)). With growing ℓ the exact rounding is retained in H_s and can alter this by polynomial-logarithmic factors, not erase the obstruction.

In fact, for each rooted chart the two unfiltered sign boxes have equal cardinality, and at least one is retained. Hence the retained occurrence count is between one half and all of the original rooted occurrence count, base by base, before any new bases are added. The filter cannot by itself deliver an asymptotic reduction in these carry occurrences. It removes a correctness guard; it does not supply a shorter product.

**Restriction, localization and the original uniform alpha.** A retained record still contains its stratum, canonical residues, sign, polynomial coefficients and three ordinary integer intervals. Subdividing any interval leaves εσ unchanged. Both children have the same nonzero-exponent guarantee, products multiply exactly, and an empty child has product 1. Do not add padding in x or y outside the proved covering domain merely from this observation; the promised interface is restriction of the existing boxes. Repeated occurrences across strata/bases remain labeled occurrences.

Halve the finite retained chart list, then integer intervals, or use an equivalent balanced disjoint partition. The productive depth is bounded by the logarithm of the record count plus the logarithms of the side lengths, O(B+log n) in the stated regimes. At a singleton, u,v,τ and E are decoded by fixed-degree integer evaluation. No root search or hidden carry oracle is needed at a leaf. This is a representation theorem, not a paid product routine. All restricted products, chart-list subsets, coefficients rebuilt after restrictions, gcds and decoding must be included in the evaluator's cost.

On W020's promise (odd N with at least two distinct prime factors), draw alpha exactly uniformly from 1,…,N−1. A nonunit gcd already splits N. Otherwise the scheduled good base and its covered range contain a retained leaf whose exponent is the nonzero multiple (p−1)(vq−u) of p−1. Therefore 1−alpha^E vanishes modulo p for every such unit alpha. The union over all retained bases/ranges satisfies coverage even though a particular bad base need not.

A trial is the complete covered public schedule, with the same original alpha, stopping early on a factor or on a localized full collision followed by the complete W020 two-adic chain. A unit product on one base continues to the next. A collision from an earlier, possibly bad, base is also valid: all its leaf exponents are nonzero, and W020's pointwise failure-set proof allows adaptive leaf selection. A full product gcd at an internal node still must be localized before an exponent is used. Do not resample or prefilter alpha according to a guessed good base, or replace it by a powered image.

The accepted expected count at most two trials therefore composes unchanged **provided a finite correct evaluator/localizer is supplied**. For deterministic acquisition P and a uniform complete-trial bound T_eval including all bases, restrictions, widths and recovery, expected cost is at most P+2T_eval, with preprocessing added. A detector that can miss a nonunit leaf requires its own failure accounting. No high-order-base step is restored.

**Disposition and the unpaid computation.** Accept the filter and symbolic coverage proof, the explicit polynomial prime schedule, and the ordinary-box/localization representation. Repair the informal uniformity claim with the concrete bounds above; small targets use k=1, admissible recomputed rectangles and paid carry widths, not a blanket finite-input fallback. No mathematical counterexample to the repaired W024 construction was found. The loss at p≡1 for one base and the loss at p≡−1 under whole-chart exclusion are real and explicitly accounted for.

The new overhead comprises the prime sieve/product/gcd schedule; at most n complete base schedules; ℓ-dependent brute-force root trials and Hensel/inverse work; rounding M and recomputing all range/stratum endpoints; chart enumeration, coefficients and the sign tests. Those costs are constructible and bounded above here. They do not become free because they are polynomial logarithmic. The still-unpaid central work is an exact shared product evaluator over the retained charts, with equally paid restrictions/localization, preprocessing/storage and exponent setup. The unbalanced carry count, all factor ranges and the inherited small-factor screen remain obligations for any complete exponent claim.

The next decisive object is a concrete batched evaluator for these filtered ordinary boxes, or a separately proved representation with a smaller paid carry occurrence count. Another certificate of the residue identity would not answer that question. **Verified complete improvement remains NONE.**

Only this report and its assigned evidence directory were written. The [read-scope and verification record](W024-prime-filter-review-evidence/verification.json) and [delivery manifest](W024-prime-filter-review-evidence/delivery-manifest.json) preserve the final boundary. All reviewed claims refer to the frozen inputs, not concurrent parent edits.
