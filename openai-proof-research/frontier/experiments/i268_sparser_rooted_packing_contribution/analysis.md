# I268 contribution analysis

2026-10-12. Final verdict **TECHNICAL**, on the authenticated I267 proposal. This is an independent contribution assessment. I257 proves only I248's old range; no proof-gate conclusion for I267 is supplied. Pinned OpenAI results are stipulated true. Target twenty, accepted ten, same chain and no count changes.

## 1. The polynomial enlargement is real

Write ρ=r^b. Compression costs O_d(ρ^(-1)) patterns, each drawn from a universe with log-size O_d((log n)^2). The source/target root and test entropy bound therefore has the general form

    A(ρ)=O_d(n^(2/3)log n+ρ^(-1)(log n)^2).

The partition witness gives μ_Q≥c_d nρ for nonempty tests. In the uncapped amplification case q≥c μ_Q; in the capped case q is linear and the estimates are easier. The old proof's uniform lower-bound tail scale is nρ². At ρ=δ=n^(-1/3)(log n)^2,

    nδ²=n^(1/3)(log n)^4=o(n^(2/3)log n).

Thus the old bounds cannot close the displayed union bound using that witness lower bound. This does not prove the old method fails for every particular Q: actual means can be larger. It identifies the deficit in its available uniform estimates. Ignoring the family cost, the old root-count balance already requires ρ much larger than n^(-1/6)(log n)^(1/2); the original n^(-.01) range had considerable further slack.

The two improved relative tail scales are c_d μ_Q and c_d q, both at least c_d nδ in the submitted analysis. At δ they are of order n^(2/3)(log n)^2, whereas the family entropy is only O_d(n^(1/3)). The ratio to the dominating root entropy grows like log n. Both changes are needed: retaining either old n-scale variance charge leaves the available exponent too small.

For fixed b, the lower permissible r changes from n^(-1/(100b)) to n^(-1/(3b))(log n)^(2/b), a polynomial gain. For s=c log n and fixed c>0, b=dc log n+O_d(1), so log(1/r)≤1/(3dc)+o(1). These symbolic comparisons are not numerical experiments. The endpoint exponent 1/3 is the balance with the full-root enumeration, not a demonstrated rooted-density critical exponent. Replacing log² by another sufficient logarithmic margin would change no structural mechanism; no such revised theorem is nominated here.

## 2. A general optimum-witness deletion property

Let feasible objects be disjoint sets U of at most d vertices, with local weights w_U in [0,1]. Let independent coordinates X_v be such that changing X_v affects weights only for U containing v. Set Z=max_P sum_(U∈P)w_U and define Z_v by restricting to U avoiding v. The latter is a function of the coordinates other than X_v. For one fixed optimum P, restriction loses at most the weight of the unique U containing v. Consequently

    0≤Z−Z_v≤1,
    sum_v(Z−Z_v)≤sum_(U∈P)|U|w_U≤dZ.

This deterministic property needs no exchange of maxima, differentiability, independent item weights or unique optimizer. It is generic for bounded local disjoint packing. I267 verifies its hypotheses by assigning root-incidence and later-nonroot edges to X_v; deleting v removes every local use of that coordinate. Both ordinary ν_Q and smoothed W_Q fit this same lemma. The weighted loss is charged to w_U, so the summed bound is d times the weighted optimum, not d times an unrelated cardinality bound.

BLM Theorem 1 then gives the displayed tails at a=d,b=0. For d≥2 its lower-tail c_- is zero. For the source upper tail E W_Q≤μ_Q and t=μ_Q/8 suffice: the event W_Q>9μ_Q/8 implies W_Q>E W_Q+μ_Q/8, and the BLM denominator is O_d(μ_Q). Relative upper tails need only an exp(−c_d μ_Q) bound; the additional linear-t term is harmless here. Opting Into Optimal Matchings' discussion of that term concerns a stronger desired Gaussian-type accuracy, and is not an obstruction to I267's constant relative accuracy.

The close primary precedents are Blum et al.'s bounded-cycle packing/vertex-sampling deletion proof and Ezra et al.'s weighted packing and extended-XOS optimum proof. Neither models all I267's random-edge dependencies or implies its exact two-host statement. Together with the fully read BLM theorem they demonstrate that the proposed refinement belongs to an established optimum-witness concentration technique. Paying the dependent-local-weight distinction is useful but requires no new rooted structure.

## 3. The permutation improvement

A q-matching uses exactly the first dq entries of a uniform permutation. Under a fixed prefix, swapping two alternative next values bijects their completion laws and changes at most two avoidance indicators, including when the other value lies in the unused suffix. At the dq-th exposure the statistic is already known. There is no reason to charge the remaining N−dq increments, which are zero. Azuma with dq increments of absolute size at most two gives exp(−t²/(8dq)); taking t=7q/16 gives exp(−49q/(2048d)). This is the stated mean-scale avoidance estimate.

This is a check of the proposed improvement's nature and scale, not a certification of all cap/floor or conditioned-layer statements. The construction of a uniform trimmed matching from an invariant optimum and independent layers is unchanged from I248/I257. Root-fixed host symmetry survives arbitrary root overlap, but candidate lists would remove it. The restriction |B|<N/(16d) remains exactly the reservoir-slack reason for E X_B≥15q/16.

## 4. Contribution calibration

The strongest positive case is now stronger than I258's: the proof reaches sublinear guaranteed supply near the root-test entropy scale, where its former concentration estimates were insufficient. The polynomial r-range is materially broader. The prior n^.99-based objection is explicitly withdrawn.

The remaining objection is substantive to the gate: both new steps are standard refinements of the same generic optimum/symmetry lift. Arbitrary overlap and adaptive root/family tests come from pinned175; compatible-block hypergraphs and matching/sprinkling architecture are classical FLN/NS. No new handling of sparse subgraph bottlenecks, constrained candidate capacity, depleted reservoirs or larger components is established. No application beyond the same bounded-component AH consequence is demonstrated. The improvement is not rejected solely because d is fixed, a cap exists or a sharp threshold is absent; those restrictions explain why the generic refinement suffices without paying a further obstruction.

FLN's different-index covariance uses disjoint root neighborhoods. NS's rooted-density Janson proof uses disjoint root tuples. Hence the precise I267 theorem is not identified as KNOWN. Search absence does not establish novelty, and incomplete worldwide priority does not force an UNRESOLVED contribution verdict. The accessible primary comparisons support TECHNICAL now.

A substantive repair needs an explicit new consequence or a mechanism beyond this local-optimum/variance refinement, such as capacity-governed candidate restrictions, or feasible low-supply transfer whose test-sensitive hypotheses replace blanket root entropy. None is proved here. A separate proof gate remains necessary, irrespective of this contribution decision.
