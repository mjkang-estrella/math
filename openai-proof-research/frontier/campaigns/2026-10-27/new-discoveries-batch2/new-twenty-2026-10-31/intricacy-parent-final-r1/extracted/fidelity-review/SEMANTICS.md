# Independent semantic and calculation notes

All Lean locations below refer to the frozen `intricacy-entropy-r5` sources. These are independent checks of the displayed definitions and proof terms, not reliance on the author's bridge index. Every mathematical module was read in full. `source-declaration-locations.json` locates every source-written declaration; `complete-inventory.json` additionally includes generated declarations.

## Two-sided construction and complete law class

`TwoSided333569.lean:24` starts the Ionescu–Tulcea trajectory at index zero with the specified symbol; `halfLaw_zero` proves that symbol is fixed almost surely. Conditional independence of the two trajectories is genuine product measure independence. Gluing at zero uses the forward branch; the backward zero agrees almost surely, as used explicitly in `Stationarity333569.lean:36`. There is no unjustified independent duplicate symbol at the origin.

Using the same transition matrix backwards needs reversibility. This holds for every binary stationary interior matrix: with u=P00, v=P11, pi0=(1-v)/(2-u-v), pi1=(1-u)/(2-u-v), the off-diagonal flow is (1-u)(1-v)/(2-u-v) in both directions. Diagonal flows are tautological. `detailed_balance` and `path_balance` implement exactly this argument. `twoSidedLaw_window_forward` changes the backward product to chronological order, and `window_wordProb` reindexes the finite product. Repeated left marginalization uses stationary invariance; right marginalization uses row normalization. These give every translated block, even blocks wholly on the negative side (`twoSidedLaw_word`, Stationarity:290).

`measure_eq_of_blocks` (Stationarity:313) does not assume the measures equal merely from origin cylinders: it uses every translated block. Each finite coordinate cylinder is a preimage of a finite-window event, with window [-N,N], N=max |coordinate|; measurable cylinders form a generating pi-system. Equal total mass and finiteness are supplied. This is sufficient for full measure equality and hence all integer translations (`twoSidedLaw_shift`). Open positivity follows because any nonempty product-open set contains a finite equality cylinder, which in turn contains a positive pair of full half-path cylinders. `twoSidedLaw_fullSupport` is the standard `Measure.IsOpenPosMeasure` instance, not a custom predicate.

`OneStepMarkovLaw` (WeakMarkov:10) allows u,v in [0,1], nonnegative normalized p, pP=p, and ALL translated block products. A stochastic binary matrix has exactly this diagonal parametrization. Zero-mass states need not have well-defined conditional ratios, and the definition does not require them. At u=v=1, any stationary mixture of the two constant sequences is included. At u=v=0, the uniform two-cycle law is included. Absorbing deterministic laws are included. There is no exclusion by positivity, ergodicity, correlation sign or full support in this comparison predicate. Conversely these cylinder products imply stationarity by the same block-uniqueness argument, without needing irreducibility. A separate global boundary-law construction is unnecessary: the predicate quantifies over existing actual probability measures and uses precisely the source presentation (6.1).

## Selected observations and entropy normalization

`Selected333569.lean:43` partitions an arbitrary finite-past event by containing block atoms. Its event-determination condition makes each intersection either empty or a whole block. This justifies applying the proved next-symbol formula to a sparse past. Induction over g in `twoSidedLaw_past_gap` contracts each intermediate state using kernel composition; g=0 is the identity, not an extra positive-gap assumption. `twoSidedLaw_selected` then takes successive differences of strictly increasing integer times; their `.toNat` conversions are legitimate. The construction covers arbitrary finite gaps and translated times.

`entropy_chain` is the finite positive-chain log-product identity, with row normalization and no missing initial normalization hypothesis: normalization of p is not needed for this algebraic identity, but is supplied by its applications. All selected chain probabilities are positive in the chart, so `Real.log_mul` never needs a zero extension there. The source function is -sum p log p; mathlib's natural logarithm gives 0 log 0=0 at zero as required. `rankZeroSampleEntropy` is exactly the atom entropy of the join of coordinate-zero partition translates, including the empty join. The measure is an actual probability measure, so `.toReal` is finite; it is identified with the nonnegative real marginal before logarithms are simplified.

The finite rank-zero definition uses twice averaged sample entropy minus full-block entropy. This equals the literal source expression with the complement: on subsets of a finite N-coordinate universe, S -> S-complement is an involutive bijection, so sum H(S-complement)=sum H(S); the constant full-block term has 2^N occurrences and total uniform weight one. This elementary interpretation is external to the custom Lean definition; it is not a missing analytic hypothesis or a different entropy. N=n+1 simply discards the undefined zero-size normalization and exhausts all positive block lengths.

Independently counting selections: fixed endpoints a<b, gap i=b-a, force two selections and i-1 omissions. There are N-i-1 unrestricted coordinates, hence 2^(N-i-1) choices. There are N-i endpoint pairs at gap i. Every nonempty selected set contributes one initial entropy H0; there are 2^N-1 such sets. Consequently

2 E H(selected) = 2(1-2^-N) H0 + sum(i=1..N-1) (N-i)2^-i H(l^i,t).

Subtract H0+(N-1)H(l,t), divide by N, and obtain

[(1-2^(1-N))H0+H(l,t)]/N
 + sum(i=1..N-1) (N-i)/N * 2^-i H(l^i,t) - H(l,t).

This agrees exactly with `finiteIntricacy_series_boundary` (EntropyLimit:91), including its positive H(l,t)/N correction. For N=1 the total is zero, as it should be. The gap index g=i-1 has range g<n; N-i=n-g and its weight is 2^-(g+1). `FairSelections` proves the free-selection equivalence, sorted adjacency bijection and count; `FairEntropy` groups pairs by gap. No independence of overlapping pair indicators is needed.

The triangular coefficient is in [0,1], tends to one for fixed gap, and entropy is in [0,log 2]. Geometric domination therefore proves the stated limit. This is the same series as source Proposition 5.10 after multiplying Asc by two and subtracting entropy rate. Source conditional entropy reads the other direction, but stationary endpoints have equal entropy, so H(X0|Xi)=H(Xi|X0). Binary reversibility also suffices here. The literal finite formula avoids dependence on the source proof's notation slips.

## Actual calculus and full local promotion

Write x=(1-r)/2, h=binEntropy. The actual function is
H(r,t)=(1+t)h(x(1-t))/2+(1-t)h(x(1+t))/2.

Differentiating both weights and arguments gives
H_t=[h(x(1-t))-h(x(1+t))]/2
 +x[(1-t)h'(x(1+t))-(1+t)h'(x(1-t))]/2,
H_tt=-x[h'(x(1-t))+h'(x(1+t))]
 +x^2[(1+t)h''(x(1-t))+(1-t)h''(x(1+t))]/2.

Here h'=log(1-x)-log x and h''=-1/(1-x)-1/x. At t=0, H_tt=-2x h'(x)+x^2 h''(x)=2c(r), where
c(r)=-(1-r)log((1+r)/(1-r))/2-(1-r)/(2(1+r)).
Thus the frozen coefficient is correctly identified with half an actual derivative. It is not a substitute definition of curvature. Direct differentiation gives
c'=log((1+r)/(1-r))/2-r/(1+r)^2,
c''=4r/((1-r)(1+r)^3).
Since c'(0)=0, c increases strictly on [0,1). For 0<l<1, c(l^i)-c(l)<=0 and the i=2 term is strictly negative. The coefficient series is summable by its monotone bound between c(0) and c(l). No sign assumption on c itself is used.

For b<1, delta<1, r in [0,b], |t|<=delta, both entropy arguments lie in [(1-b)(1-delta)/2,(1+delta)/2], a compact subset of (0,1). `entropy_transverse_uniform_bounds` explicitly includes r=0. This matters because l^i approaches zero; a compact interval bounded away from zero in r would have been inadequate. The first and second t derivatives are jointly continuous there and bounded. `entropySeries_hasDerivAt` applies the smooth-series theorem twice on a preconnected open interval, with summable geometric derivative majorants and convergence at zero each time. `entropySeries_second_derivative` identifies deriv with seriesSlope on a neighborhood before differentiating. `seriesCurvature_continuousOn` supplies joint continuity in (l,t). There is no hidden longitudinal derivative or exchange of an unbounded family of limits.

On t=0, each diagonal entropy difference is nonnegative, strictly positive for gap two; the uniformly convergent diagonal series is continuous on [0,1] and vanishes at its endpoints. Its maximum is attained inside. Joint curvature continuity makes F_tt negative on a whole rectangle about (l0,0). For each nearby l, the t-slice is concave on that same interval; evenness and the midpoint inequality give F(l,t)<=F(l,0). Diagonal maximality bounds the latter by F(l0,0). `entropySeries_has_local_max` therefore is a two-dimensional maximum, with no uniqueness or longitudinal strictness assumption.

## Weak topology and junk-limit avoidance

The probability-measure topology is the existing mathlib weak topology, induced through finite measures. `complete-inventory.log` prints its actual instance. There are no new topology instances; the only local logical instance is classical decidability in finite selection combinatorics. `lawMass_continuous` uses clopen portmanteau; the cylinders in question are clopen in the actual product topology. Ratios recover P00 and P11 wherever the two one-state masses are positive.

At the witness both masses are positive. Positivity, interior recovered diagonals and the local source maximum pull back to genuine neighborhoods via continuous functions. For every Markov law in their intersection, `stationary_unique` solves pP=p and p0+p1=1 with nonzero denominator; `markovLaw_eq_bundled` uses all translated cylinders to identify the entire law. No comparison law in this neighborhood escapes the chart. Neighborhoods are nonvacuous: the actual witness belongs to the class and satisfies the open conditions. The predicate's boundary/nonergodic members are not silently removed; those that cannot meet the open conditions cannot be arbitrarily near this witness.

`bundledLaw_actualIntricacy` alone only transports two limUnder expressions, and would not close a convergence gap. The final proof separately uses `finiteIntricacy_tendsto_series` at the witness. More decisively, `markov_neighborhood_convergence` forces the inverse chart into 0<l<1, |t|<1 in a neighborhood, proves actual-law equality there, and transports the convergent finite sequence and its limit for EVERY comparison law there. Intersecting that neighborhood with the local-maximum neighborhood prevents any junk limUnder value in a relevant comparison. Global convergence outside the neighborhood is neither proved nor needed for this local assertion.
