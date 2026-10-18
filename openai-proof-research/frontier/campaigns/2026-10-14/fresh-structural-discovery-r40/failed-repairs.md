# Exact barriers to three capped-scale repairs

These statements reject specified proof routes at the unchanged scope in original-scope.txt. They do not refute the capped-metric target. Source099 truth is stipulated. Original arguments below are author-side, not independently reviewed.

## 1. A globally noncontracting intermediate map cannot already have the desired local expansion

Suppose, at one fixed K, that for every n there were maps G_n on all binary words of length at most n with

    ||G_n(x)-G_n(y)||_1 >= ED(x,y)

for all pairs, and image distance at most A(K) whenever one word is obtained from the other by one insertion or deletion. A longest-common-subsequence script deletes to the common subsequence and inserts the target. Every intermediate length is at most n and its number of operations is ID(x,y)<=2 ED(x,y). The triangle inequality would imply

    ED(x,y) <= ||G_n(x)-G_n(y)||_1 <= 2 A(K) ED(x,y)

for every pair. This contradicts source099's unbounded least distortion as n tends to infinity. Therefore a capped-scale construction cannot first obtain a globally noncontracting intermediate embedding with a length-independent bound on all edit edges. The periodic-free theorem escapes this argument because its restricted domain is not closed under the intervening edit path.

## 2. Short fixed blocks followed by Poisson truncation still have linear-in-K distortion

Fix any block width L>=2 and an integer m>=2. Put n=2mL and

    x=(0^L 1^L)^m,
    y=1 x[0:n-1].

Thus y is obtained by moving x's final symbol1 to its beginning. ED(x,y)<=2. The Hamming distance is2m>=4, so an equal-length one-edit script (which would have to be a substitution) is impossible. Hence ED(x,y)=2 exactly.

Partition both words into the same 2m consecutive blocks of length L. Each source block is monochromatic. The corresponding target block has the opposite symbol first and the source symbol in the other L-1 positions. Every corresponding block therefore has ordinary edit distance1 and one-sided LCS deficit1. Consequently their summed block distances and summed deficits both equal2m.

Suppose an intermediate L1 map G has the blockwise noncontraction property

    ||G(x)-G(y)||_1 >= sum_j r_L(x_j,y_j).

This is precisely the lower estimate established at the top step of the source's power-length histogram recursion; the actual-window variant has the stronger summed ordinary-block-distance lower estimate. It also holds for a direct sum of noncontracting short-block embeddings. Therefore this pair has image distance at least2m, despite ED=2. Merely stopping the recursion at a short width L=poly(K) does not remove this top-level effect when the number of blocks is unbounded.

Now apply the standard soft cap to an L1 distance r:

    h_K(r)=K(1-exp(-r/K)).

This is realizable as an L1 distance: use the source's Poisson-cut partition at rate1/K, send a point to its one-hot part vector scaled by K/2, and average over all partition outcomes. Distinct parts have distanceK and their probability is1-exp(-r/K). Thus this is an actual metric operation, not a merely numerical postprocessing of pairwise distances.

Choose2m>=K and n>=K. The above ED=2 pair then has capped image distance at least(1-exp(-1))K. Every image distance under h_K is at mostK. There is a pair of source words at edit distance at leastK, for instance0^n and1^n. In any distortion comparison with min(ED,K), its lower scale s must satisfy sK<=K, hence s<=1. The ED=2 pair forces

    D >= (1-exp(-1))K/(2s) >= (1-exp(-1))K/2.

Thus the short-block-then-soft-cap repair has distortion Omega(K), uniformly regardless of the chosen width L(K). For any fixed proposed absolute C, this eventually exceeds exp(C sqrt(log(K+2) log log(K+3))). This is a decisive failure of that repair, not a failure of every capped embedding.

The example also explains why a bound on current offset alone cannot pay cumulative boundary errors. The two strings differ by a single shift of one position, but each of arbitrarily many alternating run boundaries contributes a blockwise cost. Randomizing only the initial offset of an L-periodic grid does not solve this: every full interior length-L block still contains a shifted run boundary and has a one-symbol count discrepancy (and hence edit distance at least1). End fragments affect only a bounded number of blocks.

## 3. Independent deletion traces have the right Lipschitz bound but no length-uniform separation

Fix K>=2 and let q=1/K. Send a word w to the probability distribution P_w of the random subsequence obtained by retaining each symbol independently with probability q. This is an L1 probability vector on all finite output words (a finite set when the input cap n is fixed).

For one insertion, couple the retain/delete decisions on all original symbols; the output traces can differ only if the inserted symbol is retained, an event of probability q. The same coupling handles deletions and substitutions. Hence

    TV(P_x,P_y) <= q ED(x,y),

so K*TV is globally1-Lipschitz. No stochastic sample is being confused with the deterministic distribution-valued map.

For N>K set

    x_N=0^N 1^N,
    y_N=0^(N+K) 1^(N-K).

Their edit distance is exactlyK: substituteK ones by zeros, and note that one edit changes the number of zeros by at most1. Their traces are uniquely represented by their counts of zeros and ones. Under P_x these are independent Bin(N,q) variables; under P_y they are independent Bin(N+K,q) and Bin(N-K,q) variables.

For a unimodal integer-valued law Z, TV(Z,Z+1)=max_j Pr[Z=j], by telescoping its rising and falling probability masses. Since Bin(t+1,q) is the mixture (1-q)Bin(t,q)+q(Bin(t,q)+1),

    TV(Bin(t+1,q),Bin(t,q)) = q max_j Pr[Bin(t,q)=j].

At fixed q in(0,1), the maximum binomial point mass tends to zero as t tends to infinity. For completeness, Stirling's factorial estimate at the mode gives O_q(t^(-1/2)); no uniformity in q is needed here because K is fixed. Telescoping K times and coupling the two independent count coordinates yields

    TV(P_xN,P_yN) <= 2Kq sup_{t>=N-K} max_j Pr[Bin(t,q)=j] ->0.

Meanwhile the empty word and the one-letter word0 have total-variation distance exactly q and edit distance1. Consequently the distortion of this distribution-valued map on the capped edit domain grows without bound as N tends to infinity, at the same fixed K. Rescaling cannot repair that ratio. This rejects independent Bernoulli traces as the sole capped-distance representation, without asserting a lower bound for arbitrary embeddings.

## Remaining interface

The primary CGKK section5 min-hash construction controls synchronized partitions when local windows are distinct, guaranteed there by a periodic-free hypothesis. Its section6 periodic-marker construction instead controls edit distance between sequences of compressed blocks, not the indexed sum of original block distances. Applying the finite-cap embedding to the entire compressed sequence leaves its length dependent on n. Replacing that sequence metric by an indexed block sum incurs the explicit shift obstruction above.

A full repair must simultaneously preserve repetitive-region alignment, avoid this cumulative boundary loss, and obtain capped separation before rare alignment failures incur a length-dependent cost. Neither a bounded expected current offset nor a dimension-reduction contraction statement supplies that interface. The original all-string, all-n,K target remains unresolved; no periodic-free or weaker-distortion substitute is nominated.
