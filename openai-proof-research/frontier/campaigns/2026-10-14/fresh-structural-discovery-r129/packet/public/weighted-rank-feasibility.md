# Weighted-rank containment covers: external-field comparison

This is a prefreeze feasibility note. It is not a candidate proof, and nothing in it is nominated. The source175 integral/fractional theorem and its operative proof are stipulated. The r128 nonuniform product cloning transfer, uniform-rank thinning and conditional-negative-association transfer of the source covering lemma are already paid (r128 `threshold-feasibility.md`) and are only cited here. C0=25*512^4 is the source constant used there.

## The full question (unchanged from r128)

For n>=1, 0<=k<=n and positive reals w_1,...,w_n, let B be the random k-set with P(B)=w(B)/e_k(w), and let c_w(S)=P(S subset B). The open full-scope question is whether one absolute C>=1 works for all data, all increasing proper families F and all fractional covers g: if sum_S g(S)c_w(S)<=1/2, then F has an integral cover G with sum_(S in G) C^(-|S|)c_w(S)<=1/2.

## Mechanism tried in r129: comparison with an external-field product law

The idea was to sandwich c_w between product laws and then call the paid nonuniform product transfer. This is different from the r128 marginal-product substitution because the comparison law is chosen through the external field, not from the marginals.

### Exact identity (checked, elementary)

Fix t>0 and put p_i=t w_i/(1+t w_i). Let X be the random set with independent coordinates, P(i in X)=p_i. For |A|=k,

    P(X=A) = prod_i (1-p_i) * t^k w(A),

so X conditioned on |X|=k has law w(A)/e_k(w), the law of B. Since P(|X|=k)>0 and the coordinates are independent, for every S,

    c_w(S) = (prod_(i in S) p_i) * P(|X restricted to the complement of S| = k-|S|) / P(|X|=k).

For |S|>k both sides vanish. The mean-field choice of t is the one with sum_i p_i=k. The identity is a standard rank-conditioning computation. It is recorded only to locate the gap: c_w is a product law times a rank-correction factor that depends on S.

### Conditional reduction (checked, routine, not nominated)

Let 0<a<=1<=b and let p be a vector in (0,1]^n. Assume

    (L) a^|S| prod_(i in S) p_i <= c_w(S) for every S with g(S)>0,
    (U) c_w(S) <= b^|S| prod_(i in S) p_i for every S.

If sum_S g(S)c_w(S)<=1/2, then sum_S g(S) prod_(i in S)(a p_i)<=1/2. Then the paid nonuniform product transfer, applied at the probability vector a p, gives an integral cover G with sum_(S in G) prod_(i in S)(a p_i/C0)<=1/2. By (U),

    sum_(S in G) (a/(b C0))^|S| c_w(S) <= sum_(S in G) prod_(i in S)(a p_i/C0) <= 1/2.

So the full question would follow with C=bC0/a if (L) and (U) held with a and b independent of n, k, w and F. This is a composition of paid operations. It earns nothing by itself.

### The sandwich cannot be uniform

Take n=3, k=2 and w=(M,1,1). Then exactly

    c_w({2})=c_w({3})=(M+1)/(2M+1),   c_w({2,3})=1/(2M+1).

Let p be ANY vector in [0,1]^3, not only a field vector or the marginals. If (U) holds for {2} and {3}, then p_2 and p_3 are at least (M+1)/(b(2M+1)). If (L) holds for {2,3}, then a^2 p_2 p_3<=1/(2M+1). Together these give

    (b/a)^2 >= (M+1)^2/(2M+1),

which is unbounded in M. The script `cb_checks.py` confirms these rational values for M=10, 100 and 10^4. This strengthens r128's marginal-product diagnosis to every product comparison law. It uses the same r128 example and is a diagnosis of the substitution only. It is not a counterexample to the full question: a family that uses {2,3} in its fractional cover need not use {2} or {3} in its integral cover.

### Where the comparison does and does not hold numerically

Call the data light if the mean-field p satisfies max_i p_i<=1/2. In 300 random light instances (n between 4 and 10, k<=n/2, integer weights 1..30, every S with |S|<=k), the smallest observed value of (c_w(S)/prod_S p_i)^(1/|S|) was 0.4665. The largest observed ratio of marginal to mean-field coordinate, P(i in B)/p_i, was 1.2165. These are floating-point samples, not bounds. Even a proof of a light-regime sandwich would give only a restricted version of the question. That is a weaker variant of the named interface, so it is not a candidate.

Outside the light regime the per-coordinate lower ratio drifts toward zero. In the sampled overload instances, m coordinates have odds 0.55/0.45 and m coordinates have odds (1-eps)/eps, k is the rounded value of 0.55m+(1-eps)m, the mean-field vector is then recomputed numerically, and S is the first block. The observed values were 0.4376 (m=20, eps=0.05), 0.2451 (m=20, eps=0.01), 0.2450 (m=40, eps=0.01) and 0.1209 (m=40, eps=0.002). The exact identity explains the mechanism. Containing the whole first block forces the heavy block to give up about 0.45m elements, an event of probability roughly eps^(0.45m) under the field law. These numbers are sanity output only.

## Why this stops

In the overload regime, coordinates whose field probability is close to one make the rank-correction factor exponentially small in |S|. No single product law then sandwiches c_w. A proof of the full question would have to control that factor against the fractional cover of the ORIGINAL law. This is the same simultaneous budget/certificate requirement that r128 isolated for the source's selector and signed-weight step. The external-field comparison does not supply it. Neither a split into heavy and light coordinates nor conditioning on the heavy part was carried to a common budget. Conditioning changes the rank of the light part and its field, so the paid uniform-rank transfer does not apply to the conditional laws with a uniform constant. No exact target was frozen.
