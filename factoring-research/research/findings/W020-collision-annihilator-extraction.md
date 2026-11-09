# W020 parent construction: use global collisions as annihilators

2026-10-08 local. Proposed replacement for W019 A's large-order preparation,
component-order checks, global sorting/removal and per-tag quadratic recovery.
Independent audit pending. No new complete exponent is claimed, and this
does not implement the missing implicit pair-product evaluator.

## The changed computation

All W019 powers have one known preimage alpha. A full-modulus collision is
therefore not merely an unsuccessful duplicate: it supplies an annihilating
integer exponent for alpha. Use the full squaring chain on alpha, rather
than recovering and deleting every globally matched tag before the product.

Consider odd composite N with at least two distinct prime factors. Draw
alpha uniformly from 1,...,N-1. A nonunit has a proper gcd immediately.
Otherwise use an exponent-indexed family of differences

    d_i = alpha^(A_i) - alpha^(B_i) mod N,

where signed exponents have paid binary widths and are evaluable when the
index i is recovered. Require:

1. For every unit alpha, at least one d_i has a nonunit gcd with N (coverage).
2. For every possible leaf, the integer E_i=A_i-B_i is NONZERO.
3. The product or collision evaluator can localize one nonunit leaf at its
   stated cost, including pair-dependent domains and empty subdomains.

The family may be implicit. These are an explicit extractor's input
contracts, not a claim that the W019 implicit evaluator has been built.

On a proper leaf gcd, return the factor. On gcd(d_i,N)=N, alpha is a unit,
so alpha^|E_i|=1 mod N. Write |E_i|=2^s*u, u odd, and inspect the full chain
alpha^u, alpha^(2u),...,alpha^(2^s*u), testing gcd(x-1,N). Return a proper
factor when found; otherwise restart with a fresh alpha.

## Success does not require independence of the chosen leaf

Write N=product p_j^e_j only in the proof. On the unit branch the local
components of the ORIGINAL alpha are independent uniform units. Let v_j
be the 2-adic valuations of their orders. If some v_j differ, every positive
annihilator of alpha produces a proper gcd somewhere in its full squaring
chain. Extra powers of two in E must not be discarded by checking only
the final half-exponent.

For two distinct odd prime-power components, the W018 counting proof gives
P(v_1=v_2 | alpha unit)<=1/2. A failed collision trial is contained in this
equal-valuation event: coverage supplies a nonunit leaf; a proper leaf gcd
already succeeds; a full leaf gcd supplies a nonzero annihilator which
splits on unequal valuations. The selected leaf and E_i can depend on alpha.
There is NO inference about valuations conditioned on a global collision.

Thus the proposed procedure has at most two expected trials, with all
outputs checked, if coverage and finite localization hold for every unit.
If the evaluator is randomized and sometimes misses all collisions, that
miss probability and its possible correlation need a separate contract.
Prime powers require preprocessing and are not included in the half bound.

The additional extraction work is polynomial in log N and bitlen(|E_i|),
including reading, sign, odd-part scan, binary powering and all chain gcds.
No order of alpha or factorization of E_i is needed. This is a direct
composition of the accepted W018 annihilator argument, not a novelty claim.

## Apply it to the explicit W019 cover

Retain the independently reviewed signed cover and root intervals. Do NOT
prepare an element of large order. For the newly sampled alpha simply set
beta=alpha^(m^2). For each block start t0 keep

    gamma = alpha^(u+vN-s) * beta^(-t0).

At baby j the difference beta^j-gamma is a unit multiple of

    alpha^(s+m^2*(t0+j)) - alpha^(u+vN).

The leaf exponent, up to a harmless sign, is therefore

    E = u+vN - [s+m^2*(t0+j)].                         (C1)

The true covered S=up+vq still guarantees a collision modulo p for EVERY
unit alpha, even when all baby powers coincide modulo p or modulo N.
Distinctness is unnecessary for existence and for this extraction rule.

Construct the monic product of ALL giant factors and evaluate at ALL B
babies. Repeated points and roots are allowed over Z/NZ. Scan the resulting
B gcds until one is nonunit. If its gcd is proper, return it. If it is N,
descend to one nonunit giant leaf. The leaf gcd is either proper, or full;
in the latter case apply (C1)'s annihilator chain. There is no global-match
deduplication and no enumeration of all tags sharing that baby. Only the
localized leaf's u,v,s,t0,j is needed. The exact operation remains paid
O~(B+G) for the explicit monic product/remainder trees and one descent.

## Nonzero exponent guard, including padded baby positions

Use the reviewed root interval S in [-W,W], with 1<=u<=U, |v|>=1. Each
block starts at a valid t0; its last block can use all B babies. Then every
padded candidate satisfies

    -W <= S' <= W+m^2*(B-1).

The computable strict guard

    U+W+m^2*B < N                                     (C2)

implies |E|>=N-U-|S'|>0 for every leaf. Both signs of v are covered. It
excludes the trivial integer identity E=0 BEFORE searching, rather than
assuming a random base will make it useful.

For m=Theta(N^(1/5)), B=ceil((N/m)^(1/4)), W<=6sqrt(mN), U<m, the left
side is O(N^(3/5)), so C2 holds for sufficiently large N. A fixed small-N
fallback preserves the already known one-fifth exponent. More generally
for the hypothetical m=Theta(N^(1/3)), B=Theta(N^(1/6)), it is O(N^(5/6)),
again below N eventually. These are asymptotic guards, not chosen numeric
cutoffs; an implementation tests C2 exactly and must price its fallback.

If intervals are not padded, use U+W<N. An arbitrary exponent-family
extractor cannot omit the nonzero guard: alpha^0=1 supplies no positive
annihilator and can trap a descent on a useless full-gcd leaf for every alpha.

## What an implicit evaluator would now have to supply

Suppose it computes a product over its exponent-indexed domain and permits
restrictions that partition this domain, with product conservation and
poly(log N)-depth descent to a leaf. At a nonunit product, evaluate a child:
proper gcd returns; full gcd descends there; unit gcd descends in the other
child. No division by a nonunit is needed. If each restricted product costs
at most the full evaluation bound C, localization costs O(C log|domain|).
This sufficient bound need not be the sharpest possible one.

At the leaf, compute its signed exponent and run the above extraction.
Thus the evaluator need not output all matching tags or provide a quadratic
root test for each full match. It still must compute the product or equivalent
collision certificate, support correct restricted domains, and pay for the
pair-dependent modular roots/carries. The dominant UV cost is not removed.

The known explicit W019 expected N^(1/5) bound is not improved by this
simplification. Its value is narrower and concrete: high-order preparation,
componentwise uniqueness, and all-global-tag recovery are not necessary
conditions for a RANDOMIZED implicit multiplicative collision approach
with a common uniform preimage and a nonzero exponent at every leaf.
