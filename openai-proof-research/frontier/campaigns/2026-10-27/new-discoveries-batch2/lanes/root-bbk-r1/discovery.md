# BBK refinement: root continuation, no result

Credit0. Source Banerjee-Bringmann-Keith, arXiv2601.04014v1, Section5 Conjectures5.1 and5.2. Root read actual current HTML Section5 and the prior exact source/partial-results lane. Full nonnegative coefficient statement remains open here; no Lean or paper is warranted.

Put O_r(q)=prod_{j=0}^{r-1}(1-q^(2j+1)). For a=n+1>=1 and b=k-1>=0, the literal source series is

    F(a,b)=O_(a+b-1)/(O_a O_b).

For a,b>=1 this is symmetric; it is the source symmetry, not a new result. If a=1 or b=1 it is 1/(1-q). Previous source/lanes already cover these boundaries; no credit. The source stronger comparison is exactly F(a,b)>=_coeff F(a-1,b+1) in its stated range. Direct cancellation gives, for n>=1,k>=n+1,

    G_(k,n)-G_(k+1,n-1)
     = q^(2n+1) (1-q^(2(k-n-1)))
       (q^(2k+1);q^2)_(n-1)/(q;q^2)_(n+1).

At k=n+1 it is zero. At k>n+1 the residual rational function still needs coefficient positivity; writing it does not prove that property. check_monotonicity.py computes exact integer prefixes of this residual. All1600 pairs1<=n<=40,1<=k-n-1<=40 have no negative coefficient through shifted degree1200. These are finite prefixes, not all coefficients, not a proof, not an eligible finite result. Existing much larger5.1 checks are not recounted.

## Two ruled-out proof routes

1. Divisibility matching: multiply F(a,b) by1-q^L for an odd common period L, then try pairing every denominator factor with a numerator factor divisible by its weight, producing geometric polynomials. At a=b=10 denominator weights are1,3,...,19, numerator weights21,23,...,37 plusL. Neither17 nor19 divides any weight21..37. Both therefore need the single L factor. A bijective pairing is impossible, for every L. This disproves this proof scheme, not positivity or an arbitrary more complicated decomposition.

2. Complete intersection: realize F(10,10) as the Hilbert series of nine homogeneous equations of degrees21,23,...,37 in a polynomial ring with variable weights1,3,...,19. Restrict to the coordinate plane carrying weights17 and19. Every positive-degree monomial involving only these two variables has degree17,19, an even sum in{34,36,38}, or degree>=51 if it has at least three factors. None equals21,23,...,37. Thus all nine equations vanish on the entire coordinate plane, for any choice of coefficients. Their zero locus has dimension at least2; they cannot form a regular sequence of length9 in dimension10 (whose quotient would have dimension1). This specific homogeneous complete-intersection realization is impossible; no conclusion about other Hilbert-series constructions follows.

A still broader invalid criterion is that every odd cyclotomic polynomial divided by1-q has nonnegative coefficients. Exact sympy expansion refutes it already atPhi_105: the prefix sum at degree9 equals-3. This supplies no BBK counterexample because its other cyclotomic factors cannot be discarded.

## Honest remaining gaps

A uniform nonnegative coefficient decomposition, partition injection, or valid analytic/integer-tail proof is absent. The simple-pole/eventual-periodicity facts in the previous lane do not alone establish a sign. An attempted residue-amplitude proof would need uniform control in both indices and a proof of the full initial segment, not just eventual positivity. No claimed novelty, resolution, formal endpoint, paper or acceptance. Do not count the symmetry, cancellation identity, finite scans, boundary cases or failed-method obstructions.

Primary source: https://arxiv.org/html/2601.04014v1 . Prior full refinement context: pi-discrete-discovery-r7/FINDINGS.md in the previous campaign. Chern-Wang2601.19845 resolves the motivating sum, not automatically this refinement; root has not independently reread that entire successor in this continuation.

## Further termwise-transformation obstruction

A finite q-Chu-Vandermonde convolution suggests, for k>=2,

    G_(k,n) = sum_(j=0)^n q^((2k-2)j)
      [k+n-j-2 choose n-j]_(q^2)
      (q^(2j+2);q^2)_(n-j)/(q^(2j+1);q^2)_(n-j+1).

This is the usual finite convolution (ab;Q)_n = sum_j [n choose j]_Q (a;Q)_j (b;Q)_(n-j) b^j, with Q=q^2,a=q,b=q^(2k-2), followed by elementary cancellation. It is an identity route, not a positive decomposition.

Even in the source-symmetry triangular range k>=n+2, its individual terms need not have nonnegative coefficients. Take k=n+2,j=n-1,n>=3. After removing the positive monomial shift, that term is

    (1+q^2+...+q^(2n)) (1-q^(2n)) /
       ((1-q^(2n-1))(1-q^(2n+1))).

Its coefficient at degree2n+2 is-1: the numerator has coefficient-1 there, every numerator exponent is even, one denominator part has odd degree, and two denominator parts have degree>=4n-2>2n+2. The positive numerator ends at2n, so no other contribution occurs. The explicit n3,k5,j2 instance was verified by exact integer series arithmetic (-1 atdegree8). Thus a claim that this finite convolution is termwise positive is false, including after the valid source symmetry reduction. This does not refute the full G sum; it identifies unavoidable cancellation in this route.

The still simpler possible assertion (q^2;q^2)_n/(q;q^2)_(n+1)>=_coeff0 is false: n3 has coefficient-1 atdegree12. Chern-Wang's actual denominator length2n in their separate positive theorem cannot be shortened to n+1 without proof. No such theorem is invoked here.
