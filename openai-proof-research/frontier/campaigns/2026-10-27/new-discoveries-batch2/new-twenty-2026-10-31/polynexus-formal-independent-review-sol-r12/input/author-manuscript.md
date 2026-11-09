# Polynexus formula for the contiguous-diagonal source monoid

MathDB 352496. Formal implementation candidate, credit zero pending independent review and root acceptance. This manuscript uses the explicit interpretation of the literal MathDB record supplied by its cited paper, Fikioris–Fikioris, arXiv:2111.01863v3, §§2–4 and §8, equations (53)–(55), Remark 3. It does not identify that submonoid with the entire rook monoid. Current prior-art and significance clearance remain separate and are not claimed here.

## Statement and matrix semantics

For a positive integer n, let M_n consist of the zero n-by-n matrix and the matrices X(d,k,m), for signed integer d and natural k,m, satisfying

1-min(0,d) ≤ k ≤ m ≤ n-max(0,d).

At one-based indices i,j, the entry is 1 exactly when k≤i≤m and j=i+d; all other entries are zero. Products are ordinary finite matrix products. Count ordered pairs of nonzero operands, with multiplicity as pairs, whose product is nonzero. Denote this cardinality by psi(n). Then

120 psi(n) = (n+1)^7-n^7-(n+1)^3+n^3.

The rational formula follows on dividing by 120. The same definitions at n=1 give exactly one nonzero pair. There is no claim of noncommutativity at n=1.

Lean `PSrcLeg_printed` proves equivalence of the printed signed min/max inequalities with `PSrcLeg`. `PNZ_source` proves that membership of the actual finite operand set is exactly membership of `PSourceMn` excluding its genuine zero. `polynexus_literal` states the integer identity directly for the filtered finite set of ordered matrices with ordinary nonzero product. `polynexus_one` covers n=1.

## Coupled diagonals and source correspondence

Set a=k-1, b=k+d-1, e=m-k. Legality becomes a+e+1≤n and b+e+1≤n. The zero-based matrix B(a,b,e) has entry 1 at (a+t,b+t) for 0≤t≤e. In particular its row and column positions use the same t. Its support is a diagonal segment, not the Cartesian product of two intervals. Conversely d=b-a, k=a+1, m=a+e+1 recover every legal source matrix. The signed cast and subtraction identities, equality at every matrix coordinate, nonzero corner, and injectivity on legal parameters are proved in `PolynexusDiag` and `PolynexusSrc`.

For X=B(a,b,e), Y=B(c,q,f), a nonzero summand in a product entry requires a middle position j=b+u=c+v with the corresponding outside positions a+u and q+v. The fixed outside row determines u and j uniquely, so the ordinary sum has at most one nonzero summand. Consequently XY is nonzero precisely when [b,b+e] and [c,c+f] intersect. The full coupled entry formula, disjoint zero branch, overlapping nonzero witness, and legal block closure are proved in `PolynexusProd`, `PolynexusClose`, and transported to source matrices in `PolynexusSrcPrd`. The coefficient model is ordinary natural-number arithmetic, matching the source 0/1 inner products; it is not Boolean multiplication or a distinct-output quotient.

## Partition and gap count

Let T be the number of nonzero operands. Partitioning legal triples by e yields T=Σ_{e<n}(n-e)^2, hence 6T=n(n+1)(2n+1), proved by induction in `PolynexusCount`.

Let D count ordered zero pairs with [b,b+e] strictly to the left of [c,c+f]. The map (X,Y)↦(Yᵀ,Xᵀ) is an involution interchanging left and right classes; transposition swaps a,b in the coupled block. The zero classes are disjoint and exhaustive, giving psi+2D=T². This is proved in `PolynexusPartition` without assuming commutativity.

A left pair is equivalent to the seven coordinates (g0,g1,g2,e,f,a,q), where

g0=b, g1=c-(b+e+1), g2=n-(c+f+1),

g0+g1+g2+e+f+2=n, a+e<n, q+f<n.

All gaps are nonnegative. The inverse reconstructs the actual pair

(B(a,g0,e), B(g0+e+1+g1,q,f)).

`PolynexusGap` proves legal bounds and both inverse identities, then transports cardinality to actual matrix operands by the already proved parameter injectivity. Gap g1=0 allows adjacent, disjoint intervals; shared endpoints instead belong to the overlap class.

For fixed e,f with e+f+2≤n, put t=n-e-f-2. The first two gaps satisfy g0+g1≤t and determine g2. Their triangular set G_t has 2|G_t|=(t+1)(t+2). Independent starts give (n-e)(n-f) choices. `PolynexusGapCount` proves the disjoint fiber union and its cardinality, not merely a symbolic sum. Equivalently the triangular factor is binomial(t+2,2).

## Finite evaluation

The implementation uses finite telescoping polynomial identities instead of formal power series and the optional three-shift binomial closed form. It evaluates the same certified gap convolution directly.

Reindex the legal length pairs by m=n-e-1 and k=n-e-f-2. This is a bijection with 0≤m<n, 0≤k<m, with inverse e=n-m-1, f=m-k-1. Every truncated natural subtraction is justified before casting into Q. Then

2D = Σ_{m<n} Σ_{k<m} (k+1)(k+2)(m+1)(n-m+k+1).

For arbitrary rational c, induction proves

12 Σ_{k<m}(k+1)(k+2)(c+k)=m(m+1)(m+2)(4c+3m-3).

With A(m)=m(m+1)^2(m+2), a second induction gives

10 Σ_{m<n} A(m)=n(n-1)(n+1)(n+2)(2n+1).

The outer induction consequently proves

30 Σ_{m<n} A(m)(4n-m+1)=n(n-1)(n+1)(n+2)(19n²+19n+6).

The induction step adds four times the quartic sum and the new boundary term. Lean `linear_combination` verifies the polynomial identities using kernel-checkable ring normalization. No external symbolic algebra, numerical evaluation, enumeration or conjectured summation lemma supplies a proof.

Combining the two finite sums yields

720D=n(n-1)(n+1)(n+2)(19n²+19n+6).

Together with psi+2D=T² and the operand-cardinality formula, polynomial normalization proves the stated integer identity. The natural cardinalities are cast to Q for this calculation and the resulting equality is reflected into Z. This avoids truncated subtraction in the answer.

## Validation and limits

All production sources compile with pinned Lean 4.34.1, mathlib d13f23b7, one Lean worker, M3500 and warnings as errors. The cleanroom setup receipt precedes every compile and records an empty build; all twelve modules and their kernel checker runs succeeded with only that fresh build plus upstream libraries on LEAN_PATH. The legacy r7/r6 paths were used only during development.

The initial pretty-printed deep audit traversed 282 production declarations and their 7,003-declaration closure, including opaque values, and found only propext, Classical.choice and Quot.sound. Pretty-print abbreviation was detected rather than treated as complete body output; the attempted Raw audit hit the CPU limit and is preserved as failed. Sixteen disjoint exhaustive hash partitions of the same full closure instead emit types and opaque bodies with pp.all, pp.privateNames, pp.deepTerms and a raised pretty-printer step limit. Coverage reconciliation verifies all 7,003 declarations appear exactly once in the unabridged body output, with zero abbreviation symbols. Final keyed results record all actual outcomes and receipts. The negative controls change the endpoint cubic sign and assert a rectangle-style off-diagonal entry; they are required to fail and are excluded from production imports.

No independent formal or manuscript review is claimed by this implementation author. Root must resolve independent statement fidelity, significance/prior-art objections, and acceptance. The accepted campaign count remains 52/60; this implementation awards no credit.
