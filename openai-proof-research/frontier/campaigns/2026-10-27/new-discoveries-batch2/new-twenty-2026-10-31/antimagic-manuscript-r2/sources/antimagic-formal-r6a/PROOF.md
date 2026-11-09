# Round 6A proof and limits

Write N = internalEdges t n, q = t^(n-1), Z = center t n, and t = 2s.
Every statement below is symbolic for arbitrary depth, not a finite certificate.

Antimagic6ABounds proves N(n+1) = N(n) + t^n, (t-1)N+t=t^n,
and N+2 <= 2q by induction. Thus Z <= q. The inherited parity identity
N-t=2(Z-1) gives N <= tZ. The constant last-parent colour
s(2N+tq+1)+Z exceeds N+t^n for s >= 2.

Antimagic6ARoot sums the row-one arithmetic progression with the inherited
sum_range_id_mul_two identity. If R is the root colour, then
2R=2Z+(t-1)(2N-t+2). Using N=2Z+t-2 gives
2R=2tZ+(t-1)N. Since t >= 4 and N > 0, R > tZ+N.
The geometric identity also gives N < R <= N+t^n. root_weight transports
this exact sum through literal_weight_row to the constructed edge equivalence.

Antimagic6AWeights places middle weights label+tZ in [N+1,N+t^n].
Adjacent middle vertices differ by internal-label injectivity. The root is
above every first-row middle weight; last-parent vertices have the constant
colour above every label and every other row colour. These exhaustive edge
cases prove higher_local. Every integer in the high band is a leaf weight by
the inherited leaf-row bijection. All vertex colours lie in those leaf colours
plus the last-parent constant. The image-cardinality upper bound is t^n+1;
the inherited lowerBound supplies the reverse inequality. This proves
higher_colors, NonbinaryWeightCompletion, and NonbinaryHigherConstruction.

Antimagic6APatch begins the binary target after the first target closes. The
index transpose is an involution preserving each finite row. The geometric
and parity identities give N=2Z and Z+1=2^(n-1). The four row-two labels are
[2,2Z-1,1,2Z-2]. Antimagic6ABinaryInternal combines the patch involution
with inherited shell-coordinate injectivity, coverage and shell inversion to
prove all binary internal labels are injective and cover [1,N].
Antimagic6ABinaryWeights proves the literal root weight 3Z and first-row
weights 3Z+1 and 4Z-1 for any edge labeling that realizes the frozen formula.
These are separated from the root because Z >= 3. These conditional weight
identities do not assert that a binary realization has been constructed.

Still open: construct the binary parent-derived tuple permutation (including
n=3, where the last internal row is patched), then the leaf permutation and
literal edge equivalence; prove the remaining row weights, adjacent separation
and colour cover. The final endpoints retain BinaryHigherConstruction, and
for arbitrary trees ModelBridge. No unconditional resolution is claimed.

Numerical diagnostics compare reviewed and closed formulas for t=2,4,6 and
n=3,4,5, test the exact new bounds and binary row identities, and retain the
inherited grid and negative controls. They are not substitutes for the proofs.

Attribution: the higher-depth symmetric-shell/tuple construction is the reviewed
r142 construction. The inherited binary depth-two case is source Figure 5;
the nonbinary depth-two case uses published Lemmas 2.2 and 2.9. The endpoint
is the even case of published Conjecture 6.1 (HTML numbering differs).
