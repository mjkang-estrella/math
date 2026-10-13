# I203 nomination received: exact all-height elliptic covering cost

2026-10-12. **Proved nomination under review; eight accepted, two remaining.**
The [report](i203-all-height-tiles.md) and
[analytic record](../experiments/i203_all_height_tiles/analytic-attempt.md)
claim the full optimum c_L(A)=1+L^2 det A for every real trace-zero
elliptic 2-by-2 A and L>0, attained by a compact parallelogram. They also
claim the corresponding finite nonlinear cost with multiplier
1+L^2(det DV)_+. Neither result is accepted at this checkpoint.

## Initial parent check

For the normalized path I+tJ, |t|<=k, D=1+k^2, the proposed matrices are

`B=[[k,2k],[-1,0]]`, `G=[[0,2k/D],[-1,2k^2/D]]`.

The parent manually checked det B=2k, det G=2k/D and

`B^(-1)(I+tJ)G=[[1,-2k(t+k)/D],[(t-k)/(2k),1]]`.

The off-diagonal product is (k^2-t^2)/D in [0,1), so the accepted source's
deformed-square lemma applies at every height, including both endpoints.
Its actual statement was read: it imposes no smallness bound on either
off-diagonal entry separately. This is a different choice of lattice and
shape coordinates, not an invalid similarity turning an elliptic matrix
into a hyperbolic one.

The density lower bound over all bounded measurable shapes is consistent
with this construction. The parent's initial reading also checked the
staircase argument's use of a bounded downward jump despite possible
backtracking, and the small-determinant cutoff in the nonlinear transfer.
These checks motivate an independent proof review; they do not replace it.

## Acceptance work remaining

An independent proof reviewer must attack the full theorem and finite-cover
consequence, including all height quantifiers, arbitrary nonnormal A,
singular limiting regimes, compact label boundaries and the distinction
between a periodic affine optimum and an arbitrary-cylinder optimum.

A separate contribution assessment is also required. The underlying square
lemma and finite-retention construction are already accepted/known. The
candidate new content is the optimal fixed pair B,G for the entire path
and the resulting coefficient-one nonlinear bound. Novelty/significance
cannot be inferred just from a solved in-project question. The source's
primary-literature comparison limits remain explicit.

The source record's five detached outputs and two retained PDF hashes
match. Source-directory membership is exact, and the unrelated I31 digest
is unchanged. No independent mathematical test, numerical experiment or
source truth audit was run. The original nomination and proofs are retained
unchanged. No finding-count increment is made before both gates pass.
