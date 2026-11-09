# W032: enumerate carry chambers by weighted edge walks

Parent constructive algorithm, 2026-10-08. **Unreviewed. No experiment.**
Verified complete factoring improvement: **NONE**. This replaces repeated
vertical-slab sampling, not the missing useful-factor theorem.

## Representation and target

Both current carry covers have the form

    C(x,y)=c0-sum_(i=0..m) lambda_i
                  floor((b_i+A_i*x+B_i*y)/N),
    0<=x,y<N,  0<=b_i<N,  A_i,B_i>=0 integers,
    A_i+B_i>0.

The old large-base cover has (A_i,B_i)=(i,1); the affine-lift family has
(A_i,B_i)=(i+1,i(i+1)). Use all positive threshold lines

    A_i*x+B_i*y=kN-b_i,   1<=k<=A_i+B_i.

There are J=sum_i(A_i+B_i) records, respectively O(R^2) and O(R^3).
The floor equals the sum of its threshold indicators on the square.
Thus crossing a threshold into its positive half-plane subtracts its
weight lambda_i from C. Coincident geometric lines, if present in a more
general instance, are combined with weight W equal to the sum of their
weights; orient them consistently. In these families normals have
nonnegative coordinates, so a common positive orientation is available.
The four square edges are also included for geometric traversal, with
weight zero. Boundary-only or point-touching threshold records create
no interior edge; their constant interior contribution is included by
the direct initialization below.

## Explicit traversal with no face-location oracle

For each distinct interior threshold line, and each square boundary line:

1. Clip it to the closed square. Retain the resulting positive-length
   segment, unless it coincides with a boundary already being handled.
2. Intersect this segment with every other nonparallel threshold line.
   Add its endpoints, sort the rational points along the segment, and
   deduplicate equal points. No zero-length subsegment is processed.
3. Each consecutive pair defines an open edge. Its midpoint is on no
   other noncoincident line. On the first edge evaluate C directly at a
   sufficiently small displacement into each adjacent open region.
   An interior line has two sides; a square boundary has only its inside.
4. Walk along the line to each next edge. At the intervening vertex,
   update the current side value by subtracting W_j if the positive
   half-plane of crossing line j is entered, or adding W_j if it is left.
   The sign is determined by n_j dot d, where d is the oriented direction
   of this walk. All lines at one vertex are processed atomically before
   testing an edge value. Parallel lines do not toggle. The walk's own
   line indicator stays constant on each side.
5. For an interior line, the two side values differ by exactly its W:
   C_positive=C_negative-W. Test the proper gcd of each side value with N.
   Boundary walks test only their inside value. Retain/validate factors;
   unit and full gcds are ordinary failures. Repeated regions/values may
   be tested again and are included in the bound.

Only one direct O(m)-floor initialization is needed per line; the other
side is obtained from W. Every intervening crossing changes the known
indicator sum, so subsequent edges require signed additions, not new
O(m)-floor evaluations. An arbitrary order within a tied vertex must not
produce intermediate gcd samples. The endpoints require no update after
the last open edge.

## Exact sample points and bit widths

Let B>=1 bound all integer normal coordinates, including square edges.
Line intercepts have O(logN+logB) bits. Pair intersections have reduced
denominators at most 2B^2 by the determinant formula. Edge midpoints can
therefore use denominators at most Qmax=8B^4. Their numerators are at
most N*Qmax in absolute value.

At a midpoint, the value of any nonvanishing integer line equation has
absolute value at least 1/Qmax. Choose the uniform rational displacement

    delta=1/(64*B^6),   P_plus/minus=P +/- delta*n,

where n is the walk line's integer normal. Each other line expression
changes by at most 2B^2*delta < 1/(2Qmax). Thus no other line changes
side. For an interior edge, distance to each square boundary also has
the same rational lower bound, so both perturbed points remain inside.
For a boundary edge use the inward unit normal; that sample stays inside.
The walk's own equation changes with the required sign because n dot n>0.
All points are rational with O(logN+logB) bits; no numerical epsilon or
unpriced real-arithmetic step is used.

An interior edge midpoint has strictly positive distance from every
boundary. A threshold coinciding with a square edge was excluded from
two-sided processing. Thresholds merely touching a corner have no open
segment. These conventions prevent sampling an outside region by mistake.
If several lines cross at one vertex, their effects between the two edge
midpoints are exactly the summed oriented toggles. The small displaced
paths need not cross them at the same instant; only the two final edge
floor vectors are being represented.

## Coverage and total cost

Every open chamber of a line arrangement clipped to the square is a
nonempty open convex polygon and has a positive-length boundary edge.
It may be the whole square, in which case the four square edges suffice.
An open edge is split at every crossing; the nearby midpoint on its
interior side lies in the adjacent chamber. Consequently these walks
visit every chamber, including those not containing an actual integer
lift. Existing one-sided perturbation proofs ensure all actual integer
lift outputs are among the chamber values. Extra gcd arguments are legal,
but do not acquire actual lift witnesses or uniform-lift probabilities.

For each of O(J) lines, O(J) intersections and O(J logJ) comparisons
generate the ordered vertices. Direct initialization costs O(m) floors.
The walk has O(J) edges and toggles, with tied incidences charged. Thus
the total arithmetic count is

    O(J^2 log(J+1)+mJ),

including O(J^2) individual gcds. Binomial weights, intermediate sums
and output carries have O(R+log(J+1)) bits; geometric values have
O(n+logB) bits, n=bitlength(N). All initial acquisition, unit checks and
gcd/factor validation remain paid. With the accepted fast arithmetic
model, a conservative complete primitive envelope is

    soft O((J^2+mJ)*(n+R+logB) + R^2*n).

For the large-base cover this is soft O(R^4*(n+R)); for the affine family
it is soft O(R^6*(n+R)). These improve the respective literal slab upper
bounds R^7 and R^10; they do not prove optimality or a factoring bound.
Store all line records and process one line's intersection list at a
time. Recomputing each pair from the other line costs only a constant
factor. Streaming space is soft O(J*(n+logB+R)+R^2*n), excluding a fully
retained output transcript. Producing every sample log additionally pays
its O(J^2*(n+R+logB)) output size.

The next decisive step is symbolic correctness/cost audit of clipping,
coincident lines, atomic crossing updates, rational displacement and
complete chamber coverage. No implementation or new numerical run has
been authorized by this note. Even an accepted primitive cannot establish
that one of its O(J^2) candidate integers yields a proper factor.
