# Checkpoint: no intersecting linear detachment of the balanced source

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.
This is a construction obstruction, not a proof or refutation of LR.

## Exact geometric hypotheses

Let A be the affine plane F_q^2, q>=4, and D its q+1 directions.
For each d choose two distinct parallel constituent lines M_d^0,M_d^1.
Choose two other split lines of direction d, with four retained designated
points on each. Let S be the collection of split lines. Put
R=A minus union S, and X=R union all designated point sets. Assume each
split line meets X in exactly its four designated points.

The d-partition P_d of X has ordinary blocks X intersect L on lines L
other than the two constituents and two split lines, one merged block
X intersect (M_d^0 union M_d^1), and two opposite-pair blocks on each
split line. Assume at most B constituents pass through any affine point.
Assume EVERY nonsplit line L contains more than 2B points of X.
Assume every constituent contains a point of R. Finally assume that some
split line has two designated points in different opposite-pair blocks
and that the original partitions give every pair of distinct X-points
at least one agreement. These assumptions are all literal properties
of the balanced source's deterministic construction.

A refinement consists of partitions Q_d of the SAME X with every Q_d
block contained in a P_d block. There is no bound on the number or sizes
of refined blocks. Claim: no such refinement gives exactly one shared
block for every pair of distinct points of X.

## 1. Forced connectivity on every nonsplit line

For a nonsplit line L of direction d, join a,b in X intersect L when
their original edges agree in exactly one part. They already agree in
part d. In a different direction h, their h-lines are distinct, since
their actual joining line is L. Therefore an additional agreement can
only come from the merged h-block, with a and b on different h-constituents.

Fix a. It lies on constituents in at most B directions altogether. For
each h!=d among those directions, the partner constituent intersects L
in at most one point. Thus a has at most B nonneighbors in this graph
(on distinct vertices; a is not counted). The graph on n=|X intersect L|
vertices is connected when n>2B. Indeed, if a component C were proper,
for any vertex in C all n-|C| vertices outside C are nonneighbors, so
|C|>=n-B. Two distinct components would then give n>=2(n-B), contrary
to n>2B.

In any refinement preserving intersection, a pair with a unique original
agreement must retain that agreement in the same part: refinement cannot
create an agreement in another part. Transitivity along the connected
graph therefore puts ALL of X intersect L in one refined d-block.
This holds for every nonsplit line, including each constituent separately.

## 2. A merged cross-identification forces a duplicate

Suppose a refined d-block contains a point of M_d^0 and a point of M_d^1.
By the preceding connectivity, it contains all of X on both constituents.
Choose x in R intersect M_d^0 and y in R intersect M_d^1. Their joining
line J is nonsplit: either endpoint in R lies on NO split line. Its
direction h differs from d because the endpoints lie on different
d-parallel lines. Connectivity on J forces x,y together in refined
part h as well as in refined part d. Thus the resulting edges have at
least two common vertices. A linear refinement cannot make ANY such
cross-identification.

## 3. A split pair forces precisely such an identification

Take the stipulated designated pair a,b separated by its split partition
in direction g. Its actual joining line is that split line. It cannot
agree in any ordinary block in a different direction, and refinement
cannot restore its lost g-agreement. Intersection in the refinement
therefore requires a,b together in a merged block of some direction
d!=g. They lie on different constituents in that direction, since their
joining line has direction g. This is the cross-identification prohibited
by step2. The contradiction proves the claim. No uniqueness of the
source's adjacency generator was assumed or needed.

## 4. Application to the actual source, with no new existence hypothesis

In balanced construction.tex, eq:det-core and eq:det-split-intersection
give exactly X,R,S above. Compatibility gives the designated-point
property. The section Partitions and intersecting edges proves pairwise
intersection. Any consecutive designated pair is separated by its two
opposite-pair blocks.

The occupancy hypotheses of prop:deterministic-reduction give at least
rho*q points of X on EVERY nonsplit line: regular lines and M_d^0
have that many points in R_0 subset R; M_d^1 has that many in R.
The source's eq:det-size-condition is rho*q>2(1+B), which implies n>2B
and supplies points of R on both constituents. Hence EVERY configuration
meeting that proposition's hypotheses has no intersecting linear
simultaneous partition refinement. This is not a probabilistic claim or
an assumed numerical property of one uncomputed source example.

The source thm:main proves existence of its configurations for sufficiently
large primes with B=ceil(log q), fixed rho>0 and the displayed inequality.
We accept that theorem, not audit its probability estimates. Our deduction
uses only its deterministic interface, which has been read in full.

## 5. Why copying edges or cloning vertices does not evade the obstruction

More generally there is no r-partite linear intersecting hypergraph K
with a part-preserving vertex map pi to such a source H whose induced
edge map is onto E(H). To see this, choose one preimage edge f_x for each
source edge e_x. Different x give different f_x because their images are
different. In each part, declare x,y equivalent when f_x,f_y use the same
K-vertex. These are partitions refining the source partitions. Pairwise
intersection and linearity of K give exactly one agreement between every
pair, contradicting steps1-3. K may have arbitrarily many vertices and
additional edges; selecting these finitely many edges suffices.

This is the natural cover-preserving lift: if a cover of K had t vertices,
its images would cover H with at most t vertices, so tau(K)>=tau(H).
The contradiction rules out this entire lift for THIS source, including
edge-surjective clone constructions. It does not rule out other source
hypergraphs, non-surjective constructions, changing the number of parts,
or genuine trades that introduce new agreements rather than refining old
ones. It certainly does not prove tau<=r-1 for all linear hypergraphs.

## Limits and contribution

Forced pairs and equivalence closure are elementary operations. The
source-specific all-configuration obstruction is supporting work; no
worldwide novelty or substantial-result nomination is asserted. Its value
is to reject a real cover-preserving operation with explicit hypotheses,
rather than declaring arbitrary pair-color choices a valid linearization.
