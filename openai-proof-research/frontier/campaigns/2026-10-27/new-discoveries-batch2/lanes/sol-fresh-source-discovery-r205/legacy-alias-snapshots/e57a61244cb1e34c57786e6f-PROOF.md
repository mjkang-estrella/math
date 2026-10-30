# A full ordinary refutation of the connected edge-irregulator conjecture

Status: complete ordinary proof; eligibility/current-priority HOLD; not accepted,
not independently reviewed, no Lean certificate, lane credit 0.

## Actual source

Bensmail, Catherinot, Fioravantes, Marcille and Oijid, *Graph Irregularity via
Edge Deletions*, WALCOM 2026, pp.353–367, DOI
https://doi.org/10.1007/978-981-95-7127-7_24, Conjecture 1, printed p.4.
The author-deposited conference manuscript at
https://hal.science/hal-05548898v1/document (HAL deposit12Mar2026) was read,
including a visual check of physical PDF p.5. The same conjecture occurs in
arXiv:2511.14514v1 (18Nov2025), Section2. Both quantify over every connected
finite simple graph G, with no regularity or minimum-degree assumption.

For a graph G, an edge-irregulator is S subset E(G) such that each retained
edge uv has d_(G-S)(u) != d_(G-S)(v). Degrees are recomputed after deletion.
Write I_e(G) for the minimum cardinality of such S. The source conjectures
an absolute real constant c>=1 with I_e(G)<=|E(G)|/3+c for all connected G.

## Construction

For each integer t>=2, let G_t have vertices h and, for every 1<=i<=t,
six distinct private vertices a_i,b_i,c_i,d_i,x_i,y_i. Its edges, and no others,
are for each i

    a_i b_i, a_i c_i, a_i d_i, b_i c_i, b_i d_i,
    c_i x_i, x_i y_i, y_i h.

Thus each block is a diamond K4 minus c_i d_i, joined at c_i to h by a
three-edge path. The graph is finite, simple and connected; it has 6t+1
vertices and 8t edges. The eight-edge blocks partition its edge set, even
though they share vertex h.

**Theorem.** For every integer t>=2, I_e(G_t)=3t.

## Lower bound, valid against every deletion set

Let S be any edge-irregulator and fix block i; suppress subscripts. We first
prove that S deletes at least two of its five diamond edges. The only edge
from a diamond vertex to its exterior is cx. Let epsilon be 1 if cx is
retained and 0 otherwise. The degrees of a,b,d depend only on the retained
diamond edges, while c has its retained diamond degree plus epsilon.

If no diamond edge is deleted, a and b each have degree3 and retained edge
ab is a conflict. If exactly one diamond edge is deleted, exhaust the
following three cases, using the automorphism exchanging a and b:

* Deleted ab: a,b,d all have degree2. Retained ad is a conflict.
* Deleted ad (or bd by symmetry): a has degree2, b has degree3 and c has
  degree2+epsilon. If epsilon=0, retained ac has equal endpoint degrees2;
  if epsilon=1, retained bc has equal endpoint degrees3.
* Deleted ac (or bc by symmetry): a and d each have degree2, so retained
  ad is a conflict.

Every case contradicts local irregularity. Thus at least two diamond edges
are in S, regardless of all choices outside this diamond.

Independently, at least one of cx,xy,yh belongs to S. Otherwise x and y each
have degree2 and retained xy is a conflict. This conclusion does not depend
on the degree of h or on diamond deletions.

The diamond edges and its three path edges are disjoint. Hence S contains
at least three edges from each block. Since the block edge sets partition
E(G_t), |S|>=3t. This applies to every edge-irregulator S.

## Matching upper bound

Delete exactly ab,ad,xy from every block. The remaining degrees in every
block are

    d(a)=1, d(b)=2, d(c)=3, d(d)=1, d(x)=1, d(y)=1,
    d(h)=t.

The five retained edges in each block are ac,bc,bd,cx,yh. Their degree
pairs are respectively (1,3),(2,3),(2,1),(3,1),(1,t). All pairs have
unequal entries because t>=2. The retained graph is therefore locally
irregular and exactly 3t edges have been deleted. This proves equality.

## Full source quantifier is contradicted

For any proposed real constant c>=1, choose an integer t>3c (hence t>=2).
Then

    I_e(G_t)-|E(G_t)|/3 = 3t-8t/3 = t/3 > c.

Consequently no absolute c in Conjecture1 exists. This is a connected
infinite-family refutation, rather than a fixed-instance violation of a
particular guessed value of c. No computational premise enters the proof.

## Adversarial points

The upper-degree list was corrected while drafting: x has degree1 after
xy is deleted; using degree2 there would be an error. The independent
literal construction checker confirms the displayed degree pairs. The lower
bound depends on final degrees, handles both choices of cx, and makes no
assumption about h. The proof does not use the invalid principle that an
induced bad subgraph must remain bad after exterior edges are added.

No current-head registry clearance, absolute priority, formal verification,
or independent mathematical review is claimed. Eligibility is separate from
the complete ordinary mathematical refutation above.
