# Operation comparison for the family 089 screen

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

This is a bounded pre-freeze screen, not a contribution review or an
assertion of worldwide novelty.

The pinned planar theorem supplies constant L1 distortion for every finite
connected planar graph with arbitrary positive edge lengths. Its
`consequences.tex` already invokes Lee--Sidiropoulos Theorem 1.7 together
with the bounded-treewidth companion to cover fixed almost-embeddable
classes. Those consequences are antecedents, not available nominations.

The bounded-treewidth companion's `02-cut-laws.tex` constructs a Markov
gluing of consistent symmetric bag measures. Proposition
`prop:uncertainty` transports a dominated reserved submeasure along a bag
path using symmetric finite-state Markov flow. Its proof inserts a full
testing-bag assignment layer; the number of states is at most 2^k.
The cardinality bottleneck in that proof is distinct from construction
of the measures to be transported.

`03-particles.tex`, Lemmas `lem:trace-update` and `lem:particle-bounds`,
supplies two operations jointly: affine threshold-cut traces on a common
weak-order cone, and a signed subset-sum invariant under paired averaging
with opposite perturbations. Proposition `prop:particle-realization`
uses N=2q+k!+2 to find an unreserved common-order pair. Those are the
actual source operations, not consequences of the theorem title. The
obstructions in `interface-obstructions.md` explain why replacing k by
the interface size or replacing real particles by arbitrary L1-valued
particles has not transferred those operations.

The closest external primary body read was James R. Lee and Anastasios
Sidiropoulos, *On the geometry of graphs with a forbidden minor* (STOC
2009), [author PDF](https://people.csail.mit.edu/tasos/papers/geoforbid_stoc2009.pdf).
Retained extracted lines 100--250 state the structural context, clique-sum
closure conjecture and one-sum closure. Lines 590--752 include the entire
random-retraction proof (Theorem 3.4) and peeling proof (Lemma 3.5), plus
the adjacent apex argument.

The retraction proof uses dyadic Lipschitz partitions and one random
scale offset, obtaining a 5-local retraction whose separation probability
is bounded by (beta+2)d(x,y)/min(d(x,A),d(y,A)). The peeling proof makes
one copy of G[V\A union {a}] per a in A and attaches each copy to G[A]
at a single vertex. The pair either stays in the same copy, at no cost
in the relevant case, or pays an excursion of order d(x,A). Multiplying
that excursion by the displayed separation probability yields an
O(beta*dilation(A)) expected bound. This is a one-sum reduction with
specified geometry, not a theorem gluing arbitrary multi-vertex cut laws.
Repeatedly applying its fixed factor does not yield a depth-independent
bound. No new amortization argument was supplied here.

The primary introduction explicitly separates arbitrary clique-sum
closure from its almost-embeddable reduction. Its stochastic-embedding
obstruction also cautions against treating a general clique-sum family
as uniformly stochastically planar merely because each constituent is
planar. The screen therefore cannot obtain a new result by renaming
peeling or invoking an unproved closure theorem.

Lee--Poore's 2013 publication listing/abstract on constrained embeddings
and two-sums was located, but the publisher PDF request returned 403.
No proof-body reading or operation-level conclusion from that paper is
claimed. Other search-only papers are listed in `source-reading.md` and
are not mathematical premises. No absence of a search hit is evidence
that the desired new mechanism is novel.
