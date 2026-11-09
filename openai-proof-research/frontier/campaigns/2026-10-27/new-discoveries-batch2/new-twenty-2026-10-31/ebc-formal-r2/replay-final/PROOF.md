# Proof

The endpoint is `EBC337062.conjecture21_false_unconditional : ¬ Conjecture21`.
It has no remaining bridge hypotheses.

## General BFS correctness

BFSGeneral.lean works for any finite simple graph with decidable equality and
adjacency. For a target t, natural labels d satisfy: d a = 0 iff a = t;
d a ≤ d b + 1 on every edge; every a ≠ t has an adjacent predecessor b
with d b + 1 = d a. Induction constructs an a-t walk of length d a.
Induction on an arbitrary walk bounds d a by its length plus the terminal
label. Applying that bound to a minimum walk proves dist a t = d a.

`walk_count_succ` counts walks of length n+1 by the first edge. The sets for
distinct first neighbours are disjoint, since the second vertex identifies
the neighbour. A walk shorter than its label cannot exist. Strong induction
on the label therefore proves `sigma_eq_of_bfs`: c t = 1 and the local
predecessor sum determine the literal shortest-path count c a.
`shortestPaths_eq` from round 1 supplies the path/walk bridge.

BFSRecurrence.lean also proves sigma symmetry by walk reversal and proves the
general first-edge and last-edge shortest-path recursions for connected graphs.
It retains the literal invariant throughout; sigma_self proves sigma a a = 1.

BFSTable.lean checks the zero-label, edge inequality, predecessor, diagonal
count and neighbour-count equations for EVERY ordered pair of ZMod 32 vertices.
These are kernel `decide` proofs of finite local certificates, without enumerating
walk objects. The general correctness theorems then give g32_dist_table and
g32_sigma_table. Round2Endpoint.lean combines them into DistanceAndCounts.

## General path splitting

Splitting.lean applies to any finite simple graph with decidable equality and
adjacency, connected for the orientation-disjointness step. Oriented paths
are minimum-length walks containing the one-edge walk u→v as a subwalk.
Every such walk is p ++ (u→v) ++ q. Minimum subwalks have minimum length,
so p and q have lengths dist x u and dist v y; their lengths force
`dist x u + 1 + dist v y = dist x y`.

If that equality holds, concatenation is a bijection from pairs of shortest
x-u and v-y walks onto these oriented paths. Concatenation has minimum length,
so is a path by the existing minimum-walk theorem. Injectivity follows by
splitting the dart lists at the common prefix length; surjectivity follows
from the subwalk witness and minimum-subwalk lengths. This bijection is
implemented directly by Finset.card_bij in orientedPaths_card. If the distance
equality fails the oriented-path set is empty.

The two oriented sets are disjoint. Were both orientations present, their
two distance equalities, combined with the triangle inequalities through u
and v, would force each terminal distance to exceed the other. An unordered
edge occurs exactly when one of its oriented one-edge walks is a subwalk.
Taking the disjoint union proves sigmaEdge_split, with exactly the two products
in PathSplitting32. The theorem even holds for x = y.

## Endpoint

The BFS predecessor certificate also proves G32 connected. The general split
theorem therefore proves PathSplitting32. Applying the unchanged round-1
conjecture21_false theorem to the two now-proved Props yields the unconditional
endpoint. The unchanged exact rational arithmetic, ordered-pair reindexing,
Class 4 n=1 instantiation and C_2 controls are all replayed.

This is a formalization result only. It does not resolve the independent
prior-art/credit question, which remains for root.
