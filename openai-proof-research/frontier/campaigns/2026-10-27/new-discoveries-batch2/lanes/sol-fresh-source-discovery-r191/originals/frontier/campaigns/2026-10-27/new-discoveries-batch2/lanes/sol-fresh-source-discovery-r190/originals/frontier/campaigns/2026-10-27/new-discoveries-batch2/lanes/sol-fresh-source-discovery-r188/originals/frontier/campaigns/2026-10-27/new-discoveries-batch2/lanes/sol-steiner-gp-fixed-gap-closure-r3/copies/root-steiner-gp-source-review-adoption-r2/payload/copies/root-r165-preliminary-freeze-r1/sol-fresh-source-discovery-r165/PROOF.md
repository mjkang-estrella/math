# Ordinary proofs; substantive eligibility not cleared

These are complete ordinary finite-graph arguments. They are not certificates of
novelty or qualifying discoveries. Both are recommended for routine-source
exclusion; no Lean or manuscript investment is requested.

## Monotonicity: the explicit graph

Let F have distinguished vertices w,a,b,c. Join w to each of a,b,c by a path
of length two, and join each pair among a,b,c by a path of length three.
All nine internal vertices of these six paths are distinct. Thus |F|=13.
This is exactly the k=3 graph of the published source Proposition 2.4.

For an integer m>=1, replace each of w,a,b,c by an independent class of m
false twins W,A,B,C. Keep each internal vertex as a singleton. For every
edge of F put all edges between its two replacement classes, and no others.
Call the resulting finite simple connected graph F_m. Its order is 4m+9.

Claim: gp(F_m)>=4m and sgp_3(F_m)<=3m+9. Consequently for m>=10,
sgp_2(F_m)>sgp_3(F_m).

Proof of the first bound. Between different replacement classes, distances
are the corresponding distances in F. A base shortest path lifts to a path
with any specified endpoints. Conversely, projecting any path produces a
walk of the same length in F, so it cannot improve distance. In F the three
rim-pair distances are 3 and each center-rim distance is 2. Two distinct
vertices of the same distinguished class have distance 2, since they are
nonadjacent and have a common neighbor. Every triple in W union A union B
union C therefore satisfies all strict triangle inequalities: triples in
three classes have side lengths (3,3,3) or (2,2,3); triples in one or two
classes have lengths (2,2,2), (2,2,2), or (2,3,3).
Thus no selected vertex lies on any shortest path between two others.
The union is a genuine general-position set of cardinality 4m.

Proof of the second bound. First the Steiner distance of {a,b,c} in F is 6.
Indeed a minimum tree has no nonterminal leaf. Every internal degree-two
vertex of one of the six subdivided edges is consequently either absent or
part of the entire path between its distinguished endpoints. Suppress those
paths: a tree avoiding w uses at least two rim edges, of weight 3 each; a
tree using w spans all four distinguished vertices and has at least three
edges, each of weight at least 2. The three spokes attain 6.

Take any a' in A, b' in B, c' in C, and w' in W. Their three length-two
spokes through w' form a tree with six edges. It is a Steiner tree: the
projection of any connected subgraph containing a',b',c' is a connected
subgraph of F containing a,b,c, with no more distinct edges than the original
subgraph. It therefore has at least six edges. The six-edge tree contains
w', which is not one of its three terminals.

It follows that a 3-Steiner general-position set cannot meet all four
classes W,A,B,C. It contains at most 3m distinguished-class vertices and at
most the nine remaining vertices, proving the asserted upper bound.
At m=10 we have gp(F_10)>=40>39>=sgp_3(F_10), on 49 vertices.

The source restricts k to 2<=k<=n-1. The example is within that range.
Its sequence also cannot be nonincreasing: sgp_40(F_10)>=40, since every
40-element set is vacuously 40-Steiner general position, whereas sgp_3<=39.
Thus this same graph has a sequence which is neither nondecreasing nor
nonincreasing over the source's k-range. This addresses universal
monotonicity; it does not classify graphs with monotone sequences.

## Lexicographic sharpness: a direct source bridge

Let X=P_3 composed with K_2, let k=4. The two outer layers together induce
two disjoint edges, and the middle layer is adjacent to all outer vertices.
Theorem 5.2 gives 2*sgp_[2:3](P_3)=4, because every two-element set qualifies
for both parameters and the entire P_3 fails the parameter-2 condition.

Delete one outer vertex and call the remaining five-element set S. Every
four-element subset B of S contains a middle vertex and hence is connected.
Its Steiner distance is |B|-1=3, and every Steiner B-tree has precisely the
four terminal vertices. Hence S is 4-Steiner general position. On the other
hand all six vertices do not qualify: the four outer vertices are disconnected,
and each minimum tree joining them uses a middle vertex. Therefore
sgp_4(P_3 composed with K_2)=5>4, disproving universal sharpness in Problem 7.3.

## Eligibility objection

The first proof takes the source's explicit set-level obstruction, applies
the elementary false-twin blow-up and the projection bound, and overwhelms
the fixed auxiliary-vertex budget. The second uses the source bound and a
five-element connected-subset check. These are complete source-adaptation
bridges, not exclusions inferred from shortness. Under the assigned standard
excluding routine classical/source adaptation, both are recommended for
zero credit. This recommendation is not an independent review or a claim
that an earlier exact public proof has been found.
