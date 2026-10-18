# Directed scale splitting: the surviving interface

This is author-side continuation work on the unchanged r33 question. No restricted result is substituted for the full target.

## Two-sided vertex expansion still gives a long directed cycle

Let 0<alpha<=1 and let H be a finite simple digraph of order u. Suppose every nonempty S with |S|<=u/2 has at least alpha|S| external out-neighbors and at least alpha|S| external in-neighbors. Put q=alpha²u/100, and suppose q>=1. Then H contains a directed simple cycle of length greater than q.

Proof. The expansion assumptions imply strong connectivity: a proper sink strongly connected component of order at mostu/2 contradicts out-expansion; if its order exceedsu/2, its nonempty complement has order at mostu/2 and has no external in-neighbor, contradicting in-expansion. A single-source directed DFS therefore explores all vertices without an empty stack before exploration is complete. At the time the finished and unexplored vertex sets have equal order t, the stack is a directed simple path P of order L=u−2t. No arc goes from a finished vertex to an unexplored vertex. If t>=u/3, the finished set's external out-neighbors all lie on P, so L>=alpha t>=alpha u/3. If t<u/3, then L>u/3>=alpha u/3.

Set j=floor q and split P in its forward order into X,J,Z, with |J|=j and the two outer segments as equal as possible. Since j+1<=2q<=alpha u/6<=L/2, both outer segments have at leastL/4 vertices. There is a directed path from Z to X avoiding J. Otherwise let R be the vertices reachable from Z in H−J. It containsZ, missesX, and has no outgoing neighbor outsideR∪J. If |R|<=u/2, out-expansion gives j>=alpha|R|>=alpha L/4. If |R|>u/2, put S=V(H)\(R∪J). Then X is contained inS, 0<|S|<u/2, and every external in-neighbor ofS is inJ, so again j>=alpha L/4. Either conclusion contradicts j<=q<alpha²u/12<=alpha L/4.

Choose a shortest Z-to-X path in H−J. Its interior missesX andZ, since otherwise it could be shortened. Thus it meetsP only at its endpoints z inZ and x inX. Together with the forward x-to-z segment ofP, it forms a directed simple cycle of length at leastj+2>q. ∎

This is the source181 DFS and bypass proof with the bypass direction reversed and with both expansion assumptions used explicitly. It is technical support, not a separately nominated theorem. It does not follow from only undirected expansion of the underlying graph.

## A one-sided neighborhood is not an undirected box boundary

The preceding lemma says that after deleting all sufficiently long directed cycles, every large current digraph has some small set with a small outgoing OR incoming external neighborhood. Source181's undirected scale split needs a small neighborhood containing ALL endpoints across the boundary. Equality of directed cut sizes does not give that vertex-set conclusion.

For an exact balanced example, take U={u_1,...,u_m}, R={r_1,...,r_m}, and a vertex b. Put the arcs u_i->b->r_i->u_i for each i. Optionally add all antiparallel pairs between distinct vertices ofU. The graph is simple and balanced in either case. For the setU, the external out-neighborhood is {b}, while the external in-neighborhood is all ofR. Thus replacing the source's undirected boundary by the small one-sided neighborhood loses m incoming arcs and m distinct outside endpoints. The example disproves that literal implication for the selected cut; it does not rule out another separator, another compression, or the full cycle target.

In the version without internal U-arcs, suppressing r_i gives a simple directed two-cycle on u_i,b, so even this obstruction can be repaired in that special example. It is not an impossibility theorem for compression.

## Why balancing expanders alone is insufficient

The local flow repair in balanced-reserves.md assumes both two-sided expansion and a SMALL pointwise imbalance. At an arbitrary source box boundary, defect can be as large as its internal degree; the parameter epsilon=k/h need not be at most1. The existing r33 four-class example P_t explicitly has imbalance t and guaranteed expansion only t/2. Neither independent random coloring nor the new flow lemma supplies an Eulerian completion inside such an arbitrary assigned piece.

Girão–Letzter's actual primary Lemmas2.2 and3.4 supply a different already-paid operation: an immersed subgraph of an Eulerian graph can be completed to an Eulerian MULTIDIGRAPH on the same branch vertices; applied to a selected undirected expander this retains directed expansion. The completion paths may share internal vertices, and the quotient may have parallel arcs. A directed simple cycle of that quotient can therefore lift to a closed directed trail with repeated vertices. Decomposing such a trail can produce many cycles; the needed one-cycle lifting or linear total surcharge is not in the cited statement.

## Remaining work

A complete proof still needs a joint directed box/path construction. The balance repair now permits Eulerian reserves with balanced complements at the source's dense polynomial scale. It does not bound the number of directed simple paths required to cover those complements, nor make arbitrary overlapping boxes balanced at total vertex cost (1+O(1/log D))n. Both operations must be paid before the source induction can be used. The full r33 target remains unresolved.
