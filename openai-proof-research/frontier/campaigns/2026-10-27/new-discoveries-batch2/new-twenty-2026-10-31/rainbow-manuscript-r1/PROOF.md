# Proof dossier for MathDB 346167

DRAFT; zero accepted credit. See manuscript.md for bibliography and formal trust limits.

## 1. Definitions and the target

All graphs here are finite, simple and undirected. Let x and y be distinct vertices of a connected vertex-colored graph K. If xy is absent, an x–y vertex-cut is a set S such that x and y belong to different components of K − S. If xy is present, they must instead belong to different components of (K − xy) − S. In either case S excludes x and y. A set is rainbow when its vertices have pairwise distinct colors.

An x–y rainbow vertex-cut is such a cut S with the following additional condition: for a nonedge xy, S is rainbow; for an edge xy, S + x or S + y is rainbow, where S + x denotes S ∪ {x}. The disjunction matters. A coloring is a rainbow vertex-disconnection coloring if every distinct pair has such a cut. The minimum number of colors in such a coloring is rvd(K). Proper coloring is not required. These are the source definitions [1, Section 1].

Li and Weng state the following (the overbar denotes complement):

“Let G and Ḡ be nontrivial connected graphs of order n ≥ 8. Then rvd(G) + rvd(Ḡ) ≥ n.”

This is [1, v2, Conjecture 6.12, p. 18], identically numbered 5.12 in v1. Immediately before it, the authors suggest improving their lower bound further, and note that when rvd(G) = 1, Lemma 6.6 gives the conjectured sum bound for n ≥ 8. Their Theorem 6.11 proves n − 5 ≤ rvd(G) + rvd(Ḡ) ≤ 2n for n ≥ 24, with sharp upper bound. The example here does not contradict that theorem or the rvd = 1 remark.

Theorem. The graph G specified in Section 2 and its complement H satisfy all the hypotheses at n = 8, but their rainbow vertex-disconnection numbers sum to 7.


## 2. The graphs, colorings and exact lower bounds

Use the vertex set {0,1,2,3,4,5,6,7}. The following complete neighborhood lists specify both graphs. Their adjacency masks are respectively (202,225,232,149,232,22,23,31) and (52,28,19,98,7,201,168,96), with bit j of mask i recording adjacency ij. The columns c and d are the proposed colorings of G and H.

| Vertex | Neighbors in G | Neighbors in H | c | d |
| 0 | 1,3,6,7 | 2,4,5 | 0 | 0 |
| 1 | 0,5,6,7 | 2,3,4 | 1 | 1 |
| 2 | 3,5,6,7 | 0,1,4 | 2 | 0 |
| 3 | 0,2,4,7 | 1,5,6 | 2 | 1 |
| 4 | 3,5,6,7 | 0,1,2 | 3 | 2 |
| 5 | 1,2,4 | 0,3,6,7 | 0 | 0 |
| 6 | 0,1,2,4 | 3,5,7 | 3 | 2 |
| 7 | 0,1,2,3,4 | 5,6 | 1 | 0 |

The lists are symmetric, loopless and complementary. In G, vertices 1,3,6,7 are adjacent to 0; vertices 2,4,5 are reached from 0 through 3,3,1 respectively. In H, vertices 2,4,5 are adjacent to 0; vertices 1,3,6,7 are reached through 2,5,5,5 respectively. Hence both graphs are connected and nontrivial. They have 16 and 12 edges, and minimum degrees 3 and 2.

Lemma 1. If vertices u and v have two distinct common neighbors a,b in a graph K, every rainbow vertex-disconnection coloring gives u and v different colors.

Proof. Any a–b cut must contain u and v, since the length-two paths a,u,b and a,v,b survive deletion of ab. Its rainbow requirement, including in the adjacent case, forces distinct colors on u and v. This uses a,b distinct from u,v, as the graph is loopless.

In G, the vertices {0,1,2,4} must therefore have four different colors. The six pairs have the following common-neighbor witnesses: (0,1): {6,7}; (0,2): {3,6}; (0,4): {3,6}; (1,2): {5,6}; (1,4): {5,6}; (2,4): {3,5}. Thus rvd(G) ≥ 4.

In H, the adjacent vertices 0 and 2 have two internally vertex-disjoint paths after deleting edge 02: 0,4,2 and 0,5,3,1,2. Any 0–2 cut in H − 02 must meet both disjoint interior sets, so it has at least two vertices. Since 02 is an edge, adjoining 0 or 2 must make a rainbow set of at least three vertices. Thus rvd(H) ≥ 3.

Section 3 proves that c and d are admissible with four and three colors. Together these arguments establish the exact values and the theorem. The lower-bound arguments are ordinary proofs supplied here; equality is not claimed as an additional Lean endpoint in the reused packet.


## 3. Complete cut certificates for the upper bounds

A decimal mask M denotes {v : bit v of M is 1}. For each unordered pair x < y the table supplies a cut S and a side A containing x and excluding y. All entries are literal finite data; no search is needed to use them.

| x,y | G: S | G: A | H: S | H: A |
| 0,1 | 200 | 1 | 28 | 225 |
| 0,2 | 232 | 3 | 18 | 233 |
| 0,3 | 148 | 99 | 34 | 21 |
| 0,4 | 232 | 3 | 6 | 233 |
| 0,5 | 22 | 201 | 2 | 21 |
| 0,6 | 22 | 137 | 34 | 21 |
| 0,7 | 74 | 1 | 34 | 21 |
| 1,2 | 232 | 3 | 17 | 234 |
| 1,3 | 149 | 98 | 1 | 22 |
| 1,4 | 232 | 3 | 12 | 2 |
| 1,5 | 20 | 203 | 9 | 22 |
| 1,6 | 21 | 170 | 9 | 22 |
| 1,7 | 21 | 98 | 9 | 22 |
| 2,3 | 145 | 102 | 3 | 20 |
| 2,4 | 232 | 4 | 3 | 4 |
| 2,5 | 18 | 205 | 3 | 20 |
| 2,6 | 19 | 172 | 3 | 20 |
| 2,7 | 104 | 4 | 3 | 20 |
| 3,4 | 133 | 8 | 3 | 232 |
| 3,5 | 22 | 201 | 65 | 30 |
| 3,6 | 23 | 136 | 32 | 31 |
| 3,7 | 21 | 8 | 96 | 31 |
| 4,5 | 6 | 217 | 3 | 20 |
| 4,6 | 7 | 184 | 3 | 20 |
| 4,7 | 104 | 16 | 3 | 20 |
| 5,6 | 22 | 32 | 136 | 55 |
| 5,7 | 22 | 32 | 64 | 63 |
| 6,7 | 23 | 64 | 32 | 95 |

For each row, direct substitution into Section 2 verifies: (i) x,y ∉ S, x ∈ A and y ∉ A; (ii) the colors on S are distinct; (iii) if xy is an edge, at least one endpoint color is absent from S; (iv) every edge crossing from A to its complement, other than xy, has an endpoint in S. These four finite assertions, checked independently in scripts/check.py, are also sufficient as an ordinary proof: in (K − xy) − S a path starting at x cannot leave A, so it cannot reach y. For a nonedge, deleting xy has no effect. For an edge, (ii) and (iii) make S + x or S + y rainbow. The same S works for the reversed pair. Thus the 28 rows per graph cover all distinct pairs and prove rvd(G) ≤ 4 and rvd(H) ≤ 3.

For illustration, for (0,1) in G, S = {3,6,7}, A = {0}, and the only surviving edge out of 0 before deleting 01 is 01 itself. Its cut colors are {2,3,1}, avoiding c(0) = 0. In H, S = {2,3,4}, A = {0,5,6,7}; the colors on S are {0,1,2}, and 01 is a nonedge. The supplementary JSON retains the 112 ordered certificates used by Lean; the compact table uses just one orientation.



The source-only Lean endpoint proves the universal negation using upper bounds. The exact lower bounds above are ordinary proofs, independently consistent with the retained exhaustive partition checks.
