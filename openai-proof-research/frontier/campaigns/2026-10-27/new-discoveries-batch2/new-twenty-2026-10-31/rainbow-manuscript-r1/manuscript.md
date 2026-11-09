# An eight-vertex counterexample to the rainbow vertex-disconnection sum conjecture

DRAFT • 3 November 2026 (America/Los_Angeles)

Prepared with AI assistance (OpenAI Codex). No human authorship or affiliation is asserted. This is an internal draft for root review; accepted campaign credit is zero. No priority claim is made.

## Abstract

We give an explicit connected graph G on eight vertices whose complement H is connected and for which rvd(G) = 4 and rvd(H) = 3. Thus rvd(G) + rvd(H) = 7 < 8, refuting the literal lower bound in Conjecture 6.12 of Li and Weng [1] (Conjecture 5.12 in version 1). Complete cut certificates prove the upper bounds, and short combinatorial arguments prove equality. A previously performed catalogue computation reports 74 failing order-eight isomorphism classes, and three checked one-vertex extensions fail at order nine. These computations support the example and earn no separate credit. The supplied Lean packet proves the literal negation; its prior audits are recorded, with a separate root replay status in the dossier. This is a modest finite refutation, not a replacement general bound.

## 1. Definitions and the target

All graphs here are finite, simple and undirected. Let x and y be distinct vertices of a connected vertex-colored graph K. If xy is absent, an x–y vertex-cut is a set S such that x and y belong to different components of K − S. If xy is present, they must instead belong to different components of (K − xy) − S. In either case S excludes x and y. A set is rainbow when its vertices have pairwise distinct colors.

An x–y rainbow vertex-cut is such a cut S with the following additional condition: for a nonedge xy, S is rainbow; for an edge xy, S + x or S + y is rainbow, where S + x denotes S ∪ {x}. The disjunction matters. A coloring is a rainbow vertex-disconnection coloring if every distinct pair has such a cut. The minimum number of colors in such a coloring is rvd(K). Proper coloring is not required. These are the source definitions [1, Section 1].

Li and Weng state the following (the overbar denotes complement):

“Let G and Ḡ be nontrivial connected graphs of order n ≥ 8. Then rvd(G) + rvd(Ḡ) ≥ n.”

This is [1, v2, Conjecture 6.12, p. 18], identically numbered 5.12 in v1. Immediately before it, the authors suggest improving their lower bound further, and note that when rvd(G) = 1, Lemma 6.6 gives the conjectured sum bound for n ≥ 8. Their Theorem 6.11 proves n − 5 ≤ rvd(G) + rvd(Ḡ) ≤ 2n for n ≥ 24, with sharp upper bound. The example here does not contradict that theorem or the rvd = 1 remark.

Theorem. The graph G specified in Section 2 and its complement H satisfy all the hypotheses at n = 8, but their rainbow vertex-disconnection numbers sum to 7.

<!-- pagebreak -->
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

<!-- pagebreak -->
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

<!-- pagebreak -->
## 4. Supporting finite computations

The independent review [5] enumerated all 4,140 partitions of eight vertices, with no conflict pruning, for each witness graph. Among partitions into 1,2,3 classes (respectively 1,127,966 partitions), G has no admissible coloring; it has two with four classes. H has none with one or two classes and 36 with three classes. These exact calculations agree with Section 2 but are unnecessary for the short lower-bound proofs.

The review also processed the public McKay order-eight catalogue [4]: 12,346 isomorphism classes, of which 9,888 have connected complements and are themselves connected. Exactly 74 fail the sum bound, with invariant pairs (3,4) or (4,3), forming 37 unordered complementary pairs. This is a catalogue-based exhaustive check, conditional on the catalogue's completeness; no independently certified isomorph-free generator was used. The statistic counts isomorphism classes, not labeled random graphs. The stored last index 12,314 is the last eligible graph, not an early cutoff; later disconnected entries were skipped.

For reproducibility, the review's exact procedure first enumerates every subset S excluding the endpoints and tests separation after deleting xy. Inclusion-minimal separating sets suffice because rainbow admissibility is inherited by subsets. It then enumerates color partitions as restricted-growth strings: c(0)=0 and 0 ≤ c(i) ≤ 1 + max{c(j):j<i}. For every pair it asks whether one separating set is rainbow and, for an edge, avoids at least one endpoint color. The first admissible class count is rvd. The broader sweep prunes pairs of equal-colored vertices with two common neighbors, which is sound by Lemma 1; the separate 4,140-partition calculation does not prune.

All 256 possible neighborhoods of a new vertex 8 attached to G were checked; 254 extensions had both graphs connected. The following three failed, each with exact pair (4,4). In every row the extension of c is (0,1,2,2,3,0,3,1,0); the second column gives a four-coloring of the complement.

| Neighbors of 8 | Complement coloring, vertices 0 through 8 |
| 1,5 (mask 34) | 0,1,1,2,3,0,3,1,2 |
| 2,5 (mask 36) | 0,1,0,1,2,0,2,3,3 |
| 4,5 (mask 48) | 0,1,2,1,0,0,2,3,3 |

These give sums 8 < 9, so replacing the threshold 8 by 9 would still fail. The three are not asserted pairwise nonisomorphic. A check of all 512 extensions of the mask-34 graph to order ten found 510 eligible and no failures. This last statement is only about that extension family, not all order-ten graphs. Random sampling at orders nine and ten also found none and cannot support a universal theorem.

The dossier preserves the review's input catalogue, algorithms, outputs and logs. Its matrix verifier independently checked all supplied cuts and the six displayed order-nine colorings. The present lane independently verifies the main cut table and complement relation, and rechecks the extension colorings with all separating subsets. It does not repeat the full catalogue classification or run Lean.

<!-- pagebreak -->
## 5. Formal correspondence, audits and limitations

The byte-identical source packet has SHA-256 038c7acfb665189952f706cfdf65de6d9bc5dc16c4a7af70f3b0832ec4c86057. In Base.lean, G is the literal mask graph on Fin 8. cutGraph deletes edge xy and isolates S. Since the endpoints are outside S, this has the same endpoint reachability as vertex deletion. cert_sound proves the side-invariance argument along arbitrary mathlib walks; there is no bounded-path substitute. Sixteen row modules check finite CutCert facts by kernel decide; Certificates.lean assembles them, and Final.lean proves both connectivity statements and the sum contradiction.

Semantics.lean proves that distinct colors on S and absence of an endpoint color are equivalent to the source's rainbow extension clause. It identifies sourceRvd with the implementation invariant and proves the least-admissible-number characterization when a coloring exists, as it does here. The endpoint Rainbow.mathdb_346167_literal negates the universal assertion over n and simple graphs on Fin n with n ≥ 8 and both connectivity hypotheses. Any finite graph can be labeled this way; nontriviality follows from n ≥ 8. The formal endpoint proves the refutation from upper bounds, not the separate equalities or catalogue counts.

The original and independent review receipts report 20 strict module builds and 20 explicit-module checker runs, an axiom audit of 168 local declarations, and no unsafe, partial, implemented-by or extern flags. Allowed axioms were propext, Classical.choice and Quot.sound. They used Lean 4.34.1 and cached mathlib at d13f23b723b8a846827a245b89c10fc7d3f11612. Cached upstream dependencies were trusted; an upstream rebuild or independent cache validation is not claimed. This lane performs only safe extraction and byte checks. The separate root replay-result.json (4 November 2026 UTC) reports PASS: root’s own driver built and explicitly checked 21/21 modules including Audit, with peak RSS 3.46 GB, and independently rechecked the coloring certificates. Root’s metadata audit found 168 declarations and no prohibited flags; the literal endpoint has only the three allowed axioms. This is a supplied root receipt, not a replay performed by this manuscript lane. The accompanying registry refresh records bounded complete-subtree path screening and unrelated rainbow-connector hits. Root paper review and acceptance remain outstanding.

## 6. Related work and access limits

The introductory work [2] treats special families, connectivity and extremal edges. Weng [3] studies minor-free bounds and complexity. Its K4-minor-free bound does not immediately give this G: 16 > 2·8 − 3 edges rules out that minor-free class. Weng [6] treats bounds, products and complexity; the reviewed constructions did not supply this example. Neither witness has a leaf or is a tree. No matching refutation was identified in the accessible primary bodies described by [5].

The published 2021 source body and final 2024 journal body were NOT read. The arXiv source bodies, an author-hosted 2021 manuscript retaining the conjecture, the introductory paper and later accessible material were inspected in earlier lanes; all seven OpenAlex citing records were read or screened, not all seven journal bodies. Registry checks were bounded path screens, not universal theorem-body searches. No new live search is claimed here. Prior-art clearance is qualified and cannot establish priority. The independent review recommended HOLD on that gap; root explicitly overrode HOLD to permit packaging with the limitation. Root alone reads the paper and decides acceptance. This small, easily found finite refutation has modest significance; the correct general lower bound remains open in this dossier.

## References

[1] Xueliang Li and Yindi Weng, Further results on the rainbow vertex-disconnection of graphs. arXiv:2004.06285v2 (2020); v1 has Conjecture 5.12. Published in Bull. Malays. Math. Sci. Soc. 44 (2021), 3445–3460. DOI: 10.1007/s40840-021-01125-8 (metadata verified in retained OpenAlex record; journal body unread).

[2] Xuqing Bai, You Chen, Ping Li, Xueliang Li and Yindi Weng, The rainbow vertex-disconnection in graphs. arXiv:1812.10034v2 (2020).

[3] Yindi Weng, Some results on the rainbow vertex-disconnection colorings of graphs. arXiv:2307.03964 (2023); published in Graphs and Combinatorics 40, article 42 (2024), per retained metadata. Final journal body unread.

[4] Brendan D. McKay, Graphs catalogue, users.cecs.anu.edu.au/~bdm/data/graphs.html, graph8.g6. Downloaded copy and HTTP receipts retained in [5].

[5] Internal independent adversarial review, MathDB 346167, rainbow-review-r1, REVIEW.md and review.json (receipt dated 4 November 2026 UTC). Unpublished evidence; not an external priority source.

[6] Yindi Weng, Bounds and complexity results of rainbow vertex-disconnection colorings. AIMS Mathematics 10(3) (2025), 5960–5970. DOI: 10.3934/math.2025272 (verified in the retained paper).
