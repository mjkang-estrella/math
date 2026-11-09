# Held ordinary endpoint: MathDB 376322

Status: complete ordinary combinatorial argument proposed; NOT independently reviewed, NOT novelty/significance cleared, NOT Lean checked, credit 0. Root must adjudicate the older compound-graph subsumption gap before authorizing Pi. No formal execution took place.

## Exact statement and primary reconciliation

For positive hypercube dimension n and positive k, if Q_n has k completely independent spanning trees, then F_{n+1} has k completely independent spanning trees. This is the full implication in reservation 376322, not just the previously known k=2 case. The literal record is preserved in provenance/376322.raw.jsonl; full statement/provenance are in provenance.json.

Primary: Lalou–Mbarek–Skender–Togni, https://arxiv.org/html/2607.25917 (v2, September 21, 2026), Section 2 definitions, Theorem 1, Theorem 2 and proof, Section 4.2 compatible-port graph, concluding Conjecture 1. The same target and Theorem 2 proof were read in https://arxiv.org/html/2607.25917v1. The printed Figure 4 port interpretation and formula were read as HTML text; figure images were not inspected. No computational example is needed below.

The record's reference “this conjecture was later disproved” concerns Hasunuma's general connectivity conjecture in the introduction, NOT this lifting conjecture. We do not claim credit for correcting that routing error. No journal reference appears on the current arXiv abstract page. Search surfaced Togni's publications page listing this as submitted; direct retrieval failed hostname certificate verification, without retry or TLS changes. Consequently latest journal/corrections clearance remains bounded, not complete.

Relevant companion https://arxiv.org/html/2608.00900 was read in its definitions, complete printed construction/proof discussion, and concluding remarks. It proves the separate F_4 two-tree endpoint by a printed cubic partition and externally verified finite checks. Those checks were NOT run here. Its remark explicitly raises Qin–Hao–Chang's compound-graph paper (IEEE TPDS 31 (2020), 201–210, DOI 10.1109/TPDS.2019.2931904); that full theorem remains unread. Its possible all-k subsumption is a material hold, not clearance. The companion leaves higher-k dual-cube questions open, which is routing evidence only.

## Semantic model

Let A=(F_2)^n, written additively with addition XOR. Model the dual-cube by triples (b,x,y), b in {0,1}, x,y in A. For b=0, x is cluster label and y the local coordinate; for b=1, y is cluster label and x the local coordinate. Internal edges change exactly one bit of y when b=0, or of x when b=1. Cross-edges join (0,x,y) to (1,x,y). Thus clusters are L_x={(0,x,y):y in A} and R_y={(1,x,y):x in A}. This is exactly the source's 2n+1 bit definition for F_{n+1}, with bit blocks explicitly identified; no graph proxy is substituted.

CIST means spanning trees such that for every pair of distinct endpoints their unique tree paths are pairwise edge-disjoint and have no common vertex except the endpoints. An internal vertex has tree degree at least 2.

## Preliminary tree facts, with proofs

In a tree on at least three vertices the internal set S is nonempty, connected in the tree, and dominating. Any interior vertex on the unique path between two internal vertices is internal, proving connectedness. Every leaf has an internal neighbor: two adjacent leaves would form an entire two-vertex connected component. These facts also show that all vertices outside S have degree one and attach to S.

CIST trees are edge-disjoint: an edge shared by two trees gives the same one-edge path between its ends. They have disjoint internal sets. To prove the latter directly, suppose v is internal in two trees. Deleting v gives two partitions of V minus {v}, each having at least two parts. There exist x,y in different parts of both partitions: start with x,y in different parts of the first; if they are in one part of the second, choose z outside that second part. Either x,z or y,z are separated in the first as well. The two corresponding paths then both have v as an interior vertex, contradiction. Conversely, edge-disjoint trees with disjoint internal sets are CIST: any shared nonendpoint on two simple paths would have degree at least two in both trees. This proves the entire required semantic bridge, rather than assuming its formal availability.

## Coordinate lemma

Suppose k>=2 CIST T_i exist in Q_n. The n=1 graph has only one edge, so this case cannot occur; hence |A|>=4. Fix i and put S_i=Int(T_i). For every coordinate j there is a j-direction hypercube edge with both ends in S_i.

If there were no such edge, connectedness of T_i[S_i] would imply all elements of S_i have the same jth bit c: a path in Q_n can change that bit only along a j-edge. Thus S_i lies in the coordinate half H={a:a_j=c}. For every z outside H, domination by S_i forces its unique neighbor in H, z+e_j, to lie in S_i. Consequently S_i=H. Every z outside H is a leaf of T_i, its neighbor is internal, and its unique available neighbor in H is z+e_j. T_i therefore uses every edge of the j-direction perfect matching.

Choose h!=i. Internal disjointness gives S_h subset A minus H. Again, domination forces S_h=A minus H, and every vertex of H is a leaf of T_h attached across the same j-direction perfect matching. This contradicts edge-disjointness. The coordinate lemma follows. In particular, for every j there are s_j,t_j in S_i with s_j+t_j=e_j.

## Compatible quotient graphs are connected

For each i define a bipartite simple graph H_i on {0,1} x A by
  (0,x) adjacent to (1,y) iff x+y is in S_i.
For any x and coordinate j the two-edge walk
  (0,x), (1,x+s_j), (0,x+s_j+t_j)=(0,x+e_j)
lies in H_i. Flipping the finitely many coordinates in which x and x' differ connects all vertices of the left class. S_i is nonempty; fix s in S_i. Every right vertex (1,y) is adjacent to (0,y+s), so H_i is connected. This is an exact symbolic path proof, not an enumerated search. Choose any spanning tree B_i of H_i; finite connected graphs have a spanning tree, e.g. by deleting edges of cycles until none remain. Since the S_i are disjoint, the H_i (and therefore B_i) have pairwise disjoint edge sets.

## Lift the original trees and glue

In cluster L_x, use the translated copy of T_i under a -> (0,x,a+x). In cluster R_y, use the translated copy under a -> (1,a+y,y). Translation preserves Q_n adjacency. Each vertex (b,x,y) is internal in this local tree precisely when x+y is in S_i, independently of b.

For each quotient edge {(0,x),(1,y)} of B_i add the actual cross-edge {(0,x,y),(1,x,y)}. Both its endpoints are already internal in the corresponding local T_i copies. Let U_i be the union of all these local tree edges and selected cross-edges.

U_i spans every vertex. It is connected: lift a B_i path between clusters, using each cluster's connected local tree to join successive cross-edge endpoints. It is acyclic: deleting any selected cross-edge splits B_i into two cluster sets, and that cross-edge is the only U_i edge between those sets, so it is a bridge. A cycle cannot contain a cross-edge, while a cycle contained in one cluster contradicts the local tree property. Thus U_i is a spanning tree.

The U_i are pairwise edge-disjoint. Within a cluster this follows from the original T_i after a common translation; different clusters have disjoint local edges. Selected cross-edges are disjoint because B_i are disjoint, and a cross-edge is never a local edge. Their internal sets are also disjoint: added cross-edges only touch vertices already internal locally, so Int(U_i) is exactly {(b,x,y):x+y in S_i}. Disjointness of the S_i proves the claim. By the proved semantic bridge the U_i are k CIST in F_{n+1}. This proves the full implication for k>=2.

For k=1, F_{n+1} is connected: its clusters are copies of the connected Q_n and every left cluster has a cross-edge to every right cluster. A spanning tree exists by the finite cycle-deletion argument. This completes all positive k. The source works with positive dimensions. If a formal endpoint includes n=0, root must settle the degenerate definition of a family of repeated empty trees on Q_0; do not silently assert that convention. Standard set-of-k-distinct-trees avoids repetition; an indexed family without distinctness needs an explicit positive-dimension hypothesis matching the source.

## Failed approaches and significance boundary

Merely choosing edge-disjoint spanning trees of K_{2^n,2^n} fails because their ports may be leaves in the wrong local trees. Using identical unshifted copies of T_i in every cluster also fails: only a rectangle indexed by S_i can be connected through fully internal ports. The cluster-label XOR translation is what makes all clusters participate. The coordinate lemma is necessary to establish connectivity of this compatible-port graph; nonemptiness of S_i alone would not suffice.

The source already glues local trees through compatible internal ports, and Section 4.2 already defines the compatible-port graph for two trees. That gluing argument is credited, not a new contribution. The proposed addition is a uniform all-k alignment and the coordinate lemma proving its compatible-port graphs connected for arbitrary supplied CISTs. Whether that addition is already a complete classical/compound-graph corollary requires independent review. Ease alone is neither acceptance nor exclusion. No new diameter bound or new Q_n existence theorem is asserted.

## Dormant actual semantic Pi plan — no execution authorized

If root first clears source/scope, novelty and significance, route implementation only to Pi spark/GLM-5.3-Flash-EXL3, high thinking, in a separately authorized lane. Do not execute this plan now.

Use finite vertices A=Fin n -> ZMod 2 (or Bool with proved XOR-group equivalence). Define Q_n as the simple graph differing in exactly one coordinate. Define D_n on Bool x A x A by the three edge clauses above, and prove its bit-block equivalence to source F_{n+1}. Define a spanning tree as a spanning SimpleGraph subgraph with IsTree; define CIST literally using unique simple paths and pairwise edge/nonendpoint-vertex disjointness. Prove equivalence to edge-disjointness plus disjoint degree>=2 sets, including the two-partition lemma above. A theorem about disjoint connected sets alone is not the endpoint.

Prove sequentially: internal-set connected/dominating; singleton/two-vertex exclusions for k>=2; missing-coordinate implies full half cube; all matching edges forced; coordinate-edge existence; connectivity of H_i by explicit two-step walks; finite spanning-tree existence; translation adjacency and internal-degree preservation; cluster gluing connected and acyclic; exact lifted internal sets; CIST path semantics. Conclude forall positive n,k, HasKCIST (cube n) k -> HasKCIST (dualCube (n+1)) k. Preserve source definitions, quantifiers and dimension convention in a separate fidelity statement.

This is a uniform proof, so no giant numerical certificate or Boolean enumeration is needed. Root should pin Lean/mathlib only after authorization. Initial bounded implementation budget: one 120s CPU / 140s wall process at a time, two CPUs, <=6GiB AS; persist partial lemmas and report any unpaid bridge rather than claiming completion. Expected engineering is substantial finite graph/tree API work; no credible declaration count or completion-time estimate is asserted without inspection. Audit the eventual transitive #print axioms to allow only propext, Classical.choice, Quot.sound. No sorry/admit/new axiom/unsafe/native_decide. Root's separate independent ordinary review, statement review, literature/significance adjudication and extracted replay are mandatory before credit.
