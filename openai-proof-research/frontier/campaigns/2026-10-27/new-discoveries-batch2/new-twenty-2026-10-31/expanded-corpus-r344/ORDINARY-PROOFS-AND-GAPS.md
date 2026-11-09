# Ordinary proof routes and exact gaps

This is discovery and ordinary reasoning only, GPT-6.1 Sol high/default. No mathematical enumeration, code-based witness testing, solver, CAS, Lean, children or execution delegation was used. The first two routes below reach the exact literal negation, but are ineligible because they reproduce public mathematics or an endpoint correction. The third was pursued into the actual published construction rather than stopped at an abstract. It is a public refutation, with the independent reconstruction limits explicitly retained.

## 376138: complete 36-vertex ordinary refutation, already in the source

Primary: Bai–Li–Park, arXiv:2607.18047v2, introduction, definition of second neighborhood and Remark 3.1, published on arXiv 24 July 2026. Version 1 (20 July) still proposes the conjecture. Both versions were retrieved; v1 statement and v2 construction/proof were read. The v2 source attributes the construction to David Dzitsoev and acknowledges use of GPT. No independent priority is claimed.

Let Q have vertices 0,...,5 and out-neighbor sets
0: {1,4,5}; 1: {3,4,5}; 2: {0,1,3}; 3: {0,4}; 4: {2,5}; 5: {2,3}.
This specifies exactly one direction for every pair, and no loops. Replace vertex i by an independent class C_i of size (7,3,11,3,9,3), respectively, and replace each arc i→j by all arcs C_i→C_j. The resulting D is a finite loopless oriented graph on 36 vertices.

For x in C_i, its out-neighborhood is the union of the classes indexed by Q's out-neighbors of i. The exact second out-neighborhood excludes x and the entire first out-neighborhood; no vertex of C_i can be reached in two steps, since that would require a 2-cycle in Q. Its class indices are, respectively, {2,3}, {0,2}, {4,5}, {1,2,5}, {0,1,3}, {0,1,4}. All these claims follow directly from the displayed arc sets, with all arcs between classes complete.

A complete matching would give distinct destinations to every tail in any subset S of the first neighborhood. The following S and possible destinations Z inside the exact second neighborhood violate this necessary injection condition:

* i=0: S=C_1∪C_4∪C_5, Z=C_2∪C_3, so |S|=15>14=|Z|.
* i=1: S=C_4∪C_5, Z=C_2, so 12>11.
* i=2: S=C_0∪C_1∪C_3, Z=C_4∪C_5, so 13>12.
* i=3: S=C_0, Z=C_1∪C_5, so 7>6.
* i=4: S=C_2∪C_5, Z=C_0∪C_1∪C_3, so 14>13.
* i=5: S=C_2, Z=C_0∪C_1, so 11>10.

For example, for i=1 the outgoing arcs from C_4∪C_5 lead only to C_2∪C_3∪C_5, and the latter two classes belong to x's first neighborhood. Thus only C_2 is available. The other five destination restrictions are obtained by the same explicit unions of the listed arc sets. This proves every vertex fails the matching property, and refutes the full literal universal assertion, not merely the minimum-degree or tournament special case. No Hall sufficiency or computer enumeration is needed.

Beyond the first shortcut: a minimum-out-degree choice or the feed vertex of a median order does not prove the statement; v2 Remarks 3.2–3.3 explain these failures. Merely proving |N++|≥|N+| also does not give a matching. The actual obstruction is a strict inequality on a subset of tails. Our proof supplies that missing semantic bridge. The same S obstruction survives replacing every independent C_i by a transitive tournament: the second neighborhood still has no vertices of C_i, and all newly added arcs lie within external first-neighborhood classes, so they cannot supply additional destinations in N++. This also explains the stronger source variant, but receives no extra credit.

Disposition: EXCLUDE_PUBLIC_EXACT_REFUTATION, credit 0. This is not excluded for its size, ease, or family membership. The complete published construction and the explicit bridge above settle the exact record before new investment. No CANDIDATE or Pi plan is warranted. No journal version was established by the bounded search; this does not weaken the already established public-source exclusion.

## 376333: full literal counterexample and full classical value

The assigned source, Montgomery arXiv:2607.26049v1 Conjecture 9.1, indeed prints n≥m≥3 without excluding (3,3). The corpus reproduces it. Set n=m=3, so its claimed value is 5. On vertices Z/5Z color {a,b} red when b−a=±1 and blue when b−a=±2. This defines every unordered edge in exactly one color. The red graph is the cycle 0,1,2,3,4,0; each vertex's two red neighbors are not red adjacent, so there is no red triangle. Multiplication by 2 modulo 5 sends red edges to blue edges; it is a permutation, so blue is another triangle-free 5-cycle. Thus K_5 avoids both required monochromatic triangles and R(C_3,K_3)>5.

For completeness, every coloring of K_6 has a monochromatic triangle: at a fixed vertex v, three of its five incident edges have the same color. If any pair of their other endpoints has that color, they form a triangle with v; otherwise the three endpoints form a triangle in the opposite color. Hence R(C_3,K_3)=6. The exact literal universal claim is false.

Beyond the first shortcut: this is not evidence against the corrected conjecture. Read the pinned OpenAI/math manuscript introduction at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, preprints/Cycle-clique-Ramsey-numbers-September-25-2026/build/sections/01-introduction.tex, theorem thm:main: it states the complete range with (3,3) excluded and states value 6 there. Its ordinary theorem is accepted as true under project instructions; its upstream proof was not audited. Renaming its cycle variable m to the record's n and clique variable n to the record's m covers every other pair. Thus the corrected full endpoint is already public too. The pinned scope document lean/docs/189.md matches. Current MathVet family 189 and challenge CycleCliqueRamsey explicitly record the exact finite simple graph semantics, the exception, and Comparator pass; this is a registry report, not our own replay.

Disposition: EXCLUDE_CLASSICAL_ENDPOINT_CORRECTION, credit 0, not a new theorem. SIAM's journal page returned 403 and was not retried; no journal-body clearance is claimed. The original 1978 and all companion proof bodies were not exhaustively audited. Neither limitation makes the explicit classical exception into eligible discovery.

## 361504: public full-scope construction, independent reconstruction limits

Read Aubian arXiv:2401.07776v1 Section 4, definitions 4.3, Lemmas 4.4–4.7, Theorem 4.8 and Figures 8–11 including the printed adjacency matrix and exclusion table. The later companion arXiv:2310.04265v2 Section 4.2 (Conjecture 4.3 and Remark 4.4) explicitly records the disproof. The source's abstract incorrectly says maximum over backedge orders; the definition and proof use the minimum. The record leaves its directed clique number implicit, so this distinction is material.

The public obstruction is the regular cyclic five-tournament R5 with arcs i→i+1,i+2 modulo 5. In the order 1,2,3,4,5 its backward edges are {1,4},{1,5},{2,5}, a path on {4,1,5,2} and an isolated vertex 3, hence a forest. The source constructs D_1=C3 and D_{k+1}=Pi(D_k), with directed clique number 2 and unbounded dichromatic number, all avoiding R5. For any proposed bound f, choose k with dichromatic number greater than f(2); D_k violates it. Since embeddings between tournaments of equal arc completeness are induced on the image, source subtournament avoidance is exactly the record's subgraph avoidance.

Sustained route: Pi(T) consists of left blocks A_i, a middle block B, and right blocks C_j, initially in forward block order, with an A_i–C_j arc reversed exactly when their bijective labels agree. Labels range over an odd set of size 2n−1 with all n-subsets represented as blocks. For an acyclic color class to meet every block it must hit every n-subset on both sides. Each set of chosen labels has size at least n (otherwise its complement contains an n-subset). The two chosen-label sets intersect; with a chosen middle vertex, this gives a directed triangle. Therefore an optimal acyclic coloring needs more colors than T. Cross-block backward edges cannot form a triangle because they only join left to right and within each block equality labels are injective; internal backedge graphs also have clique number 2. Consequently directed clique number stays 2.

Avoiding R5 is the essential additional step: clique number 2 alone does not imply R5-free. The source proves that any strong subtournament of D_k has a cut with four explicit label-equivalence and interval-path properties (Lemma 4.7). Its Figure 11 gives an obstruction for each of the nine possible clique-two orders of R5 with vertex 1 first and each of the five cut choices. Vertex transitivity normalizes the first vertex. This proves the required avoidance in the published proof. We read the actual matrix/order/table text, did not run its Python code, and did not independently execute or certify the exhaustive-order completeness. The source writes 2n+1 in the codomain of phi in Definition 4.3 while its cardinality and Lemma 4.5 use 2n−1; the coherent 2n−1 construction is described above. This local correction and table verification would need explicit independent handling for a fresh formalization, not a new discovery claim.

The corpus reference to Zykov is not the proof of this directed endpoint. Aubian's own Section 4 and the companion's Remark 4.4 are the relevant primary resolution. Disposition: EXCLUDE_PUBLIC_EXACT_REFUTATION; independent complete reconstruction/certificate not claimed, credit 0. No execution or dormant candidate plan is nominated.

## Other endpoint attempts

The exact remaining scopes and missing lemmas are in results.json. In particular, 371754 and 372142 are the same epsilon problem: an alpha≤2 solution implies the alpha=2 version; conversely cap epsilon at 2/3 and alpha≤1 graphs are complete (empty graph is trivial), giving the alpha≤2 version. This is a complete equivalence bridge, not a solution. 369153's two deleted edges must be independent in the source; choosing incident edges would merely select its already proved K7-vee theorem. 364519's literal definition says simultaneous presence of both fat minors, whereas the intended source excludes either kind. No general-X counterexample automatically refutes the planar special case. No unsupported scaled-subdivision quasi-isometry claim is asserted.

All future accepted endpoints would require precise definitions, all semantic bridges, independent fidelity and adversarial review, pinned Lean dependencies, axioms limited to propext/Classical.choice/Quot.sound, a paper and a safe clean extracted strict replay. No such execution is authorized or performed here.
