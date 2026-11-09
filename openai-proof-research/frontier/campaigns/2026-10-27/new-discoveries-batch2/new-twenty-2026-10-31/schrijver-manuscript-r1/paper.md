# A diameter drop of two in Schrijver graphs

**A certificate-based refutation of the unit-gap conjecture**

**DRAFT - 3 November 2026 - MathDB 352827.** Prepared with AI assistance in lane schrijver-manuscript-r1. No human author or affiliation is asserted. This manuscript and its dossier await root adjudication; accepted credit is zero.

## Abstract

The unit-gap conjecture of Ledezma, Pastine, Torres and Valencia-Pabon asks whether increasing the ground-set size by one can reduce the diameter of a Schrijver graph by more than one, within the range 2 ≤ r ≤ k−2 for n = 2k+r. We refute the conjecture as stated in arXiv:2112.01884v2. The graphs SG(27,12) and SG(28,12) have diameters 8 and 6, respectively. We give an explicit distance-8 pair in the first graph and explain finite certificates proving a lower bound of 8 and an upper bound of 6. These two bounds alone suffice. The supplied Lean packet proves the literal negation of the conjecture, including enumeration completeness and transport from indexed certificates to the source graphs. Exact diameters and the further pair of values 9 and 7 at k = 13 are independently verified finite computations; they are not the statements of the Lean endpoint. A separate correction remark concerns the source's false Theorem 6 and plays no role in the refutation.

## 1. The question and the result

Write [n] = {1,…,n}. A k-subset S of [n] is cyclically 2-stable if no two of its elements are consecutive on the n-cycle, including the pair {1,n}. The Schrijver graph SG(n,k) has these subsets as vertices, with an edge exactly when two vertices are disjoint. For a finite connected graph G, let d_G(x,y) be shortest-path length and D(G) its maximum over vertex pairs.

The source [1, §4] formulates two conjectures. Conjecture 1 asserts, for r ≥ 1, that D(SG(2k+r,k)) ≥ D(SG(2k+r+1,k)). Conjecture 2 asserts, for integers 2 ≤ r ≤ k−2, that

D(SG(2k+r,k)) − D(SG(2k+r+1,k)) ∈ {0,1}.

The subtraction here is in the integers. A drop of two is consistent with monotonicity and contradicts the stronger unit-gap assertion.

**Theorem.** The unit-gap assertion of [1, Conjecture 2] is false. At k = 12 and r = 3, the two connected graphs satisfy D(SG(27,12)) ≥ 8 and D(SG(28,12)) ≤ 6. Thus their diameter difference is at least 2.

Independent exhaustive certificates give equality in both bounds. The supplied formal endpoint proves the sufficient bounds and their consequence, without assuming either exact diameter equality. The source's computed table reaches k ≤ 7; this witness lies beyond that range. We make no priority claim and do not resolve Conjecture 1.

<!-- PAGE -->

## 2. Finite certificates and the distance-8 pair

For reproducibility, bit i−1 of a natural-number mask denotes source element i. The two vertices used for the lower bound are

A = {1,3,5,7,9,11,14,16,18,20,23,25},

B = {1,3,5,7,10,12,15,17,19,21,23,26}.

Their masks are 21669205 and 39144021. Both contain exactly 12 elements, have no consecutive elements, and avoid the cyclic endpoint pair. In the formal stored enumeration their indices are 29 and 143; the independent review enumeration uses different indices. Masks and literal sets, rather than enumeration indices, identify the witness across implementations.

**Distance-labelling lemma.** Let G be a graph and f: V(G) → ℕ satisfy f(y) ≤ f(x)+1 on every oriented edge x∼y. If f(a)=0 and f(b)=h, every walk from a to b has length at least h.

Indeed, along a walk x_0,…,x_m beginning at a, induction gives f(x_i) ≤ i. Apply this at b. When a and b are connected, taking a shortest walk proves d_G(a,b) ≥ h. Reachability is needed: a library's convention for distances between disconnected vertices must not replace it.

For SG(27,12), the certificate supplies a label on every one of its 819 vertices. The labels of A and B are 0 and 8, and every oriented disjointness edge satisfies the lemma's inequality. The full labelling is the BFS layer index from A. Its successive layer sizes are

1, 8, 26, 93, 183, 275, 193, 38, 2.

These sizes sum to 819. The numbers alone do not prove the bound: the per-vertex layer assignment and the checked edge inequalities do. The files graph-27-12-certificate.json and the formal Label27 modules retain those assignments. A parent tree proves reachability independently of the lower-bound inequalities.

For an explicit upper witness d(A,B) ≤ 8, the intermediate vertices of an eight-edge path are the following seven sets, between A and B:

{2,4,6,8,10,12,15,17,19,21,24,26};

{1,3,5,7,9,11,13,16,18,20,22,25};

{2,4,6,8,10,12,14,17,19,21,23,27};

{1,3,5,7,9,11,13,15,18,22,24,26};

{2,4,6,8,10,12,14,16,20,23,25,27};

{1,3,5,7,9,13,15,17,19,21,24,26};

{2,4,6,8,11,14,16,18,20,22,25,27}.

Each set is stable and consecutive sets, including the endpoints, are disjoint. Together with the labelling, this proves d(A,B)=8. The exact whole-graph diameter 8 additionally uses the complete representative BFS certificates described next.

<!-- PAGE -->

## 3. The upper bound and exact computations

**Parent-tree lemma.** Fix a root c in a finite graph. Suppose each non-root vertex v has a parent p(v) adjacent to v, a positive depth h(v), and h(p(v))+1=h(v), while c has depth zero. If every vertex is covered, induction on depth constructs a walk of length h(v) from c to v. In particular the graph is connected; if all depths are at most q, all distances from c are at most q.

This certificate checks local edges and strictly decreasing depths. It does not trust an external BFS program to have found shortest paths. The upper bound uses only the resulting walks. For exact diameter calculations, our separate ordinary checker verifies the stronger BFS recurrence: layer zero is {c}, each next layer consists of all neighbors of the current layer not previously visited, and the layers exhaust the vertex set.

Cyclic rotation by t positions sends a stable k-subset to a stable k-subset. Its inverse is rotation by n−t modulo n. It preserves disjointness in both directions, hence is a graph automorphism. Thus if every vertex can be rotated to one of a collection of roots whose certified eccentricities are at most q, then the diameter is at most q: rotate the first endpoint to a root, use its tree to reach the rotated second endpoint, and rotate the walk back.

The 3,185 vertices of SG(28,12) are covered by 116 rotation roots. Every root has a certified spanning parent tree of depth at most 6. Applying the preceding argument proves D(SG(28,12)) ≤ 6. This is not a quotient-distance computation: all tree edges are literal disjointness edges, and rotation witnesses cover every original vertex. No reflection or assumed transitivity is required.

For context, the number of cyclic stable k-subsets is n/(n−k) times binomial(n−k,k). One way to count is to mark a selected point and record the k positive gaps of unselected points after selected points: the gaps sum to n−k. There are n choices of the marked position and binomial(n−k−1,k−1) gap compositions, and each subset is counted k times. This gives 819 and 3,185 for the main graphs. This count is a useful diagnostic; the formal proof establishes exact membership completeness rather than inferring it from counts.

| Graph | Vertices and rotation roots | Independently checked diameter |
|---|---|---|
| SG(27,12) | 819 vertices; 31 roots | 8 |
| SG(28,12) | 3,185 vertices; 116 roots | 6 |
| SG(29,13) | 1,015 vertices; 35 roots | 9 |
| SG(30,13) | 4,200 vertices; 140 roots | 7 |

All four exact values follow from exhaustive BFS layers and rotation coverage. The manuscript lane independently regenerated these vertex sets and all their disjointness adjacencies and rechecked every retained layer recurrence. At k = 13, r = 3, the difference is again two. This corroborating instance is an ordinary finite certificate result, not an additional Lean endpoint or a separate credited result.

<!-- PAGE -->

## 4. Enumeration completeness and literal graph semantics

The formalization represents source positions by Fin n, with Lean value i corresponding to source position i+1. A vertex is a Finset of cardinality k satisfying the cyclic successor exclusion. Adjacency is disjointness together with distinctness; at positive k, disjointness itself already forces distinctness. No extra gap condition, orbit quotient, or unlabeled identification is imposed.

To turn an indexed calculation into a theorem about this graph requires more than a table of masks. Encoding and decoding are proved inverse on masks below 2^n and on the corresponding finite subsets. Mask validity expresses the cardinality and cyclic stability conditions. Bitwise disjointness is proved equivalent to literal finset disjointness. The reference enumeration is defined using all k-element subsets of Fin n and is proved to contain exactly the valid masks.

The efficient stored enumerations are connected to this reference by a complete finite generator. Let P(n,k) enumerate path-stable k-subsets of positions 0,…,n−1 as masks. For k=0 it returns [0]; for n=0 and k>0 it is empty. At positive n and k, split according to whether the final position n−1 is absent or present. The absent branch uses P(n−1,k). The present branch sets bit n−1 in every mask from P(n−2,k−1), with the boundary case n=1 handled explicitly.

Completeness follows by strong induction on n. A set omitting n−1 is covered by the absent branch. If it contains n−1, erase that element. Path stability excludes n−2, so the remaining set lies in the earlier n−2 positions and has cardinality k−1. The induction hypothesis reconstructs it; setting the final bit reconstructs the original set. Equality of all test bits proves equality of the encoded masks.

Every cyclically stable set is path-stable and cannot contain both endpoints 0 and n−1. Therefore every valid mask survives the generator's weaker endpoint filter. Kernel decision establishes exact list equality between this filtered output and each stored vertex table. Conversely, previously checked validity of every stored entry supplies the reverse inclusion into the reference enumeration. This two-direction argument proves membership equivalence; neither the count formula nor generator completeness alone would suffice.

Table lookup and strict ordering prove the indexed tables injective. Combining injectivity, membership completeness, and adjacency correspondence yields graph isomorphisms from the finite indexed graphs to the literal SG(27,12) and SG(28,12). Connectivity, distances, and walks transport through these isomorphisms. The literal rotation automorphisms and the checked numerical rotation witnesses are proved to agree, so orbit coverage also transports.

Mathlib's natural diameter is extended diameter converted to a natural number; disconnected or infinite-diameter cases can produce zero. Both concrete graphs have separately proved connectivity from spanning parent trees. For these finite connected graphs the library diameter agrees with the maximum shortest-path length. The proof therefore cannot exploit a disconnected-graph convention.

The unit-gap statement universally quantifies natural k,r with 2 ≤ r and r+2 ≤ k, equivalent to the source range. Both diameters are cast to integers before subtraction. The specialization k=12,r=3 meets the range conditions, and 8−6=2 forces failure of membership in {0,1}.

<!-- PAGE -->

## 5. Formal architecture, audits, and trust limits

The source-only packet has 474 Lean modules and exposes the unconditional theorem Schrijver.mathdb_352827 : ¬ SchrijverUnitGap in EndpointRound5.lean. Historical rounds r1–r4 were partial: generic soundness came first, then encoding and trees, table transport, and rotation coverage. Round 5 closes the two remaining enumeration propositions by the path-generator argument. Conditional theorem names remain internally, but their premises are supplied by proved theorems.

| Mathematical component | Packet modules | Obligation discharged |
|---|---|---|
| Source definitions and conclusion | Definitions; EndpointRound5 | Cyclic stability, integer gap, literal negation |
| Generic certificate soundness | Checkers; IndexedCertificates | Edge labels bound walks; parents construct walks |
| Encoding bijection | Encoding; MaskSemantics | Inverse masks/sets; adjacency equivalence |
| Enumeration completeness | Enumeration; PathGenerator; PathCoverage; Enumeration27Proof; Enumeration28Proof | Exact reference/stored membership equivalence |
| Concrete indexed facts | TableLinks; Table27; Table28; Label27_*; LowerIndexed; Tree27_*; Tree28_*; UpperTrees | Valid injective tables, lower label, spanning trees |
| Rotations and coverage | Rotations; RotationCheck; Rotation28_*; RotationCoverage28 | Literal automorphisms and exhaustive witnesses |
| Transport | MetricTransport; BridgeTransport | Connected literal graphs and sufficient metric bounds |

The packet pins Lean 4.34.1 and mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612. Its SHA-256 is

685b78855d145dae95ba175796528739f8a9ee5ea54fb621fc78b5ccdc763d1b.

This dossier reuses the archive byte-identically. It includes a safe extraction and checks the archive's source manifest, without executing Lean, lake, or leanchecker.

The r5 author reports 474 strict builds and 474 leanchecker passes from a fresh extraction. The independent fidelity review [3] instead performed a representative replay of 21 modules using hash-bound existing dependency objects. It is not a second full source-only rebuild. That review reports an exact endpoint closure of 463 local modules and 1,585 declarations; its wider audit covers 1,611 declarations. The allowed and observed endpoint axioms are propext, Classical.choice, and Quot.sound.

Declaration audits reject unsafe or partial flags, generated unsafe recursion companions, implemented_by, extern, and any other transitive axiom. The review's source scan found no forbidden source uses. Seven reported negative controls reject corrupted enumeration, masks, packed lookup, rotation, cycle semantics, path count, and tree bound. Their intended failures test the checkers; they are not substitutes for the soundness proofs.

Root's decisive fresh replay result is pending at this manuscript snapshot: schrijver-parent-final-r1/replay-result.json is absent. We claim no result for that replay. The formal statements and prior audit outcomes above are descriptions of the supplied packet and receipts, not a new kernel replay by this manuscript lane. The trusted base includes the pinned kernel and library, correct source/statement correspondence, and integrity of the delivered bytes. The exact-diameter computations additionally trust the ordinary checker; the Lean refutation only needs its independently formalized sufficient bounds.

<!-- PAGE -->

## 6. Search coverage and a separate correction remark

The first retained search covered k=2,…,10 and r=1,…,min(6,k−1), subject to a 6,000-vertex cap. The independent review recomputed Table 1 ranges for k=2,…,6, including the first graph in each diameter-two tail. For k=7, n=15,…,24 completed; n=25 timed out, and n=26 exceeded the 60,000-vertex enumeration cap. These are incomplete instances, not verified values.

The further review search considered k=8,…,16 with n=2k+1,…,2k+5 and a 4,500-vertex cap. Completed and skipped records are retained in the graph logs and graph-combined.json. Across the review's retained runs, 75 distinct graph instances completed. The smallest k with a retained r≥3 unit-gap violation is k=12, at r=3. This is computational evidence within those bounded searches, not a proof of global minimality or exhaustive coverage of every admissible r.

For n≥4k−2, the review also gives an elementary diameter-two tail argument. That argument is not additional finite search coverage. In particular neither skipped graphs nor infinite tails are counted as successful BFS runs. The present lane rechecks only the five certificate graphs used here; it does not rerun or extend the historical search.

**Correction remark (no credit claimed).** Source [1, Theorem 6] asserts, for k≥3, that D(SG(2k+2,k)) is floor(3k/4) for even k and floor(3k/4)+1 for odd k. For k=6 it prints 4, whereas D(SG(14,6))=5.

An explicit pair at distance five is A₀={1,3,5,7,9,12} and B₀={1,3,6,8,10,12}. A path of length five between them has intermediate sets

{2,4,6,8,10,14}, {1,5,7,9,11,13},

{3,6,8,10,12,14}, {2,4,7,9,11,13}.

All consecutive sets are disjoint and stable. The complete closed radius-two balls around A₀ and B₀ have sizes 17 and 13 and are disjoint, as checked over all 49 literal vertices. Any path of length at most four would have a middle vertex within distance two of both endpoints, a contradiction. This proves distance five. Complete orbit certificates establish the whole-graph upper bound five; these are ordinary certificates, not a claimed Lean theorem about SG(14,6).

The reviewer identifies a concrete invalid step on printed page 19 of arXiv v2. Setting j−i=k−floor(3k/4)−1 gives k+i+1−j=floor(3k/4)+2, not a number at most floor(3k/4). Consequently the subsequent “without loss” restriction on j−i does not exhaust the required cases. This is an identified error, not a claim that it is the only defect.

The original r=2 example at k=10 was classified as a source-internal correction: the source's printed diameter 7 would give a drop of only one to the computed next value 6, whereas the actual first value is 8. No credit is claimed for that route or this correction. Our r=3 proof uses neither Theorem 6 nor any r=2 graph and does not contradict the source's stated r≥3 bounds.

<!-- PAGE -->

## 7. Source fidelity, related work, and access limits

The target is the literal Conjecture 2 on printed page 21 of arXiv:2112.01884v2, dated 11 February 2022. The source's definitions and conjecture body were available as PDF and text. The earlier v1 lacks the added r=2 section and Conjecture 2. The raw MathDB record's historical “open” label and empty solution list establish neither present openness nor novelty.

The journal publication is Discrete Applied Mathematics 350 (2024), 15–30 [2]. Its body was not read. ScienceDirect was excluded as an access route; HAL title and author searches supplied no copy, and CONICET returned HTTP 403 and was not retried. The retained OpenAlex evidence identifies the arXiv version as a green copy. Consequently the statement-fidelity claim is to arXiv v2; we do not certify that the journal retains identical wording or that it contains no correction.

The bounded literature review [4] sought later exact diameter work, corrections, author copies, and relevant citing work. No resolution of this r=3 instance was identified in the checked material. The identified citing journal work concerns strong diameters of graph products and was not evidence of a Schrijver refutation. Citation databases and exact searches are incomplete, and negative search results are not proof of originality. We do not claim worldwide novelty or priority.

The source itself develops exact formulas and bounds for Schrijver graph diameters, using the stable-set description that our proof preserves. Our contribution in this draft is the concrete r=3 obstruction and its verified certificate architecture. Its force comes from an explicit lower witness and a whole-graph upper bound, rather than reliance on the source's erroneous r=2 formula.

The parent registry refresh of 3 November 2026 is copied as a dated receipt. It records OpenAI/math head 4eaee87548250b2682affda7d05d947c05554bae and Omega head 46f0e39d7fd8e9a0d33c0a6be8d64298f9abd383. A keyword screen over complete current D5 and Problems trees found no matching paths. This is a path screen, not a complete proof-body search or a journal-scope clearance. This manuscript lane made no external requests and did not independently refresh those registries.

## Bibliography and evidence references

[1] Agustina Victoria Ledezma, Adrián Pastine, Pablo Torres, and Mario Valencia-Pabon. On the diameter of Schrijver graphs. arXiv:2112.01884v2, 11 February 2022. https://arxiv.org/abs/2112.01884v2. Definitions in §§1–2; Theorem 6 and its proof in §3; Conjectures 1–2 in §4.

[2] The same authors. On the diameter of Schrijver graphs. Discrete Applied Mathematics 350 (2024), 15–30. DOI: 10.1016/j.dam.2024.02.019. Journal metadata verified in the retained review evidence; journal body unread.

[3] Project evidence, schrijver-fidelity-r1. REVIEW.md and review.json, 3 November 2026. Independent statement-fidelity, proof-architecture, semantic sanity, and representative replay review. Advisory, not acceptance.

[4] Project evidence, leads-review-r122. REVIEW.md, review.json, and graph certificates, 3 November 2026. Independent ordinary computation, Theorem 6 diagnosis, and bounded prior-art review. Advisory, not acceptance.

[5] MathDB record 352827. Unit-gap conjecture for diameters of Schrijver graphs. Frozen raw line from mathdb-normalized-chunk-0008.jsonl, one-based line 2143. https://mathdb.com/p/352827/unit-gap-conjecture-for-diameters-of-schrijver-graphs. The dossier retains the exact bytes; its historical status is not independently endorsed.
