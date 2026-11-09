# A three-weight obstruction for two copies of 3P₂ ∨ O₂

DRAFT · AI-assisted research manuscript · 4 November 2026Prepared with OpenAI Codex assistance. No human authorship or affiliation is asserted. This draft has not been accepted by the campaign root or submitted for publication.

Abstract. We give a complete counting proof that the graph G = 2(3P₂ ∨ O₂) admits no local antimagic labelling with at most three vertex weights. This refutes Conjecture 4.1 of Gee-Choon Lau and Wai Chee Shiu [1] at r = s = 1, m = 2. An explicit labelling with four weights establishes χla(G) = 4 as supporting ordinary mathematics. The archived Lean endpoint is the literal negation of the general conjecture; it does not formalize the upper bound. The equal-role parity argument has an older analogue [2]; the mixed-role obstruction is the additional content. The significance is modest and no priority claim is made.

Definitions and source scope. All graphs here are finite, simple and undirected. A local antimagic labelling is a bijection f from E(G) onto {1,…,q}, where q = |E(G)|, such that the incidence weight w(v) = ∑e incident to v f(e) differs at adjacent vertices. Its color number is the number of distinct weights. The local antimagic chromatic number χla is the minimum of these color numbers over such labellings, when they exist. The construction below supplies existence for G.

P₂ is a single edge; Om is an edgeless graph on m vertices. A ∨ B is the join: take disjoint vertex sets and add every edge between them. Disjoint union takes separate copies with no added cross edges, and aH means a disjoint copies of H. In particular aP₂ ∨ Om uses one shared set of m null vertices, whereas a(P₂ ∨ Om) uses a separate null set in each copy. Parentheses are essential.

Lau and Shiu [1, published p. 205] conclude their constructions by stating χla(a(bP₂ ∨ Om)) = 3 for a,b,m ≥ 2 except when a is even and b is odd. Their Conjecture 4.1 reads, verbatim in mathematical notation:

“For r, s ≥ 1 and m ≥ 2, χ_la(2r((2s + 1)P₂ ∨ O_m)) = 3.”

The connected joins addressed in [1] and the even-matching constructions in its Sections 2 and 3 do not cover the missing parity case. We use precisely its admissible instance (r,s,m) = (1,1,2). It is two separate joins, not a join of all six matching edges with one null graph.

Explicit graph. For each component c ∈ {0,1}, take u_cj,v_cj (j ∈ {0,1,2}) and x_c0,x_c1. Its edges are u_cj v_cj and u_cj x_ck, v_cj x_ck for all j and k ∈ {0,1}. There are no others. Each component has 8 vertices and 15 edges; G has 16 vertices and 30 edges, with twelve degree-three vertices and four degree-six vertices.

# The complete impossibility proof

Theorem. G = 2(3P₂ ∨ O₂) has no local antimagic labelling with at most three weights.

Palette reduction. Suppose such a labelling exists. A matching edge and either null vertex form a triangle, so exactly three distinct weights occur. In a component the endpoints of any matching edge have different weights. Both null vertices are adjacent to both endpoints, so both must have the third weight. Every matching pair therefore uses the other two weights, in either orientation. This argument allows color roles to change between components.

Let M_c be the sum of the three matching-edge labels in component c. If its null weight is X and its endpoint weights are Y,Z, its join-edge sum is 2X: each join edge is counted exactly once at the null vertices. Summing the six endpoint weights counts matching labels twice and join labels once. Hence

3(Y + Z) = 2M_c + 2X.                 (1)

The labels are exactly the integers from 1 to 30, and their total is

T = 1 + ⋯ + 30 = 30 · 31 / 2 = 465.                 (2)

Case 1: equal null weights. If both components have null weight X, let Y,Z be the other global weights. Equation (1) gives 2M₀ = 2M₁ = 3(Y+Z) − 2X, so M₀ = M₁. Their join sums total 4X. Thus T = 4X + M₀ + M₁ = 4X + 2M₀ is even, contrary to (2).

Case 2: different null weights. Call them X,Y and call the remaining global weight Z. The endpoint weights are Y,Z in the first component and X,Z in the second. Put S = X+Y and M = M₀+M₁. Adding (1) in both components and using (2) yields

2M = S + 6Z,       465 = 2S + M,       5M = 465 + 12Z.       (3)

There are six matching labels, each at most 30. Thus M ≤ 180 (a deliberately loose bound). From (3),

12Z = 5M − 465 ≤ 5 · 180 − 465 = 435.                 (4)

Each of the six matching pairs has exactly one endpoint of weight Z. These six vertices are independent: the only edges between matching endpoints are within pairs of unequal weights. Their incident edges are all six matching edges, once each, and twelve distinct join edges, two per selected endpoint. No join edge can occur twice because it has just one matching endpoint. Let Q be the sum of these twelve labels. Injectivity and positivity give Q ≥ 1+⋯+12 = 78. Summing weights at the selected endpoints gives 6Z = M+Q. Eliminating M with (3),

5Q = 30Z − 5M = 18Z − 465,     18Z ≥ 5 · 78 + 465 = 855.    (5)

Equations (4) and (5) imply 36Z ≤ 1305 and 36Z ≥ 1710, respectively, which is impossible. Both cases are exhausted, so no such labelling exists. □

# A supporting four-weight certificate and related work

Exact value in ordinary mathematics. In the notation of the explicit graph, each row below supplies the five labels for one matching pair and its four incident join edges. The component and pair indices agree with the definitions above.

| c | j | u v | u x₀ | u x₁ | v x₀ | v x₁ |
| 0 | 0 | 19 | 15 | 11 | 27 | 3 |
| 0 | 1 | 22 | 2 | 21 | 10 | 17 |
| 0 | 2 | 16 | 4 | 25 | 26 | 7 |
| 1 | 0 | 14 | 18 | 13 | 30 | 5 |
| 1 | 1 | 20 | 24 | 1 | 6 | 23 |
| 1 | 2 | 8 | 9 | 28 | 12 | 29 |

The thirty entries are a permutation of {1,…,30}. Every u vertex has weight 45, every v vertex has weight 49, both null vertices in component 0 have weight 84, and both in component 1 have weight 99. For example, the first pair gives 19+15+11 = 45 and 19+27+3 = 49. The first component null sums are (15+27)+(2+10)+(4+26) = 84 and (11+3)+(21+17)+(25+7) = 84. In the second they are (18+30)+(24+6)+(9+12) = 99 and (13+5)+(1+23)+(28+29) = 99.

Every edge is a u-v edge or an endpoint-null edge, so its weights differ. The palette is exactly {45,49,84,99}. Thus χla(G) ≤ 4; the theorem gives χla(G) ≥ 4, establishing equality. The fresh verification script reconstructs the graph, checks all incidence sums and all edges, and compares its output with the independent review certificate. This upper bound is supporting mathematics and is not in the Lean theorem.

Older analogue. Tsz Lung Chan, Gee-Choon Lau and Wai Chee Shiu [2, Theorem 9] prove χla(C₃ + C₃) = 4. Its degree-two setting supplies a relevant older counting/parity analogue. We credit that precedent for the equal-null idea. It does not settle this join graph, whose null vertices have degree six. The new content relative to that analogue is completing the exchanged-null-role case using the six common-weight endpoints and twelve distinct join labels. No monotonicity of χla under taking subgraphs is used or asserted.

Bounded comparison. The independent review reads the source, the disconnected-graph paper [2], a companion join paper, and related tripartite constructions. None of the checked theorem bodies supplies this lower bound. The later formalization lane read the full publisher volume reprint of “Local Antimagic Chromatic Number for Copies of Graphs” [3], overcoming the review’s earlier blocked article-page access. Its constructions and general union upper bounds do not imply this lower bound; our graph is neither regular nor a forest. See the archived SIDE-CHECK.md for the theorem-by-theorem scope comparison.

These are bounded screens, not exhaustive prior-art clearance. OpenAlex citing coverage is incomplete and inconsistent between scalar and query results. The cached current-registry checks are path/topic screens, not full proof-body audits. No priority claim follows from a missing hit. The root ruling assesses significance as a qualified pass, modest: a short refutation of a published universal conjecture. It treats this as distinct from the earlier full t-ary-tree result, despite the shared invariant.

# Literal formal correspondence and trust limits

General family. In the reused packet, LauShiu.graph r s m is a SimpleGraph for 2r((2s+1)P₂ ∨ Om). Its matching endpoints are (t,b) with t < 2r(2s+1) and Boolean b; its null vertices are (h,k) with h < 2r and k < m. Matching adjacency fixes t and switches b. Join adjacency requires floor(t/(2s+1)) = h. No edges join different components or two null vertices. The proved vertex and edge counts are

|V| = 2r(2(2s+1)+m),       |E| = 2r((2s+1)+2(2s+1)m).

Literal invariant. AntimagicBasics.lean uses actual unordered graph edges. Labeling is an equivalence E(G) ≃ Fin |E(G)|, and weight sums label.val+1 over incident edges. IsLocal is inequality on adjacent weights. colorCount counts the finite image, spectrum is the set of attained local color counts, and chiLA is its natural infimum. The file is reused byte-identically from the accepted tree packet; its tree helpers are irrelevant here.

The formal natural infimum of an empty spectrum is 0. This convention does not create an existence gap: assuming chiLA = 3 explicitly rules out an empty spectrum, and Nat.sInf_mem then produces an actual local labelling of color count 3. In ordinary mathematics the displayed certificate supplies existence independently.

Transport and obstruction. LauShiu.vertexMap is a bijection from the discovery vertex type to the literal instance, preserving adjacency. indexedEdge is a bijection from the discovery’s complete, unique edge enumeration to the actual unordered edge set. indexedLabel composes a literal labelling with this map and adds 1, giving bounded injective integer labels. weight_correspondence reindexes every incidence sum, including the natural-to-integer cast. Endpoint.lean transports locality and the three-element image to R159.Proper and R159.Three and invokes the unchanged obstruction R159.no_three. This bridge is proved, rather than left as an assumption.

Conjecture41 quantifies over all natural r,s,m with 1 ≤ r, 1 ≤ s, 2 ≤ m and asserts chiLA (LauShiu.graph r s m) = 3. LauShiu.instance_chi_ne_three contradicts its admissible instance (1,1,2). The final theorem is

not_conjecture41 : ¬ Conjecture41.

Audits and replay evidence. The packet has seven Lean modules. The formalization lane reports a fresh extraction followed by seven strict builds and seven explicit-module checks. Its endpoint axiom log lists only propext, Classical.choice and Quot.sound; the saved transitive metadata audit has 7,825 declarations, including 201 local declarations, with no local unsafe, partial, implementation-substitution or extern flags. This dossier recomputes those metadata counts; it does not rerun Lean or a checker.

Lean is pinned to 4.34.1 and the documented mathlib revision is d13f23b723b8a846827a245b89c10fc7d3f11612. Upstream precompiled dependencies are trusted, not rebuilt here. The audit, toolchain, kernel and correspondence review are part of the trust boundary. Archived successful logs are evidence from the producing lane, not a new replay performed by this manuscript worker. The exact value 4 has not been formalized.

# Reproducibility, status and references

Reproducible dossier. The accompanying source-only.zip is copied byte for byte from the formalization lane, with SHA256

9b269351bf3dddcfd3e2c98e00ce50c60b9a8cf4edbb979011658c312e386d12

The safe-extraction receipt checks member paths, duplicates and file types and hashes every extracted file; no packet code is executed. The discovery obstruction is compared byte for byte with its original tar packet. The MathDB raw JSONL is preserved exactly, including its newline; its hash is in receipts/arithmetic.json and the source-copy manifest.

scripts/verify.py, run with python3 -I, reconstructs the certificate and recomputes graph counts, degrees, sums, bounds, palette, audit counts and archive checks. scripts/author.py produces this paper from editable content; scripts/render.py creates the editable document source; LibreOffice exports it to PDF and Poppler renders every page. REPRODUCE.md gives the foreground commands. All outputs and temporary files stay inside this lane. The resource wrapper restricts each child to at most two CPUs, CPU time 120 seconds, wall time 140 seconds and sampled process-group RSS below 6 GiB, with MALLOC_ARENA_MAX=2. Only one heavy process runs at a time.

The source copies retain publisher and retrieval receipts, including failed access attempts. Inputs are hash-bound before dossier production and checked again at handback; this is a preservation check, not a claim that the inputs are infallible. The manuscript’s finite arithmetic is rechecked from scratch. Bibliographic and source identifiers are verified against cached bodies and receipts, not treated as computed mathematical quantities.

Parent acceptance status. Root’s replay-result.json reports PASS for a fresh extraction and strict builds and checks of every module, with the permitted endpoint axioms only. Root’s separate metadata audit reports a different local-declaration count; these are distinct audit outputs, not counts to be silently equated. Root’s registry-refresh.json reports no relevant hit in its refreshed complete D5 and Problems path screens; this remains a path screen, not a full-body proof search. Both reports are copied and hash-bound here. Manuscript acceptance and paper read remain root decisions.

Draft disclosure and scope. AI assistance was used in manuscript preparation and dossier verification. No human authors or affiliations have been invented. The result is a small explicit counterexample, not a classification of the remaining parameters. It receives zero accepted credit in this dossier; root alone decides acceptance. The campaign’s administrative target is not evidence of mathematical novelty. There was no network access, publication, upload, external messaging, account interaction, browser use, git operation, theorem-prover invocation or solver invocation in this manuscript task.

References

[1] Gee-Choon Lau and Wai Chee Shiu. On local antimagic chromatic number of the join of two special families of graphs - II. Utilitas Mathematica 124 (2025), 189–206. DOI: 10.61091/um124-12. Preprint: arXiv:2410.17674v1. Conjecture 4.1 remains on published p. 205.

[2] Tsz Lung Chan, Gee-Choon Lau and Wai Chee Shiu. Complete solutions on local antimagic chromatic number of three families of disconnected graphs. Communications in Combinatorics and Optimization 10(4) (2025), 973–988. DOI: 10.22049/cco.2024.29032.1818. The DOI and journal details are verified in the cached primary body.

[3] Martin Bača, Andrea Semaničová-Feňovčíková and Tao-Ming Wang. Local Antimagic Chromatic Number for Copies of Graphs. Mathematics 9 (2021), article 1230. DOI: 10.3390/math9111230. Primary text read through the publisher volume reprint, printed pp. 39–50; metadata verified there.

Evidence pointers. evidence/joinla-review-r1/REVIEW.md supplies independent gates; evidence/joinla-formal-r2/STATEMENT-CORRESPONDENCE.md supplies the bridge review, and SIDE-CHECK.md supplies the later reprint comparison. Their historical access limitations are retained, with the later update distinguished explicitly.
