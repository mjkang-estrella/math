# Proof dossier: MathDB 366974

The complete self-contained proof and exact arithmetic follow. The lower bound is proved in prose; the supplied Lean endpoint certifies the upper bound and full refutation. Zero accepted credit.

# Five positive matchings for C₃ □ C₄

## A finite counterexample to Conjecture 4.7 of arXiv:2502.02826

DRAFT • 3 November 2026 (America/Los_Angeles) • MathDB 366974

Prepared with OpenAI Codex AI assistance. No human authorship or affiliation is asserted. This draft and its evidence are submitted for root review; accepted campaign credit is zero.

### Abstract

We give an explicit ordered decomposition of the 24 edges of C₃ □ C₄ into five positive matchings. Integer vertex weights certify every stage in the residual graph. A short lower bound for nonempty finite r-regular graphs, r ≥ 2, then gives pmd(C₃ □ C₄) = 5. This contradicts the explicitly listed case (3,4) of Conjecture 4.7 of Farrokhi D. G. and Yazdan Pour [1]. The upper bound and the negation of the full conjecture have a supplied Lean certificate, with a previously completed independent root replay. We also retain checked five-part certificates for (3,5), (3,6) and (3,7). The contribution is modest: a finite-search counterexample to a specialized exact-value conjecture, without an infinite construction or classification. No priority claim is made.

### 1. Definitions and the source assertion

All graphs here are finite and simple. A matching is a set of pairwise vertex-disjoint edges. Following [1, p. 1], a matching M in G = (V,E) is positive if there is w: V → ℝ such that, for each uv ∈ E, w(u) + w(v) > 0 if and only if uv ∈ M. Unselected edges thus have nonpositive sums; strict negativity is not part of the literal source definition.

A positive matching decomposition is an ordered partition (M₁,…,Mₖ) of E into nonempty parts such that Mᵢ is positive in the residual graph Gᵢ = (V, E ∖ (M₁ ∪ ⋯ ∪ Mᵢ₋₁)). The number pmd(G) is the least number of parts. Every finite graph admits such a decomposition, for instance by successive single edges: give their two endpoints weight 1 and all other vertices weight −3 in the current graph.

For m,n ≥ 3, Cₘ □ Cₙ has vertex set ℤ/m × ℤ/n. Two vertices are adjacent exactly when one coordinate agrees and the other differs by ±1 in its cyclic group. This is the ordinary Cartesian product, with no loops or repeated edges. In particular, the edges of C₃ form a triangle.

The following is Conjecture 4.7 verbatim, with the Cartesian product symbol typeset as □ and subscripts restored from the PDF [1, p. 23]:

“Conjecture 4.7. pmd(Cₘ □ Cₙ) = 6 for all m, n ≥ 3 with m + n even or (m, n) = (3, 4), (3, 6), (5, 6).”

Theorem 4.5 of [1] proves 5 ≤ pmd(Cₘ □ Cₙ) ≤ 6 for all m,n ≥ 3. It further proves equality 5 if m+n is odd and {m,n} is none of {3,4}, {3,6}, {5,6}. Its construction explicitly excludes these cases. Proposition 4.6 proves pmd(C₃ □ C₃) = pmd(C₄ □ C₄) = 6. Neither result determines the (3,4) case.

---PAGE---

### 2. The complete five-part certificate

Label vertex (a,b) by 4a+b, for 0 ≤ a < 3 and 0 ≤ b < 4. The rows below are in deletion order. A pair uv denotes the unordered edge {u,v}; commas separate its endpoints.

| Stage | Matching |
| --- | --- |
| 1 | {2, 10};  {3, 7};  {5, 9};  {8, 11} |
| 2 | {0, 8};  {1, 5};  {2, 3};  {4, 7};  {6, 10} |
| 3 | {0, 4};  {1, 2};  {3, 11};  {6, 7};  {9, 10} |
| 4 | {0, 3};  {1, 9};  {4, 8};  {5, 6};  {10, 11} |
| 5 | {0, 1};  {2, 6};  {4, 5};  {7, 11};  {8, 9} |

For stage i, the next table gives wᵢ(v) in the vertex order 0,…,11. These are integers, regarded also as real numbers. Each selected edge has sum 1.

| i | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | -10 | -10 | -3 | 2 | -10 | 8 | -10 | -1 | 6 | -7 | 4 | -5 |
| 2 | -5 | -3 | 2 | -1 | -7 | 4 | -9 | 8 | 6 | -12 | 10 | -12 |
| 3 | -9 | -3 | 4 | 8 | 10 | -12 | -5 | 6 | -12 | 2 | -1 | -7 |
| 4 | -9 | 8 | -12 | 10 | -5 | 4 | -3 | -12 | 6 | -7 | 2 | -1 |
| 5 | 10 | -9 | 8 | -12 | 6 | -5 | -7 | 4 | 2 | -1 | -12 | -3 |

### Theorem 1

The displayed rows form a positive matching decomposition of C₃ □ C₄. Consequently pmd(C₃ □ C₄) ≤ 5 and Conjecture 4.7 of [1] is false.

Proof. The vertex labeling gives the following 24 edges, grouped by their smaller endpoint:

0: 01, 03, 04, 08;   1: 12, 15, 19;   2: 23, 26, 2·10;
3: 37, 3·11;   4: 45, 47, 48;   5: 56, 59;   6: 67, 6·10;
7: 7·11;   8: 89, 8·11;   9: 9·10;   10: 10·11.

Here a dot separates a two-digit endpoint; thus 2·10 means {2,10}, not a product. This list follows directly by changing one cyclic coordinate. Comparing with the decomposition table shows each edge occurs exactly once. In every row no vertex repeats, so each part is a matching. The row sizes are 4,5,5,5,5 and sum to 24.

For completeness, the next page gives every residual edge sum, rather than a sample or an invocation of search. A dash means that the edge has already been deleted and imposes no condition at that stage. Exactly the edges in row i have sum 1 in column i; every other numeric entry in that column is negative. These are precisely the required positivity tests in Gᵢ. This proves the decomposition assertion. Since (3,4) satisfies the explicit exceptional clause of Conjecture 4.7, the conjecture would give value 6 for this same graph, contradicting the upper bound 5. ∎

The certificate was found by finite search in the discovery lane. Search is a means of finding these data, not an extra premise in the proof. Checking adjacency, the partition and the integer inequalities suffices to reproduce the upper bound without a search solver, floating-point arithmetic or Lean.

---PAGE---

### 3. All residual sums and the exact value

| Edge | Stage 1 | Stage 2 | Stage 3 | Stage 4 | Stage 5 |
| --- | --- | --- | --- | --- | --- |
| 0, 1 | -20 | -8 | -12 | -1 | 1 |
| 0, 3 | -8 | -6 | -1 | 1 | - |
| 0, 4 | -20 | -12 | 1 | - | - |
| 0, 8 | -4 | 1 | - | - | - |
| 1, 2 | -13 | -1 | 1 | - | - |
| 1, 5 | -2 | 1 | - | - | - |
| 1, 9 | -17 | -15 | -1 | 1 | - |
| 2, 3 | -1 | 1 | - | - | - |
| 2, 6 | -13 | -7 | -1 | -15 | 1 |
| 2, 10 | 1 | - | - | - | - |
| 3, 7 | 1 | - | - | - | - |
| 3, 11 | -3 | -13 | 1 | - | - |
| 4, 5 | -2 | -3 | -2 | -1 | 1 |
| 4, 7 | -11 | 1 | - | - | - |
| 4, 8 | -4 | -1 | -2 | 1 | - |
| 5, 6 | -2 | -5 | -17 | 1 | - |
| 5, 9 | 1 | - | - | - | - |
| 6, 7 | -11 | -1 | 1 | - | - |
| 6, 10 | -6 | 1 | - | - | - |
| 7, 11 | -6 | -4 | -1 | -13 | 1 |
| 8, 9 | -1 | -6 | -10 | -1 | 1 |
| 8, 11 | 1 | - | - | - | - |
| 9, 10 | -3 | -2 | 1 | - | - |
| 10, 11 | -1 | -2 | -8 | 1 | - |

### Lemma 2 (regular-graph lower bound)

If G is a nonempty finite simple r-regular graph with r ≥ 2, then pmd(G) ≥ r+1.

Proof. At any vertex the r incident edges must lie in distinct matching parts, so a decomposition with at most r parts would have exactly r parts. Each of these parts must meet every vertex, hence each is perfect. Let w certify positivity of the first part M₁ and put W = ∑ᵥ w(v). Since M₁ is perfect, W equals the sum of its edge sums, all strictly positive. Thus W > 0. The graph left after deleting M₁ is (r−1)-regular, so the sum of its edge sums is (r−1)W > 0, counting each vertex weight once for each remaining incidence. Every remaining edge instead has nonpositive sum by positivity of M₁. Their total is therefore ≤ 0, a contradiction. ∎

The hypotheses matter: a nonempty 1-regular graph has pmd 1. For C₃ □ C₄, each vertex has two distinct neighbors in each coordinate, so the graph is 4-regular. Lemma 2 and Theorem 1 give the exact value pmd(C₃ □ C₄) = 5. This lower bound is also the regular-graph consequence of [1, Lemma 4.3]. The manuscript supplies its proof independently. It is not claimed as a new general theorem or as part of the supplied Lean endpoint.

---PAGE---

### 4. Supporting certificates and formal correspondence

The independent review produced further five-part certificates. For C₃ □ Cₙ use label na+b for (a,b). The complete parts and integer weights are retained in certificates/3-n.json, with n replaced by 5, 6 or 7. Our separate verifier reconstructs the graph from coordinates and rechecks every partition, matching and residual inequality; it does not rely on the discovery program's verdict.

| (m,n) | Vertices / edges | Part sizes | Max other residual sum¹ |
| --- | --- | --- | --- |
| (3,5) | 15 / 30 | 5, 6, 7, 7, 5 | -1, -1, -1, -1, - |
| (3,6) | 18 / 36 | 6, 7, 8, 8, 7 | -1, -1, -1, -1, - |
| (3,7) | 21 / 42 | 7, 9, 9, 10, 7 | -1, -1, -1, -1, - |

All selected sums in these certificates equal 1 and all other residual sums are strictly negative. Their graphs are again 4-regular; Lemma 2 gives exact value 5. Thus (3,5) and (3,7) also contradict the even-sum clause, while (3,6) contradicts another explicit exception. These are supporting instances of the same conjecture and family. They have no additional Lean endpoint, separate priority clearance or separate discovery credit. No conclusion is drawn here for (5,6), (4,6) or any infinite family. The review's bounded searches for the first two were incomplete.

The Lean namespace is TorusPMD. The vertex type V m n is Fin m × Fin n. The predicate cycleAdj requires distinct endpoints and cyclic successor adjacency in either direction; torus is the Cartesian adjacency predicate. For (3,4), idx(a,b) = 4a+b translates the printed tables to colors and weights. Colors are indexed 0,…,4, one less than the printed stage number. Weights are integers cast into ℝ in five_part_decomposition.

Decomposition G k means that there exist a symmetric coloring c of ordered vertex pairs into Fin k and real weights w for each color. Each color occurs on an edge. Equally colored edges at a vertex have the same other endpoint, expressing the matching property. On each edge uv with color at least i, the condition is 0 < wᵢ(u)+wᵢ(v) if and only if c(u,v)=i. Coloring nonedges is irrelevant to every edge test.

The theorem parts_partition states that every graph edge belongs to exactly one color class. residual_partition identifies deleting all earlier classes with retaining edges whose color is at least i. The definition pmd G is the natural-number infimum of {k | Decomposition G k}; pmd_minimum proves it is attained and minimal whenever a decomposition exists. The constructed five-part decomposition provides this nonemptiness, avoiding any appeal to an empty-infimum convention. No edgeless-graph convention is needed at the conjecture's m,n ≥ 3.

The finite theorem certificate uses kernel decide to check the data. five_part_decomposition transfers its integer inequalities to real inequalities. pmd_le_five gives the upper bound. Finally refutes_conjecture_4_7 negates the universal assertion for every m,n ≥ 3 with the displayed even-sum or exceptional-pair condition. Its proof specializes to (3,4) and contradicts equality to 6 using the upper bound. It does not assert a classification of the other parameters.

Strictness is consistent throughout. The source and Lean permit zero on unselected edges. The displayed certificates prove the stronger strict version. More generally, for a finite nonempty selected part, subtract ε from every vertex weight, with 0 < 2ε smaller than the least selected sum. Selected sums remain positive and every formerly nonpositive sum becomes negative. Empty parts may be removed.

---PAGE---

### 5. Audits, replay and reproducibility

The frozen proof source TorusPMD.lean has SHA256

deccf349a114ba096fc2b42387c745ab169675accdf6fcea427274c037922b89

The reused lean-packet.tar.gz has SHA256

f8e94288a8ab8a1ec5a8c41c1da1795e9bade7a06c44080aef9b883ab210c2de

These hashes identify the source and packet, rather than a newly generated proof artifact. The manuscript preparation did not run Lean, lake or leanchecker. It validated archive paths and member types, safely extracted the archive locally and confirmed byte identity of the proof source. The exact original packet is included unchanged.

The independent review [7] reports a strict extracted build with Lean 4.34.1, mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612, warnings treated as errors, and explicit-module leanchecker success. Its audit covered 24 local declarations, with no unsafe/partial definitions, implemented_by or extern attributes, or prohibited proof shortcuts. The endpoint's printed axioms were propext, Classical.choice and Quot.sound. Original failed reviewer utility attempts are retained alongside their corrected successful versions; they were not proof failures.

A separate root receipt [8], dated 4 November 2026 UTC (3 November locally), reports an independently extracted build, successful explicit-module leanchecker run, audit of all 24 local declarations and an independent arithmetic check. Root used its own build command, not the packet scripts. The build exited 0 with reported peak RSS 1.96 GB. An initial leanchecker attempt lacked the pinned binary directory on PATH; the corrected attempt passed. The allowed endpoint axioms were again exactly propext, Classical.choice and Quot.sound. These are historical receipts read for this dossier, not new executions by this manuscript worker.

Trust limits remain explicit: the usual Lean kernel and the pinned imported environment are trusted; upstream dependencies were not rebuilt from first principles here. Hash identity binds the replayed source and archive. The exact-value lower bound is the ordinary proof on page 3, while the formal endpoint proves the upper bound and the full logical refutation. The additional certificates have exact arithmetic verification but no new Lean proof. Review and replay do not certify bibliographic novelty or campaign significance.

The dossier includes the exact MathDB raw JSONL line and its SHA256, the primary PDF and text, selected related-source copies, original access receipts, review artifacts, root ruling and replay receipts. The raw-line hash is 9b3dc9c18dde0785c0b01f868dfcea95d0780ae6f0536f087ee9ec9ca8bfa292. The primary PDF hash is f3a34ed5b4a8c1474a1a391e44e5ab02986a946475e1ff0d68d3e23945362843. The target is the literal source assertion, not an unsupported statement inferred from MathDB's related-paper metadata.

REPRODUCE.md describes the offline arithmetic checker, safe extraction, PDF generation and manifest verification. All frozen discovery, review and root input files are hash-bound before and after preparation. This work is confined to its assigned manuscript directory, with no external requests, publication, messages, shared edits or delegation. The rendering receipt and individual page images record visual QA. The full-dossier ZIP is a convenience copy; its checksum is external to the ZIP to avoid a self-referential manifest.

---PAGE---

### 6. Related work, access limits and significance

Positive matching decompositions arose in the study of Lovász-Saks-Schrijver ideals [3]. The companion [2] develops the graph invariant. The independent review read its relevant bounds and special graph classes: its bipartite regular results do not apply to our graph, which contains triangles; its circular and Möbius ladders and generalized Petersen graphs have degree at most 3. The target is not complete multipartite, so that class does not supply the target value either. The hypergraph works [4,5] and the small-cycle graph results in arXiv:2305.09190 do not supply this torus value in the reviewed sections.

The previously inaccessible Genova thesis lead was resolved by the reviewer using a distinct open institutional copy [6]. Section 2.3, printed pp. 64–68, and the pmd research direction were read. They discuss basic bounds, cacti, multipartite graphs and the companion, with no target value or torus table. A topic scan found no Cartesian/torus discussion. The rest of the thesis was not read line by line. Its PDF hash is e18d3fdaf5c025788e416fef5eb2497358f245b0664bdbadaec2127c73fb7431. The successful institutional URL and the earlier TLS failure are preserved in the access receipts. The successful curl downloads used --insecure; the reviewer cross-checked institutional landing metadata and a web PDF fetch. This is a disclosed transport-authenticity limitation, not a complete provenance guarantee.

The bounded prior-art review found no earlier target value. Citation indexes and search results are incomplete; the known thesis itself was absent from the targeted citation list. The source's Theorem 4.5 and Proposition 4.6 leave (3,4) unresolved. Root's later registry refresh [8] records OpenAI/math head 4eaee87548250b2682affda7d05d947c05554bae and Omega head 3bb89bf746f49a5abb27581c252bffedd863494e. Complete untruncated Omega D5 and Problems path trees (13,839 and 1,709 paths) had no target-topic regex hit. This was a path screen, not exhaustive proof-content review. No new live search was performed for this draft. These facts support a bounded negative finding, never global novelty or priority clearance.

The contribution is a small finite counterexample at a deliberately excluded, explicitly conjectured case. It settles that case and refutes the universal equality, but offers neither a general construction nor a full torus formula. Supporting cases are not separate discoveries. Root alone must read this draft and decide acceptance and significance; the present accepted credit remains zero.

### References

[1] M. Farrokhi D. G. and A. A. Yazdan Pour. Positive matching decompositions of the Cartesian product of graphs. arXiv:2502.02826v1, 2025. Primary source, especially pp. 1, 18–23. https://arxiv.org/abs/2502.02826

[2] M. Farrokhi D. G., S. Gharakhloo and A. A. Yazdan Pour. Positive matching decompositions of graphs. Discrete Applied Mathematics 320 (2022), 311–323. Open copy: arXiv:2110.12168.

[3] A. Conca and V. Welker. Lovász-Saks-Schrijver ideals and coordinate sections of determinantal varieties. Algebra & Number Theory 13(2) (2019), 455–484. Bibliographic details from [1]; no fresh full-body audit here.

[4] S. Gharakhloo and V. Welker. Hypergraph LSS-ideals and coordinate sections of symmetric tensors. Communications in Algebra 51(9) (2023), 4033–4043. Open copy: arXiv:2202.10463.

[5] M. A. Nambi and N. Kumaron. Positive matching decomposition conjectures of hypergraphs. arXiv:2309.15424, 2023.

[6] E. Tolosa Villarreal. Lovász-Saks-Schrijver ideals and the dual F-signature of Veronese subrings. PhD thesis, Università degli Studi di Genova, May 2025. Institutional handle: https://unige.iris.cineca.it/handle/11567/1250416

[7] Independent adversarial review of MathDB 366974. Internal frozen pmd-review-r1/REVIEW.md, 4 November 2026 UTC. Supplied with this dossier; bounded review, not a publication.

[8] Root replay and registry refresh receipts. Internal pmd-parent-final-r1/replay-result.json and registry-refresh.json, 4 November 2026 UTC. Supplied under evidence/root/. No unverified DOI is asserted in this bibliography.
