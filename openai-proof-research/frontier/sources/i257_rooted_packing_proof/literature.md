# I257 primary contracts, comparison, and read extents

Date: 2026-10-12. Mathematical correctness gate only. Pinned OpenAI results are stipulated true at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. No substantiality, worldwide novelty, priority, or prominence assessment is made. Exact input, source-byte, excerpt, and authored-output hashes are in the assigned input-authentication.json; its own hash is detached in the final response.

## Stipulated pinned manuscript

[Graph Decompositions at the Integral Expectation Threshold, pinned main.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Graph-Decompositions-at-the-Integral-Expectation-Threshold-October-5-2026/build/main.tex).

Retrieved directly at the immutable URL. Read **all 841 lines** of this one manuscript, including every proof. Retained `175-compression-transfer.tex` (lines 1–488) and `175-direct-embedding-assembly.tex` (489–841). SHA256 of the full source is `c40e3b32954b715c0e755bf763d5fbe675f4134d3b6b0a2936579751cb7cba7f`; its Git blob SHA1 is `928bb7e06d85629e06b700bc69080b179bacbb96`, matching the selected preprints-tree entry.

Relevant contracts and argument extents:

- `lem:compression` takes an arbitrary nonempty family of supports T with 1≤|T|≤s on a finite ground set, and selects at most ceil(2r^(−s)) members whose Bernoulli-r smoothed test is ≥1/2 on every original satisfying set. The complete greedy increment proof was read. I248 changes the domain to local edge coordinates and pays empty supports explicitly in its own proof.
- `prop:transfer` constructs a typical source graph class for all root sets |Y|≤n^(2/3), s≤10 log n and r^s≥n^(−1/100). Its target is a bipartite subgraph with at most n/8 positive-degree nonroots of degree ≤s, embedded fixing Y at density 1−(1−r)^32. The full compressed-test counting, independent scalar neighborhood concentration, two supply regimes, and ordinary Hall proof were read. This is the relevant one-vertex operation.
- `prop:degree-embedding` treats graphs of support ≤n/4, degeneracy ≤s, and maximum degree ≤n^(2/3). Its whole proof partitions into independent layers and exposes fresh bin-to-past edges, with a conflict graph used to obtain disjoint requirements. This separate operation does not combine rooted internal blocks into the I248 packing-rank comparison.
- `prop:stars` and its complete trial-counting proof were read, as was the final deterministic partition proof. The final assembly treats root-root, outside, and cut pieces separately; their embeddings need not agree. The main theorem is a fixed bounded-piece graph-decomposition threshold statement, not the I248 cross-product rank theorem.

These are contract comparisons under the stipulated truth assumption. They are not an audit of upstream correctness.

## Stipulated companion checked at a bounded scope

[Integral and fractional expectation thresholds are equivalent, pinned consequences.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Integral-and-fractional-expectation-thresholds-are-equivalent-September-23-2026/build/source/sections/consequences.tex).

Retrieved directly and read **all 50 lines**, including `cor:two-unions` and its complete proof. Retained `175-companion-consequences.tex`. Full-source SHA256 `56eef8e80f084b259396669f19301eac3e7d15d2f25747ec3354dbf2c6eb0958`; Git blob SHA1 `a502f66457cb6bbb4c11d18613c92ea137b64f83`, matching the selected preprints-tree entry.

Its conclusion is an integral cover budget for sets not covered by two members of a large class, without a double logarithmic loss. This is a distinct set-cover operation and supplies no matching-rank assertion here. The companion's other sections and the discrete-convexity companion's proofs were not read in I257; the self-contained I248 rank proof invokes none of them. This bounded check gives no blanket no-duplication assertion about the whole corpus.

## Serious external primary comparison

[Ferber–Luh–Nguyen, Embedding Large Graphs into a Random Graph, arXiv:1606.05923v3](https://arxiv.org/abs/1606.05923v3), [primary PDF](https://arxiv.org/pdf/1606.05923v3).

Independent PDF retrieval SHA256 `e723e9ef87d47c559ba520f1bcd2dd4a399f9a26de241422f84245821485e7c8`. Extracted with pdftotext -layout. Read **all §§1–2.3**, retained in `ferber-luh-nguyen-sections-1-to-2-3.txt`, and **all §2.4**, retained in `ferber-luh-nguyen-section-2-4.txt`. The §2.4 excerpt SHA256 is `99dfc40d3580aa5620152e14dff904ccef4584025b756459b3069dd3c1b4e8c6`, byte-identical to the fully read I248 excerpt.

This reading includes Theorem 1.6's almost-spanning bounded-degree hypotheses, Definition 2.2's α-good partition, the complete greedy extraction/coloring proof of Lemma 2.3, the stated sparse-part Riordan input, the exact compatible-block hypergraph construction, all of Lemma 2.7's Janson calculation and proof, and the full derivation of Lemma 2.5 using hypergraph Hall. This is substantive existing block embedding, not a decorative reference.

The authors use independent sprinkling rounds to extend a previously established embedding. Each batch consists of small blocks and supplies a hypergraph L_i of compatible nonroot images. They check the union matching criterion for every subfamily by finding edges outside residual forbidden sets and then invoke AH. Definition 2.2(v)'s distance-three condition ensures root-neighborhood sets W_ij and W_i'j' are disjoint when i≠i'. Their §2.4 δ_2 computation uses that fact to identify common required edges between different indices with the internal intersection alone. I248 allows arbitrary shared root requirements and does not reuse that Janson estimate; its proof works through compression of an arbitrary type family, maximum weighted packing, and exchangeable maximum-packings in independent layers.

The resulting distinction is a checked difference in hypotheses and argument. It is not a substantiality verdict or a demonstration of worldwide novelty. FLN's optimality/density claims and its earlier literature citations are not mathematical inputs to the I248 rank theorem.

Read limits: FLN §3 and references were incidentally partly displayed by a failed extraction-boundary diagnostic, not systematically read or retained. The original Riordan theorem proof and the original Janson references were not read. No claim that they supply additional uniformity is made.

## Exact AH theorem contract and original-access limit

[Aharoni–Haxell, Hall's theorem for hypergraphs, J. Graph Theory 35 (2000), 83–88](https://doi.org/10.1002/1097-0118%28200010%2935%3A2%3C83%3A%3AAID-JGT2%3E3.0.CO%3B2-V).

The theorem used by the corollary is precisely FLN Theorem 2.6, explicitly attributed to AH Corollary 1.2: for an indexed family of d-uniform hypergraphs L_i on one common finite vertex set, the strict inequality ν(∪_{i∈I}L_i)>d(|I|−1) for every nonempty index set I guarantees pairwise disjoint choices e_i∈L_i. The candidate establishes the stronger lower bound 2d|I| after padding and checking the cap. Roots are not hypergraph vertices. The theorem therefore needs no separation of root sets. Identical hypergraphs may appear under distinct demand indices.

The original publisher PDF URL and its Download PDF link redirected to the abstract page. Bounded author-site searches did not expose the original full proof. The original topological argument **was not read**. This review reads and uses the exact theorem as stated in the fully read primary FLN paper; it does not claim to have reconstructed AH itself. The nominated rank theorem is independent of this external theorem, which is used only for its application.

## Withdrawn lead, prominence, and exclusions

Read the substantive primary [arXiv:2609.20864v2 record](https://arxiv.org/abs/2609.20864v2): title, authorship, abstract, withdrawal notice, and submission history. The record describes overlapping and repeated neighborhood lists, and states that the manuscript was withdrawn due to concerns about analysis and interpretation. The full v1 argument was not retrieved or read and no theorem from it is used. It is overlap evidence for a separate contribution investigation only.

No direct MathDB prominence was established by this gate. No score is assigned. No broader literature search for worldwide novelty was attempted, because the assigned gate is mathematical correctness. No I247, I249, I250, I254 unfinished files, or other live review was read. All retained primary excerpt files were fully read, and no unread primary download or full source-tree snapshot is retained.
