# I258 primary comparison and read extents

2026-10-12. Contribution/overlap review only. Final verdict TECHNICAL; no proof-gate claim. The immutable OpenAI corpus is stipulated true. Source hashes and exact retained paths are in `frontier/experiments/i258_rooted_packing_contribution/input-authentication.json`.

## Stipulated primary arguments

Base URL: `https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/`.

**Graph Decompositions at the Integral Expectation Threshold**, `preprints/Graph-Decompositions-at-the-Integral-Expectation-Threshold-October-5-2026/build/main.tex`. Read all 841 lines, including the complete compression and transfer proofs, both direct embedding proofs, and final assembly. Retained the full manuscript as `175-graph-decomposition-full.tex`. Fresh retrieval matched Git blob `928bb7e06d85629e06b700bc69080b179bacbb96` in the immutable preprints tree and SHA256 `c40e3b32954b715c0e755bf763d5fbe675f4134d3b6b0a2936579751cb7cba7f`.

Relevant labels: `lem:compression` selects at most ceil(2r^(-s)) requirements with a ≥1/2 smoothed test on each satisfying set; `prop:transfer` treats root-fixed bipartite pieces with |Y|≤n^(2/3), support≤n/8, outside degree≤s, s≤10 log n and r^s≥n^(-.01), at target density 1−(1−r)^32. Its proof simultaneously controls source sums and target candidate counts for every compressed test, then invokes Hall. Repeated neighborhoods still contribute repeated demand. The source already supplies arbitrary root-neighborhood overlap, adaptive Hall families and common-mean source/target tests. `prop:degree-embedding` and `prop:stars` provide separate direct embeddings; `thm:main` does not require common embeddings of its edge pieces. Nothing read there states the nominated d-block rank transfer. All these are treated as true; no truth audit was conducted.

**Talagrand's discrete-convexity conjecture**, `.../build/source/sections/00_intro.tex` (173 lines) and `03_density.tex` (84 lines). Both read in full and retained. The main contract is same-density covering of exceptional sets outside 2^75 unions of an arbitrary likely family. The introduction's `cor:two-union` includes a full constant-loss consequence proof. The entire density-restoration proof was read, including dependent rows and the saturated case. These concern covers and unions, not maximum compatible block packing ranks. The internal covering and signed-kernel sections, and the separate figure input, were not read in I258 and are not retained or used as new proof inputs.

**Integral and fractional expectation thresholds are equivalent**, `.../build/source/sections/introduction.tex` (208 lines) and `consequences.tex` (50 lines). Read both in full and retained. `thm:main` states dimension-independent constant-factor integral/fractional rounding; `cor:two-unions` has a complete consequence proof using Li and that stipulated rounding theorem. No matching-rank transfer is stated in these read sections. The internal selector/rounding proofs were not needed, not audited, and not claimed read. These are the relevant companion contracts inspected, not a claim to have read every companion page.

## Ferber–Luh–Nguyen

[Embedding Large Graphs into a Random Graph, arXiv:1606.05923v3](https://arxiv.org/pdf/1606.05923v3). Entire §2.4, “Embedding the small dense graphs,” read, including Lemmas 2.5 and 2.7, every Janson covariance estimate, Theorem 2.6 and the final greedy matching argument. The 470-line retained excerpt was independently verified to be a contiguous substring of a fresh `pdftotext -layout` extraction. PDF SHA256: `e723e9ef87d47c559ba520f1bcd2dd4a399f9a26de241422f84245821485e7c8`.

The argument introduces compatible-block hypergraphs, demands sufficiently large matchings for every subfamily, and applies Aharoni–Haxell in independent rounds. In its notation, W_ij∩W_i'j'=∅ for i≠i'. That condition is used in the different-block covariance calculation: shared edges between distinct extended copies can only come from their internal overlap. Arbitrary root reuse would add covariance not covered by that calculation. The theorem therefore does not imply I248's rank statement directly. Its architecture is prior art; unrestricted overlap is a distinction, and the candidate's strong density restriction makes it a different regime rather than an improvement of FLN's sparse embedding conclusion.

Read limit: I258 read the entire relevant §2.4, not all other FLN sections. Contextual hypotheses explicitly restated there were read. The separate original Aharoni–Haxell topological proof was not accessed. The candidate's main nomination is independent of AH; its application uses the precise sufficient condition stated in FLN Theorem 2.6. No independent verification of AH's original proof is claimed.

## Nenadov–Škorić

[Powers of Hamilton cycles in random graphs and tight Hamilton cycles in random hypergraphs, arXiv:1601.04034v2](https://arxiv.org/pdf/1601.04034v2). Entire §3 read: definitions, Lemma 3.3, Claim 3.4, full connecting-lemma proof, §3.1 corollaries and their proofs, and the complete Janson proof of Claim 3.4 in §3.2. Retained extraction lines 211–751, exactly through the end of §3. PDF SHA256: `51a14fe0d557f6d6be65b6d176c565a3f73f9f0d793661d1814673390e9a9e2e`.

Lemma 3.3 already holds for every allowed family of disjoint root tuples on its random-host event. It uses m(F,x)-density, permits F to grow, and finds internal-disjoint rooted copies in a reservoir. Its proof obtains a simultaneous copy-after-deletion property and iterates greedy rounds in bins. This is substantial preexisting simultaneous rooted-matching machinery. Its disjoint-root hypothesis and absence of a source-host rank comparison prevent identifying the exact candidate as an existing corollary. The comparison is evidence against claiming simultaneous rooted matching itself as the advance.

Read limit: other sections, absorber constructions and Hamilton-cycle assembly were not read and are not inputs. The web introduction was inspected for identification/context; only the completely read §3 is retained.

## Yang withdrawn lead: evidence about ideas only

The current primary [arXiv record for 2609.20864](https://arxiv.org/abs/2609.20864) was read on 2026-10-12. It labels v2 withdrawn and records concerns about analysis/interpretation. **No theorem from this manuscript is treated as correct.** The [v1 PDF](https://arxiv.org/pdf/2609.20864v1) was nevertheless retrieved for actual overlap reading. PDF SHA256: `a93f62379c873427cfa7edcd86383f4a7dd95e604aeb3e7ba54f26d8cfbbe6c8`.

Fully read and retained: §3, extraction lines 324–527 (all definitions, Theorem 3.3 and its complete proof, Corollary 3.4, Remark 3.5); §4.1, lines 543–587 (complete rooted estimate and proof); concluding remarks and all Appendix A, lines 973–1123 (including complete robust-sunflower, two-sided bracket and quantitative-bound arguments). These read portions use scalar Hall-function demand/supply control, arbitrary repeated/overlapping lists, biased approximation and a finite test class. They contain no maximum d-block rank functional or exchangeable-optimum amplification lemma. This establishes conceptual overlap at the scalar level, without relying on correctness or adjudicating why the paper was withdrawn.

Read limits: this is not a full-paper claim. Graph-decomposition assembly, the later structured/few-pattern applications and most of Appendix B were not read. An extraction also displayed the opening of §4.2 and Appendix B, but neither was used or retained. The introduction was seen only at partial abstract/identification scope. Source access succeeded; the earlier author-level failure to read v1 is not carried into I258.

## Bounded current search and prominence limits

The live search used eighteen queries in five batches, including exact identifiers and combinations of rooted packing, rank transfer, weighted packing/sprinkling, overlapping root neighborhoods, rooted matching lemmas and hypergraph connecting lemmas. Exact queries:

- `"rooted" "packing" random graph transfer`; `"2609.20864"`; `"1606.05923" embedding large graphs`; `random graph simultaneous rooted embeddings overlapping neighbourhoods matching sprinkling`.
- `"2609.20864"`; `"1606.05923"`; `"rooted" "embedding" "overlapping" random graph`.
- `random graphs "rooted" "embedding lemma" "overlap"`; `random graphs rooted matching lemma arbitrary families common neighbourhoods universality`; `"packing rank" "random" graph`; `"rooted" "sprinkling" "Haxell"`.
- `random graph "rooted" "matching lemma" Nenadov`; `random graph "connecting lemma" rooted graphs hypergraph matching`; `"random graphs" "rooted copies" "disjoint" embedding`.
- `"rooted" "rank transfer" graph`; `"rooted-pattern" packing graph`; `"weighted packing" "sprinkling" random`; `site:mathdb.com rooted packing transfer`.

Search results were only leads. Nonprimary mirrors, machine-learning graph matching, arborescence packing and unrelated results were not theorem evidence. The directly read primary comparisons are those documented above. No identical primary rank-transfer statement was located in this bounded search. It is not a completeness or priority certificate. No directly matching MathDB record was established; no MathDB score or prominence claim is made. The author's Goddyn record concerns a discarded direction and is not prominence evidence for this candidate.

## Retention and authentication

Only fully read primary source files/sections are retained in this I258 directory. Full external PDFs were retrieved in memory for extraction and hashing, not retained; a PDF hash authenticates the container from which the read excerpt was taken, not a claim that every PDF page was read. Pinned files were freshly retrieved and authenticated against Git blob SHA1s in `sources/preprints-tree.json`. Each retained excerpt also has a detached SHA256 in the authentication JSON. No repository snapshots, forbidden live-review outputs or copied historical review files were used.
