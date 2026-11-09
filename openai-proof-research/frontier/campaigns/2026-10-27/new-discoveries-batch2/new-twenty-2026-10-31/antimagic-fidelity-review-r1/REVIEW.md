# Independent formal-fidelity and final review: MathDB 354228

**Recommendation: PROCEED TO ACCEPTANCE PACKAGING. This is a review, not acceptance; credit remains 0 and root decides.**

Reviewed archive: `../antimagic-formal-r7a/source.zip`, SHA-256 `987233b0343fb9855f659eefedaf28bc2a91576cf5c6c3a50342671895d3d175`. Review performed independently, with no children, git operations, external messages, publication, uploads or browser tabs. All new files are in this lane. The other lanes and pinned toolchain/packages were read-only.

| Gate | Verdict | Finding |
|---|---|---|
| A | PASS | Literal graph definitions, nonempty least spectrum, source structural certificate and arbitrary-tree isomorphism bridge meet ruling (i)-(iv). Totalized graph definitions cause no endpoint domain mismatch. |
| B | PASS | Corrected fresh extraction: all 54 strict module builds and all 54 explicit-module leanchecker calls pass. Independent metadata audit and both endpoint axiom reports pass. Preliminary run excluded. |
| C | PASS | Exact frozen construction predicates are fully discharged; before/after manifests and earlier archive source bytes agree with final extracted modules. |
| D | PASS | Independent frozen-formula transcription passes 23 parameter cases, including all 15 required cases; negative controls detected. |
| E | QUALIFIED_PASS | No resolution found in bounded arXiv abs / OpenAlex refresh; listing failures and two unread closed-access leads remain. Attribution in final packet is correct. |

## A. Fidelity and C. architecture

Statement and architecture notes (independent reading)

Source: published fi9349.pdf, pp. 100, 102-103, 111-112; pdftotext evidence/published.txt lines 49-88, 214-238, 600-640. Expanded corpus source is HTML/text, not a PDF; the PDF used is the immutable earlier-review cache. Exact hashes are in source-before.sha256 and additional-input-before.json.

AntimagicBasics.lean lines 10-30: an edge is an unordered Sym2 member of SimpleGraph.edgeSet; the equivalence to Fin cardinality, shifted by one in weight, is exactly a bijection onto 1..|E|. Each incident edge is summed once. IsLocal quantifies adjacent pairs only. colorCount is the image cardinality on all vertices. spectrum ranges over local labelings, and chiLA is its Nat infimum. Empty spectra have a totalized value, but IsLeast in both final endpoints explicitly exhibits a member, so no empty-spectrum artifact is possible. numLeaves counts graph degree one. NoK2Component says no adjacent pair both have degree one, equivalent to excluding K2 connected components in a simple graph.

The definitions are totalized beyond the paper's standing graph domain: NoK2Component and no-isolated-vertex conditions are not parameters of Labeling or chiLA. This causes no mismatch on the endpoints. The model is connected, has t children at the root and at least three vertices, every nonroot has a parent, and an internal parent has degree at least t>=2. Thus it has no isolated vertices or K2 component; every arbitrary FullTree is isomorphic to it. A standalone claim for arbitrary excluded graphs would need domain hypotheses, but none is asserted here.

AntimagicModel.lean lines 7-28: vertices (h,i), 0<=h<=n, i<t^h, with child index division by t. The root is depth zero. Edge depth equals the lower endpoint's depth, agreeing with Definition 1.4. FullTree lines 39-52 records actual treehood, root iff depth zero, adjacency exactly oriented child edges, incrementing depth, unique parent, depth bound and exactly t children below n, zero at n. For t>=2, a vertex below n cannot be a leaf. Repeatedly taking a child reaches n, so n is attained. Conversely any finite rooted tree in Definition 1.3, with common leaf depth n, supplies these fields: unique parents and connectivity/acyclicity are tree properties; every vertex below n is nonterminal, and child edges define graph adjacency. DecidableRel is available on finite vertex sets. No ordering of children is assumed; the bridge chooses it by finite equivalences. An unrooted graph with a suitable root satisfies the conclusion by choosing that certificate. Depth zero is excluded by source Definition 1.1's no-isolated-vertices condition, even though the MathDB literal does not restate that standing condition.

ModelStructure is discharged at Antimagic2Structure.lean:172, for every t>=2,n>=1, with its root/depth/child equality fields. This supplies an explicit witness and rules out contradictory hypotheses/vacuity. modelLeaves (Antimagic2Leaves.lean:57), using degree_one_iff at :39 and bottomEquiv at :46, identifies graph leaves with row n, including the nonleaf root at depth one. ModelBridge (AntimagicFinal4B.lean:6) uses that very certificate and fullTreeIso (Antimagic4BBridge.lean:154), whose layers/step construction preserves parent-child edges. AntimagicIso.lean:10,26,34,48,58,67 transports weights, locality, counts, spectra, leaves and chiLA.

AntimagicFinal7A.lean:6 and :11 instantiate the frozen Round6A endpoint with Round7A.binaryHigherConstruction, and the graph endpoint additionally with Round4B.modelBridge. Round6A (AntimagicFinal6A.lean:6,14) supplies nonbinaryHigherConstruction from Antimagic6AWeights.lean:108, obtained by exact NonbinaryWeightCompletion (AntimagicFinal5A.lean:9). That predicate concerns the actual constructed edge equivalence, not abstract weights; its formula-realization clause is retained by nonbinaryHigherConstruction_of_weights at :13. Round4A endpoints supply depthTwoConstruction (Antimagic4ADepthTwo.lean:130). Round3.remaining_iff (AntimagicFinal3.lean:23) is the exhaustive split into depth two t>=4, higher t>=4 and higher t=2. Round2.construction_of_higher (AntimagicFinal2.lean:13) adds star_construction (Antimagic2Star.lean:99) and binary_construction (Antimagic2Binary.lean:39). The base AntimagicFinal.lean:36,44 invokes the original LowerBound and Construction, and for arbitrary trees also ModelBridge and ModelLeaves. lowerBound (Antimagic2LowerBound.lean:39) proves the leaf argument with a maximum-labelled edge and a second positive edge at its parent. It even does not need locality, strengthening the bound rather than weakening it.

The binary completion (Antimagic7AConstruction.lean:143) proves exactly Round3.BinaryHigherConstruction: for each n>=3 an edge labeling realizing the frozen label on every Child edge, properness and exact count. Its proof assembles higherLabeling with higher_local and higher_colors, and the latter proves an upper bound by leaf-range containment plus one constant and invokes lowerBound for equality. These are unconditional theorems, with no residual higher-construction hypothesis. Qualified namespaces distinguish earlier conditional endpoints from final unconditional ones; there is no redefinition of Antimagic.Construction, ModelBridge or the other frozen Props.

Attribution: AntimagicLabel.lean:43 and :67-83 and PROOF.md:33-37 credit source Figure 5, published Lemmas 2.2/2.9 for nonbinary depth two, and Conjecture 6.1. Figure 5 has leaf labels [3,2,5,6] visually, while frozen code has [2,3,6,5]; these are the same rooted labeling after swapping siblings, not a different construction. Published Lemma 2.10 (evidence/published.txt:229) is the even-number-of-tuples obstruction, cited in the source at :592. It does not preclude the symmetric-shell replacement. The old discovery proof's HTML lemma numbers must not be reused as published numbering in a future manuscript. This final source packet's attribution is correct; no final publication is made by this review.

## B. Independent replay and process discipline

The driver is my own `scripts/replay.sh`, with dependency order computed by `scripts/prepare.py`; no formalization-lane driver was executed. `scripts/extract.py` checks the exact archive hash, absolute/parent/backslash paths, file types/links, file sizes and absence of bundled olean/ilean/shared libraries before extracting into a new empty directory. Each local module is compiled separately with Lean 4.34.1, `-j1 -M3500 -DwarningAsError=true`, followed by `leanchecker <explicit module>`. Mathlib's read-only `.git/HEAD` was inspected without git: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

A wrapper defect was discovered in the preliminary run: GNU timeout created its own process group, so the monitor could miss the heavy child. That run was stopped and preserved under `preliminary/`, and is excluded from validation. The extraction, order preparation and complete replay were repeated with corrected `timeout --foreground`. Every process in the qualifying run used the same caps: taskset CPUs 0 and 1, CPU 120 seconds, wall 140 seconds, aggregate process-group RSS watchdog 6 GiB, MALLOC_ARENA_MAX=2, lane-local TMPDIR/cache. No limit was raised. `evidence/corrected-process-groups.txt` records the corrected grouping. The preliminary mistake is disclosed rather than claimed compliant retroactively.

All 54 builds and 54 checkers passed in the qualifying run; complete output is in `logs/build-*.log`, `logs/check-*.log` and `logs/replay.log`. Both final endpoints report exactly propext, Classical.choice and Quot.sound. My separate `ReviewAudit.lean` enumerates all imported Antimagic-module and Antimagic-named constants, rejecting unsafe, partial, implemented_by, extern, added axioms and _unsafe_rec metadata. The source scanner independently excludes nested comments and strings before searching sorry, admit, axiom, native_decide, ofReduceBool and implemented_by. Results are in `evidence/local-metadata.tsv`, `evidence/source-scan.json` and `logs/independent-audit.log`. The audit module itself was strictly compiled and explicitly checked. Imported frozen audit modules additionally perform dependency-closure audits; their claims were not substituted for the independent local metadata check.

Local metadata declarations checked: 1434. Peak per-process RSS over module builds/checkers: 3317368 KiB.

The before/after input maps include the archive, all extracted Lean modules, source/corpus/ruling inputs, recorded inheritance manifests and earlier archives/results; all agree. `evidence/hash-chain.json` records exact checked paths and module counts, independently comparing earlier zip member bytes and lane files against the final extraction. The MathDB literal is corpus chunk 0008, exact line 3529, copied including its newline to `evidence/mathdb-354228.raw.jsonl`; its raw-line hash and full chunk hash are recorded, not reconstructed from JSON.

## D. Independent numerical spot-check

My `scripts/spotcheck.py` is a new direct transcription of AntimagicLabel.lean, including truncated natural subtraction, all depth-two branches, sigma and the binary row-two patch. It explicitly constructs graph edges and accumulates weights/degrees. It checks the entire label interval, every adjacent pair, leaf count and exact number of colors. It imports or executes no earlier checker. Run capped with python3 -I; `logs/spotcheck.log` and `evidence/spotcheck.json` preserve results.

All 23 cases pass. Depth ranges: t=2: n=1..8, t=4: n=1..8, t=6: n=1..7. This includes every required t in {2,4,6}, n in {1,2,3,4,5}. Larger cases stay below 500,000 edges. Removing the binary patch fails properness at (2,3); duplicating a label fails bijectivity at (4,3). These diagnostics support the review and are not used as a proof.

## E. Prior art and attribution

Bounded refresh on 2026-11-04 UTC (local date 2026-11-03). HTTP receipts include URL, UTC time, headers, status, body and stderr in downloads/<request>/; no cookies, browser, challenge bypass, TLS relaxation, search API, or forbidden service was used.

arXiv abs/2204.04479 and abs/2610.22783 returned 200. The latter is Brondani-Franca's October 2026 counterexamples to the general leaf conjecture; it does not announce resolution of the even complete-full-tree conjecture. The earlier review already read its body. arXiv listing requests /list/math.CO/recent?show=200 and /list/math.CO/2611 returned 400 and 404. Therefore this refresh does not certify complete arXiv listing coverage. These are failures, not evidence of absence.

OpenAlex search local antimagic, publication date >=2022-01-01, returned 319 records in two pages. All titles are preserved in evidence/oa-titles.tsv; many are irrelevant educational or other-invariant records. Searches antimagic t-ary (25 results) and antimagic binary tree (88 results) identify the source and no apparent resolution. This is bounded metadata/abstract screening, not a body-level exclusion of every paper. OpenAlex cites:W4223652911 still returns three citing works (the 2023 Sarath-Prajeesh trees paper, a 2024 local-edge invariant paper, and a 2024 graph-operations paper); cites:W7214805693 returns none. Paul-Raul 2025, Local antimagic labelling for trees (W4409438829), concerns a linear-time iterative algorithm for existence of local labelings, not an optimal color count according to its abstract. No new complete-full-even-tree resolution was identified.

Named lead Sarath-Prajeesh 2023: OpenAlex W4382053216, DOI 10.1109/ICEEICT56924.2023.10157500, closed access, no OA/fulltext location. The abstract covers diameter-3 trees, certain diameter-4 trees and complete bipartite graphs of opposite part parity. One DOI attempt returned HTTP 202 with an empty body; no retry. Exact diameter-4 families remain unread. T(t,2) has diameter 4; for n>=3 the diameter is 2n>=6. Thus the advertised scope could overlap depth two but cannot establish the full higher-depth result.

Named lead Premalatha-Arumugam-Lee-Wang: OpenAlex W3044143231, DOI 10.1080/09720529.2020.1772985, Local antimagic chromatic number of trees - I, online 2020 / journal 2022. OpenAlex reports closed access, one publisher location, no OA fulltext. Abstract says several families of trees without identifying them. One DOI attempt returned 403; no retry, alternate publisher challenge route, or bypass. Its body remains unread. Its actual scope cannot be bounded to depth two merely from that abstract; the root ruling's earlier assessment is retained as an assessment, not independently proved by this refresh. This is a residual prior-art limitation.

Attribution checked against the published PDF: Figure 5, Lemmas 2.9 and 2.10, Conjecture 6.1. Final PROOF.md lines 33-37 correctly credits Figure 5 and source ingredients for nonbinary depth two; AntimagicLabel.lean lines 43,67-83 agrees. Future acceptance packaging should use these corrected published labels rather than the old discovery proof's HTML numbering. Significance/novelty remains modest and bounded, as root already ruled; kernel replay cannot establish novelty. No acceptance or credit is asserted.

## Per-module timings and peak RSS

RSS is /usr/bin/time maximum resident set in KiB for each process invocation; the independent watchdog enforces the aggregate process-group limit. Times include the capped command. Full machine-readable rows are in `evidence/module-timing-rss.json`.

| Module | Lean s | Lean RSS KiB | Checker s | Checker RSS KiB |
|---|---:|---:|---:|---:|
| AntimagicBasics | 2.51 | 1807284 | 3.80 | 1534400 |
| AntimagicModel | 2.97 | 1964116 | 3.37 | 1675592 |
| Antimagic2Structure | 2.07 | 1975384 | 3.47 | 1677988 |
| Antimagic2Leaves | 1.77 | 1964372 | 3.36 | 1678284 |
| AntimagicLabel | 2.42 | 1957048 | 5.07 | 1674096 |
| AntimagicIso | 1.50 | 1804844 | 4.00 | 1532576 |
| AntimagicFinal | 3.03 | 1952636 | 6.15 | 1674480 |
| Antimagic2LowerBound | 2.75 | 1966012 | 3.70 | 1678996 |
| Antimagic2Incidence | 3.02 | 1963280 | 2.97 | 1675048 |
| Antimagic2Star | 1.97 | 1976820 | 4.23 | 1684264 |
| Antimagic2Binary | 1.84 | 1974464 | 3.74 | 1695688 |
| AntimagicFinal2 | 1.59 | 1965708 | 3.84 | 1683396 |
| Antimagic2Finite | 2.23 | 1969836 | 3.99 | 1681816 |
| AntimagicRegression | 5.96 | 2193840 | 3.82 | 1676000 |
| Antimagic2Regression | 29.17 | 3317368 | 17.03 | 3050312 |
| Antimagic2Audit | 16.39 | 2463320 | 4.18 | 2072260 |
| Antimagic3DepthTwo | 14.20 | 2144032 | 5.20 | 1741976 |
| AntimagicFinal3 | 1.67 | 2028232 | 4.27 | 1727892 |
| Antimagic3Audit | 18.65 | 2522364 | 3.94 | 2120204 |
| Antimagic4AHigh | 7.24 | 2097020 | 4.15 | 1743248 |
| Antimagic4ABijection | 2.47 | 2053644 | 3.83 | 1732096 |
| Antimagic4ADepthTwo | 4.25 | 2056740 | 6.27 | 1734940 |
| Antimagic4ALeafBlocks | 8.21 | 2100556 | 5.25 | 1738548 |
| Antimagic4AShell | 3.79 | 2055984 | 3.58 | 1737452 |
| AntimagicFinal4A | 1.83 | 2023780 | 3.37 | 1731208 |
| Antimagic4AAudit | 18.85 | 2528144 | 3.61 | 2125640 |
| Antimagic4BBridge | 3.20 | 1973152 | 3.56 | 1678340 |
| Antimagic5AShellRows | 2.39 | 2044176 | 3.53 | 1738016 |
| Antimagic5AInternal | 2.75 | 2056564 | 3.80 | 1738884 |
| Antimagic5ALeafParameters | 3.02 | 2059224 | 6.78 | 1743580 |
| Antimagic5ARowSums | 4.05 | 2065280 | 5.64 | 1742288 |
| Antimagic5AVertices | 2.18 | 2047924 | 3.83 | 1740936 |
| Antimagic5ALeafRow | 5.05 | 2048392 | 3.61 | 1739232 |
| Antimagic5ABijection | 2.23 | 2047360 | 5.66 | 1739776 |
| Antimagic5AWeights | 2.51 | 2041200 | 5.92 | 1740192 |
| AntimagicFinal5A | 1.76 | 2034536 | 4.19 | 1735980 |
| Antimagic5AAudit | 17.31 | 2533140 | 4.10 | 2130612 |
| Antimagic6ABounds | 2.62 | 2058476 | 3.91 | 1744252 |
| Antimagic6ARoot | 8.78 | 2083556 | 3.87 | 1751300 |
| Antimagic6AWeights | 3.27 | 2066052 | 5.00 | 1743684 |
| Antimagic6APatch | 2.38 | 2068228 | 5.87 | 1756632 |
| Antimagic6ABinaryInternal | 3.04 | 2077240 | 4.36 | 1753444 |
| Antimagic6ABinaryWeights | 2.67 | 2058000 | 4.27 | 1753356 |
| AntimagicFinal6A | 1.49 | 2034768 | 3.31 | 1741224 |
| Antimagic6AAudit | 18.73 | 2542752 | 4.49 | 2135672 |
| Antimagic7AParameters | 1.58 | 2047908 | 3.66 | 1743516 |
| Antimagic7ALeaves | 2.03 | 2057004 | 5.29 | 1747924 |
| Antimagic7ABijection | 2.36 | 2062272 | 3.54 | 1746792 |
| Antimagic7AWeights | 2.23 | 2056624 | 4.70 | 1749036 |
| Antimagic7AConstruction | 3.05 | 2078032 | 3.93 | 1749912 |
| AntimagicFinal4B | 2.02 | 2019824 | 4.27 | 1728268 |
| AntimagicFinal7A | 2.31 | 2037424 | 3.41 | 1744248 |
| Antimagic7AAudit | 18.39 | 2545448 | 3.81 | 2138728 |
| Audit | 15.00 | 2457600 | 6.07 | 2064160 |

## Handoff

No mathematical or formal fix is required by gates A-D. Package the final unconditional Round7A endpoints and retain corrected published attribution, all replay evidence and gate E's limitations. Do not advertise the bounded search as a proof of novelty. Root alone decides acceptance and any credit.
