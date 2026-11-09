# r159 investigator handback

**One kernel-checked candidate refutation; no acceptance or count change.** Exactly 20 reserved IDs are recorded in results.json. No child agents, git, shared-ledger edits, browser tabs, external messages, publication or uploads.

## Candidate 365453

The literal graph **2(3P₂ ∨ O₂)**, with 16 vertices and 30 edges, admits no local antimagic edge labeling with at most 3 induced weights. This refutes r=s=1,m=2 in Lau–Shiu Conjecture4.1. The actual 2025 published version retains the claim on p205; its statement was visually verified.

The ordinary argument splits on whether both components' null vertices have the same weight. Equal roles give a parity contradiction. Different roles give six endpoints with common weight Z. Their incident edges comprise six matching labels and twelve distinct join labels. Total-label and component identities force incompatible bounds on Z. See PROOF-365453.md.

Formal endpoint: R159.source_conjecture_4_1_counterexample in lean/Antimagic.lean. It universally forbids every bijective labeling of the fixed graph, not a surrogate statistic or bounded diagnostic. Direct adjacency, complete unique edge enumeration, bijection equivalence and incidence formulas are included.

Fresh extracted strict rebuild, explicit-module leanchecker and transitive audit passed: 97 local declarations including generated ones; 6845 transitive declarations; only propext, Classical.choice, Quot.sound. Fresh rebuild sampled RSS≈2.30GiB, checker≈1.75GiB, audit≈2.20GiB. Prescribed pinned dependency caches reused read-only; no complete upstream rebuild claim.

Packet: lean-packet.tar. Receipts: fresh-replay/logs/. Audit: fresh-replay/outputs/audit.tsv. Machine validation and hashes: outputs/validation.json.

**Independent root review required:** mathematics, source fidelity, formal endpoint, novelty, significance and credited-family independence. SOURCE-COMPARISON.md records bounded primary-body comparison. CCO's older C₃⊔C₃ theorem is a relevant parity precedent but does not handle our essential mixed-role case. Whether the extension clears the campaign's routine-consequence threshold is explicitly left to root.

## Other nineteen dispositions

| IDs | Disposition |
|---|---|
|358202|Current source prints its own t=2,3 refutation.|
|359423|Public full proof, Aliste-Prieto–Martin–Wagner–Zamora Theorem 6; body read.|
|360570|Public Aug 17, 2026 ProbXiv counterexample; full proof read.|
|365534|Public Oct 27, 2026 proof, arXiv:2610.36620 Theorem 1.3; proof read.|
|357237,357760,358412,363418,365685|Exact searches; no substantive counterexample.|
|360121,365359,365651|Positive small exact-cover diagnostics; full claims hard/partly classical.|
|358641|MathDB Johnson/intersection differs from source Kneser/disjointness; source formulas also need repair.|
|364089|Hard toroidal list-coloring problem; source already enumerates substantial region.|
|364453,364679,365135,365891,366137|Topological, unbounded-constant, categorical, eventual analytic or infinite-graph scopes; no suitable finite mechanism.|

## Actual searches

- 357237: 994 connected atlas graphs, orders3–7, all t=3..n, exact rational weights from cycles; 240 seeded samples, orders8–13, 40 per order, t=3..min(n,6), exact subset-cycle DP. No inequality failure. No credit for t=2 wording/equality corrections.
- 357760: 996 connected atlas graphs through order7; exact arboricity and induced-tree edge-color witnesses within 2 arb.
- 358412: 996 connected atlas graphs through order7;6,240,824 orientations modulo reversal. Another 80 seeded connected order 8/9 graphs,182,016 orientations modulo reversal. Unconstrained maximum equals best balanced maximum throughout.
- 365685: 994 connected atlas graphs, orders3–7, k=3..min(n,5), excluding K_k; 400 further seeded connected samples, orders10,15,20,30,40, k=3,4,5, sparse/dense and planted-clique chains/trees. Every SAT coloring independently checked on all clique-neighborhood constraints.
- 363418: 171,078 unordered subsets across Z25,Z5×Z5,Z63,Z3×Z21,Z41 at recorded(m,s); no perfect sets. Every nonzero-element subset of each specified size included.
-Decompositions: all 13 atlas trees of orders2–6 decomposed corresponding K_n,n; all 6 admissible even-cycle pairs with v∈{4,6,8} had balanced covers; all 8 connected simple r-graphs through order6 had matching decompositions. These old small constructions are not discoveries.
- 365453:initial SAT diagnostic timed out at 110 s; no UNSAT claim. Subsequent proof is solver-independent.

Scripts, inputs, full outputs and failed-run logs retained. Early dependency probes and an orientation-array crash were corrected; failed runs are not coverage. A first broad-import Lean attempt hit its own 3.5 GB threshold; narrower imports succeeded without increasing caps.

## Provenance and limits

raw/ preserves exact JSONL lines including newlines. extracted.json records one-based chunk lines and chunk/raw/statement SHA256 values. All 20 current source abstracts/PDFs have dated hash receipts. Historical ID/title searches, both ledgers and inherited accepted/excluded context read; numeric substrings in large dumps are not prior target reviews.

Registry HEADs:OpenAI4eaee87548250b2682affda7d05d947c05554bae;Omega d9880e9f2c329bb3db982f33791419d5d90126b9. Complete Omega D5/Problems trees obtained. Path screens are not global proof reading or novelty guarantees.

Numerical Python, SAT, C searches, Lean/checker calls used the lane-local watchdog: 2 CPU affinity, 120 s CPU, 140 s wall,MALLOC_ARENA_MAX=2, 6 GiB sampled aggregate RSS kill threshold; every direct Lean call used-M3500. TMPDIR, caches, builds, replays are lane-local. Sampling is not a cgroup-level transient memory guarantee. No background task remains.

Concrete candidate and bounded dispositions only: no corpus-wide technical review, exhaustive prior-art or independent acceptance claim.
