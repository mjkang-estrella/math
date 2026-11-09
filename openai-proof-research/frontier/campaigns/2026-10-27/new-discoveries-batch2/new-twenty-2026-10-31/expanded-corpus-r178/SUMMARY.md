# r178 research handback

One candidate survives as a full ordinary proof with a literal general Lean endpoint: **MathDB 360905**, intermediate values of orientable total domination. It is **pending independent review and root acceptance**, with zero self-awarded credit. Its short elementary nature gives material credit risk under this campaign's routine-observation exclusion. No global novelty claim is made.

The other nineteen reserved IDs have individual dispositions: eight excluded by prior results or source-scope corrections, eleven parked with explicit gaps. Exactly twenty ID-keyed entries, literal statements, corpus line/chunk/raw/statement hashes and source receipts are in results.json. Raw corpus bytes including newline are preserved in raw/.

## Candidate

CANDIDATE.md contains the complete proof and source-fidelity map. The key lemma compares two valid orientations: if every disagreeing arc is the unique incoming arc at its head, every total dominating set of the first orientation also dominates the second. Otherwise a disagreeing edge can be reversed safely, increasing the minimum number by at most one and decreasing disagreement. Strong induction gives interpolation between any two attained values.

The original source is Hansen–Lai–Yue, JCMCC 29 (1999), 159–181, final conjecture on page 181. Pages 179–181 were visually read from the scanned PDF; Theorem 14 proves the complete-graph case by a different vertex-deletion argument. Anderson–Dravec–Johnston–Kuenzel arXiv:2311.16307v1 restates it as Conjecture 3.1 and proves the complete-bipartite case. The later Blázsik–Nagy arXiv:2411.04560 and 2026 journal version characterize DOM_t=n−1; introductory definitions, theorem and relevant proof cases were read. Their unique-in-neighbor observations are elementary ingredients, but no general orientation-comparison interpolation proof was found in the inspected bodies. This bounded non-finding is not worldwide priority certification.

Lean endpoint: `OrientableTotalDomination.conjecture_true` in lean/Interpolation.lean. The definitions quantify arbitrary finite vertex types and all valid orientations, use literal incoming total domination, actual minimum cardinalities, and actual extrema of the attained spectrum. The result includes disconnected graphs. No auxiliary connectivity hypothesis, bounded instance, surrogate invariant or assumed semantic bridge occurs.

Validation:

- Strict Lean 4.34.1 compilation passes.
- A fresh extracted source rebuild with sanitized environment passes.
- `leanchecker Interpolation` passes with the module explicitly supplied.
- The audit checks all 38 module-owned declarations, including generated declarations, for unsafe/partial/executable substitutions and transitive axioms. Only propext, Classical.choice, Quot.sound occur.
- The cached mathlib revision is d13f23b723b8a846827a245b89c10fc7d3f11612, verified against the read-only lake manifest. Dependencies were not rebuilt in full; cached upstream oleans remain a trust limitation.
- Independent fidelity, prior-art/significance review and root acceptance are still outstanding. The present lane performed no independent-agent review and wrote no paper claiming acceptance.

Lean-packet.zip contains the theorem source, audit source, manifest and replay instructions. Full development failures remain in logs: a broad Mathlib import hit the RSS watchdog; a subsequent default-thread attempt failed to create a thread. Narrow imports and explicit `-j2 -M3500` compile within about 1.8 GB RSS. No timeout-killed background process was restarted.

## Exact computational coverage

- 360905: all connected labeled graphs of orders 3,4,5,6 with a cycle (1,22,603,25408 graphs), and all valid orientations (2,122,16168,5545668). Every spectrum is an interval. These diagnostics are not used as a substitute for the general theorem.
- 361017: all 466938 choices of nonempty move set of size at most three, maximum at most 12, and all full-length Boolean seeds. No positive-preperiod orbit satisfies the extension premise. A second exact sweep checks all unseeded move sets through maximum 65. The extension checker examines transient/seed windows and periodic residues, including enough k values to stabilize all comparisons; the finite bound is explained in SEARCH-NOTES.md. See outputs/subtraction-*.json.
- 360626: all labeled co-chordal graphs on 3–6 vertices (8,61,822,18154) and all nontrivial r; additionally the n=7 edge-mask prefix through 911740 inclusive, containing 236671 co-chordal graphs and 946684 r-tests. The n=7 coverage is explicitly partial. Exact recursive simplicial-maximal-subcircuit deletion finds no counterexample. See outputs/cochord-7.json.
- 360182: all root-zero configurations on Q2 with total at most 20 (10626 configurations), and Q3 with total at most 12 (125970 configurations). An exact terminating search of pebbling moves tests every overweight configuration. No unsolvable overweight case. The current source's full reciprocal-distance Conjecture 2 is still conjectural; the record's solved reference was not trusted.
- 360427: all 64 rotation-normalized length-eight templates with diamonds at positions 0 and 4, recovering four known n=4 binary upcycles. No n≥16 existence or nonexistence assertion.

No irrelevant finite sweep was used to claim a result about all stochastic channels, eventual stability, an unspecified asymptotic constant, infinite prime configurations, all permutation coefficients of building quotients, or all real interval colorings. Those items received source-backed parked dispositions. Known resolved Boolean, hook, poset and tournament targets were excluded before discovery computation.

## Literature and registry screen

Source abstract pages and every listed arXiv PDF version for all twenty records were retrieved with TLS verification and dated status/hash receipts. The version-specific conjecture contexts are in outputs/*-source-context.txt; review depth is stated per ID. Downloading all versions is not an assertion that every theorem in every version was fully reviewed.

Literature and citing-work searches preceded each exhaustive computation. Follow-up 2026 searches are also saved. The source's own results and companion results removed several apparent targets: Potapov's Boolean refutation; Nambi–Kumar's intended residual-hypergraph positivity theorem; Crew et al.'s tournament results; Bastide et al.'s cube-width theorem; Amdeberhan et al.'s hook formula; and Alipour et al.'s relative-packing counterexample. Definitions and actual decisive proof bodies were inspected rather than relying only on abstracts.

Registry HEADs fetched using /commits/HEAD:

- Lean Pool: 01db1d7049cf9668bda1e9e106875ee1278b43e6; projects and all ten candidates files downloaded.
- OpenAI/math: 4eaee87548250b2682affda7d05d947c05554bae; unchanged HEAD, byte-hashed cached full preprint path scope reused.
- Omega: f47ba12c91744e87f89f05ef1db7df1f6ddd9f95; fresh complete D5 and Problems path trees retrieved.

Exactly eight GitHub repository searches were spaced by eight seconds; all returned HTTP 200. The query for orientable total domination had no repositories. No matching target proof was found in the screened scope; generic Post/Schur/interpolation keyword hits are not target matches. The screen is bounded and is not exhaustive proof-body clearance. See outputs/registry-screen.json.

No denied HTTP host was retried; sources/denied.json is empty for this lane's direct fetches. No browser, account, upload, external message, git operation, shared ledger/index mutation or child agent was used. All created artifacts are lane-local. Every numerical/Lean run used the two-CPU, 120 CPU-second, 140 wall-second, approximately 6 GiB process-group RSS wrapper. The wrapper is a sampled watchdog, not a cgroup or an instantaneous RSS guarantee. No background job remains.

## Reproduction

Use real script paths from the lane, e.g. `python3 -I scripts/limited.py NAME python3 -I scripts/SCRIPT.py ARGS`. Every process is sequential and logs its full output and resource receipt. SEARCH-NOTES.md explains the finite encodings. REPLAY.md gives Lean replay commands. results.json retains exact source receipt references and honest remaining gaps. This lane changes no campaign count.
