# Expanded corpus r59 handback

One full Lean refutation candidate is ready for independent review: **MathDB 364205**, the largest rigid facet conjecture. A maximal rigid diameter-5 subset of the 8-dimensional Hamming cube has **34 vertices**, exceeding the conjectured 32. The endpoint is `MathDB364205.literal_source_refutation` in `formal/Signed.lean`. It uses the literal integer-sign cube, with an explicit equivalence and distance-preservation proof from the Boolean computation. All semantic bridges are proved.

**Zero acceptance credit is claimed. The campaign remains 4/20 beyond the prior 39.** Independent fidelity, novelty, significance, paper and root acceptance work follows separately. This lane does not selfaccept or publish.

## Deliverables

- `results.json`: exactly 40 ID-keyed dispositions, with exact literal text, corpus provenance, review depth, inherited matches, outcome and remaining gates.
- `raw/`: exact original JSONL lines including their terminating newlines; chunk hashes, one-based line numbers, raw-line hashes and statement UTF-8 hashes are in `extracted.json` and `results.json`.
- `PROOF.md`: ordinary finite proof and exact source correspondence for 364205.
- `ATTEMPTS.md`: sustained cube, Pell and Laplacian routes, failed approaches, precise hard gap, and operational failures.
- `certificate.json`: independent coordinate-level checks and all 256 farthest-point witnesses.
- `364205-proof-source.zip`: source-only Lean packet with reproducible managed replay scripts, no prebuilt local oleans.
- `replay/replay-result.json`: fresh extracted sanitized strict replay PASS. The extracted run compiles the mathematical sources and audits all 33 local declarations, including generated declarations. Only propext, Classical.choice and Quot.sound appear transitively. An additional module-origin inventory verifies the namespace inventory covers all declarations originating in Cube and Signed.
- `sources/`: dated HTTP status, URL and SHA-256 receipts; fetched primary bodies and text extracts. No fabricated source hashes.
- `scripts/` and `logs/`: reproducible extraction, bounded diagnostics, independent checker, managed Lean invocations and complete outputs. `replay-initial-failed/` preserves the first extracted audit failure; subsequent corrected replay is separate.

## Actual review depth and mathematical outcomes

All 40 exact literals were read. Three reserved claims received primary-definition and theorem/proof-body investigation: 364205, 364596 and 365143. This is **not** 40 primary reviews. The chordal-ring body was downloaded but its three conjectures were not primary-reviewed. All other claims retain explicitly shallow dispositions or reported-resolution leads, with no claims that unread proofs establish exclusion.

The cube candidate settles the entire universal conjecture negatively, through a central-domain counterexample. It is not a parameter-instance affirmative result or a wording correction. No exact optimum, minimal witness, asymptotic improvement or additional family credit is claimed.

Pell 364596 has an existing exact public registry theorem. The full `PellPartialSumMaxIndex.result` body and its Pell recurrence and companion-coprimality definitions/proofs were read. Its four greatest-index clauses directly cover the meaningful source Conjecture 18. This is not a novel result from this lane; no local rebuild of the external registry theorem is claimed.

Laplacian 365143 remains unresolved. The source odd-set-cover proof loses precisely floor(k/2); neither the known bipartite bridge nor odd-clique constructions remove that loss in the literal range. The bounded spectral diagnostics found no certified counterexample. Details and the remaining structural lemma are in `ATTEMPTS.md`.

The history search covered ID/title matches in batch prose, results, reviews and ledgers, excluding raw routing inventories. Most matches were administrative reservation entries or numeric substrings in unrelated hashes. The meaningful inherited match is 365145: r130 already reports its Z-curve screen without promotion. That old screen is retained and no repeat investment performed. No other inherited mathematical exclusion by these exact IDs/titles was identified in this bounded search. Absence from this search is not global historical nonreview. A subsequent exact source-ID/title history screen for the cube paper found no old route.

## Registry and prior-art limits

At 15:51 UTC on 2026-11-01, live `/commits/HEAD` returned OpenAI/math `4eaee87548250b2682affda7d05d947c05554bae` and Omega `759ea620b15c60a4f0c74e6b55227446439a74cd`. The current nonrecursive root trees bind OpenAI preprints `3f56f68a176b4494c346091ea0a319651bc217ec`, Omega D5 `dc94715eb7700d822e91cbf264fd1efbbe36906e`, and Problems `0b45ced5e033ab15556c8f7a9177458bc5ad1de6`. Complete byte-hashed preprint/D5 scopes were reused; Problems was fetched afresh. The truncated root cache was not treated as a complete listing. No `/commits/main` route was used.

Path screens are not proof-body review. The cube screen found general hypercube, induced-subcube, determinant-inequality and unrelated Hamming leads. The complete short general-hypercube proof was read; induced-subcube and determinant-inequality theorem statements and definitions were read, not their complete proofs. These inspected statements do not assert the rigid-facet extremal claim. Remaining registry proof bodies and historical deletions were not exhaustively read.

The actual v1/v2 source definitions and Conjecture 1 were read. Selected construction proof portions and the product proof were inspected. Bounded live arXiv searches found two later papers, 2606.20784 and 2605.00705. Their relevant theorem statements and selected proof bodies concern group actions on homology and cohomological/connectivity bounds; no complete rigid-facet counterexample bridge was located in that inspection. This does not certify all their proofs, all citing literature, a journal version, errata or worldwide priority. The source landing page lists v2 and no journal reference was located there. All these limits require independent review.

No MathDB/Palomar denied route, web/connector token failure, Crossref rate-limited route, browser tab, account action, author contact or external message was retried or used.

## Environment, reproducibility and trust

Actual binary: `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`, Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`. Mathlib uses the read-only cached packages from the 2026-10-14 formal project, pinned at `d13f23b723b8a846827a245b89c10fc7d3f11612`. The final extracted invocations clear the environment and set only explicit search paths, PATH and locale; use `-j2` and `-DwarningAsError=true`; and never use sorry, admit, new axioms, unsafe, native_decide or ofReduceBool in mathematical sources. Kernel `decide` proves the finite facts.

The diagnostic audit intentionally names generated auxiliaries, so only its auxiliary-reference linter is disabled. No proof-module linter is disabled. Warning-as-error remains enabled. The safety audit rejects unsafe/partial declarations and local axioms.

Managed expensive calls use at most 2 CPUs, CPU 120 seconds, wall 140 seconds, address space 12 GiB and sampled process RSS ceiling 6 GiB. Final replay peak sampled RSS is about 3.3 GiB. Initial wrapper-based runs monitored the Python wrapper rather than its Lean child; this limitation is retained honestly. The final wrapper uses exec so the monitored process is Lean. Sampling is not aggregate cgroup enforcement and cannot exclude transient peaks. Initial thread-creation and elaboration failures are logged, not passed off as checks.

External prebuilt dependency oleans are trusted. No full upstream rebuild or source-to-olean attestation is claimed. All 20 normalized corpus chunks match their manifest hashes, and all five reservation input bindings match; the campaign ledger remains mutable administrative context. The inventory is 95,675 historical distinct IDs, including 87,990 retrieved records and 7,685 stubs. The old 10,000 routing queue is not the full corpus.

Reproduce by extracting the proof ZIP into a fresh directory, creating its `logs/` subdirectory, and running `python scripts/replay.py` with the recorded binary and cache paths available. No background work remains at handback.
