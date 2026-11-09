# Fresh corpus r6 — 40 literal reviews, no discovery proposed

**Outcome:** all 40 reserved literal statements reviewed; 11 records received primary theorem/proof-body review. One complete Lean coordinate refutation of MathDB **327346** was obtained, but it is **not recommended for discovery credit**: a 2018 companion theorem already singles out this witness, and its formulas make the refutation routine. No acceptance credit is assigned. Root handles independent review and acceptance.

`results.json` is keyed by all 40 MathDB IDs and separates literal review, primary-body review, bounded diagnostics, missing proofs, complete formal endpoint and significance limits. `literal-records.json` preserves every exact normalized record, corpus filename, 1-based line number, SHA-256 of the original line INCLUDING its newline, and full chunk SHA-256. `input-bindings.json` binds campaign rules, prior ledgers, immutable upstream and the reservation.

## Strongest route: 327346

The witness has bipartition sizes (4,7), 22 edges, and row degrees (7,7,7,1). The only admissible proposed upper graph has dimensions (4,6), obtained by deleting two edges at a single vertex in the larger part. Their actual adjacency spectral radii are respectively

`√(11+√103) > √(11+√101)`.

`PROOF-327346.md` gives the complete ordinary argument, primary-source locators, semantic explanation and adverse prior-art conclusion. `lean/SpectralData.lean` proves `RefinedSpectral.counterexample : ¬ RefinedSpectral.Conjecture`, including edge counts, unique admissible dimensions, positive Gram eigenvectors, the block-adjacency eigenvector bridge, and a general positive-vector maximum principle proving these are the greatest actual adjacency eigenvalues. The conjecture uses 0/1 incidence coordinates for labeled simple bipartite graphs; the source's graph API is not assumed. All final printed transitive axiom lists use only propext, Classical.choice, Quot.sound. See packet and fresh replay receipt.

Original arXiv:1402.5621v1 Conjecture 6.1, p.11, and published LAA 474 (2015), Conjecture 6.1, p.42, agree. The later Cheng–Fan–Weng, *Taiwanese J. Math.* 22 (2018), Theorem 5.1(iii), p.271, identifies exactly K⁺_{3,7} at e=22 (21 composite, 23 prime); Example 3.2 gives the degree formulas. Those body passages and related proof portions were read. This is a serious public-subsumption/routine-corollary exclusion, not novelty clearance. The certificate is retained as a reviewable negative research result.

## Other sustained attempts

1. **327066, path–linear-forest Ramsey numbers.** Read original Conjecture 1 and Theorems 3–4 plus proof bodies. Exhaustive graph-atlas checks covered 18 eligible (n,F) cases at conjectured R≤7, including n=4,m=5. A separate exact path-coloring capacity search checked **269,093** cluster-graph/forest pairs over n=2..8, all nonempty forests and all clique-size partitions on the proposed threshold. No witness. The source's wheel sandwich loses the required odd-component information; a universal forest-sensitive complement embedding theorem is still missing. `cluster_diagnostic.py`, `diagnostics.py` and JSON outputs preserve the search.
2. **327617, stack versus revstack sorting.** Read the exact recursion and zigzag classification proof bodies. Exact enumeration of all **409,112** permutations over n=2..9 satisfies the conjectured weak and required strict inequalities. Existing six t-classes are known, not new. A uniform injection/fertility comparison stable under iteration remains unproved; zigzag avoidance alone does not compare cumulative preimages.
3. **327265, d-interval edge coloring.** Read Conjecture 4.2 and the endpoint-orientation proof of Theorem 4.3. That proof only gives 2d(Delta-1); its Delta=2 specialization cannot receive credit. Attempts based on fractional coloring or cliques do not supply the missing integral rounding or a valid counterexample.
4. **327275, Schoenberg operator.** Read knot/Greville definitions, the spectral definition and neighboring proof bodies. Gamma excludes the eigenvalue 1; it is not the multiplicity-counted second eigenvalue. The k=1 interpolation endpoint is unsuitable. A variance-based lower-bound idea has no proved all-grid bridge and does not settle both limits.

## Existing resolutions and fidelity traps

- **326838:** Wang Theorem 1.4 and section-3 proof already prove the full divisibility assertion.
- **327389:** Fischer–Reibnegger arXiv:2608.24548v1 (August 2026), Theorem 3/Conjecture 2 and section-3 proof establish the exact inversion symmetry. Original and newer bodies read.
- **327416:** Geelen–Nelson arXiv:1406.2588, Theorem 1.2 and Lemma 3.3/proof refute the positive-density assertion; original source read too.
- **327495:** its own primary Grosu body immediately reports the 1988 Korner–Marton tetracode counterexample at n=3,k=4. Original 1988 body was not obtained; no need to claim that old result as new.
- **327542:** Nasyrov arXiv:2605.25779v3 (June 2026), Theorem 1 and tangent-half-plane proof give the sharp 1+a bound.
- **326726, 326895, 327434:** literal records themselves report a solution/refutation; body review was not inflated from these reports.
- **327344:** the 2021/2022 BFP counterexample paper has an explicit no-isolates convention. Smaller complete bicliques with isolated padding can defeat a mechanical transfer to the normalized literal class. This is a scope hold, not a claimed exact public refutation.
- **327217, 327545, 327546:** material semantic/hypothesis corruption; no transcription loophole counted. Disconnected/isolated-vertex tricks for 327212 and parity tricks for 327461 likewise rejected.

The remaining records have concrete parked-route notes in `results.json`; no claims of primary-body coverage were made for those 29 records.

## Current registries and limits

HTTP receipts dated 2026-11-01 UTC (2026-10-31 Pacific) are saved with URLs and hashes. OpenAI math current main is **4eaee87548250b2682affda7d05d947c05554bae**, commit dated 2026-10-30. This matches the recent r5 receipt, whose complete preprints subtree is reused by exact body hash; `registry-path-hits.json` contains the bounded path screen. This is not an all-body theorem subsumption audit.

Palomar revision **651**, release **ff01fa2bd3240170cedf26fba4b146111e3b132a8c11fe533e5cea0a9fe75287**, returned no entries for path-quasar, revstack, Schoenberg, and bipartite-spectral queries. Empty hits are not novelty proof. The live MathDB solutions/comments surface remained unavailable under the recent inherited HTTP 403 receipt; no retry, bypass or browser was used. No MathSciNet/zbMATH/worldwide priority certification. See `research-limits.json` for exact scope and mistakes preserved candidly.

All writes stayed in this lane. No subagents, git, shared edits, external messages, publishing or tabs. Diagnostics used one CPU with process time/memory caps; Lean used two workers, bounded time and the existing read-only pinned mathlib, without rebuilding it.

Final replay: `replay-result.json` is PASS for `final-replay-clean/`, with zero warnings, warnings as errors, Lean -M4096, two workers and a 120-second cap. Reproduce after extracting the packet with `bash lean/run.sh lean/SpectralData.lean` in its extracted directory. The script uses existing pinned toolchain/package paths in `lean/dependencies.json`. Final source SHA-256: `41a2f8179d104b5bbd756f8653f64bc3e8b43ae33af316321b6f7bc67e883f14`. Packet SHA-256: `fe79ef41d2a2c0c86d9ce81f4ebfa92fa70dcd782532805b8c3925182168f986`. Earlier failed replay logs are retained and superseded by this receipt.
