# fresh-corpus-r10 — 40 reserved records

**Zero acceptance credit. A strong ordinary counterexample to MathDB 330264 survives; its full Lean endpoint and novelty clearance remain incomplete.** No shared ledger or count was edited.

## Main finding: 330264

Two explicit 19-vertex trees have identical adjacency, complement and line-graph characteristic polynomials, but different right-angled-Coxeter geodesic growth. At word length18 the coefficients are respectively

- 37769749324097905710910,
- 37769749324097905710906.

The difference is4. Exact six-matrix integer calculations were independently checked with two characteristic-polynomial algorithms. The selected graphs, polynomials, transition recurrence and ordinary proof are in `PROOF-330264.md`, `spectral_candidate.json`, `exact_spectra.json` and `independent-spectra.json`.

`AutomatonCertificate.lean` **passes strict Lean4.34.1 checking** and proves the length18 dynamic-count discrepancy from graph-derived clique-state transition tables. `#print axioms SpectralTree330264.counts_differ` reports only `propext, Quot.sound`. This is a partial finite certificate. It is NOT a Lean theorem about shortest words in the actual presented groups and NOT a proof of the three actual matrix characteristic-polynomial equalities. `FORMAL-GAPS.md` lists these semantic obligations precisely. `330264-PARTIAL-certificate.zip` is explicitly a partial packet; fresh extracted replay status is in `partial-replay-receipt.json` (PASS, exit0, about32seconds).

The original Ciobanu–Kolpakov Conjecture1.3 and both main construction proof bodies were read. Their unequal-growth theorem permits different line spectra; it does not directly imply this refutation. Their triple-cospectral construction gives equal growth. The 2013 Antolin–Ciobanu regularity theorem and 2021/2022 Antolin–Foniqi formulas also do not apply: these trees are not regular. **McKay1977 and Godsil spectral-construction bodies still require comparison**, so the exact advance beyond all earlier constructions is not yet independently cleared. No no-hit/open-label novelty inference is made.

## Coverage

- 40/40 actual normalized records extracted and literally reviewed.
- Original literal byte lines retained individually; `extraction.json` records 1-based source line, exact source chunk, SHA256(chunk), SHA256(original line including newline).
- Seven IDs have bounded primary-body reading:330264,330343,330507,330624,330879,330880,330947. Other33 remain literal-level screens, not source-level novelty dispositions.
- One ordinary full-scope refutation candidate:330264.
- One partial successful Lean certificate:330264. Zero completed literal MathDB Lean endpoints.
- Bounded numerical BFS spectral scouting covered all unlabeled tree orders8..16 (64,966 graph/index comparisons); no corrected violation found. These diagnostics are not proofs.

`results.json` is keyed by each of the40 IDs and separates literal review, primary-body scope, ordinary proof, formal completion, mechanism/gap and novelty limits. `research-notes.md` preserves failed and corrected routes, including the distance-matrix indexing false hit and the initial stuck Lean list-lookup normalization.

## Known-result and scope filters

330507 has a later primary paper explicitly proving the maximum and refuting the minimum conjecture.330947 has a later primary publication explicitly proving the exact uniqueness conjecture. Full later proof bodies were not obtained, and are not claimed read.330624's original maximum-critical-set formulation is explicitly settled by Short's Theorem1.6; its structural/alternating-path proof was read. The normalized all-critical-set wording must not be silently conflated with that definition.330192 and330354 already report prior refutations in their own literal statements; those are flags, not fresh discoveries.330471 and330989 present excluded wording/algorithm-scope issues; no investment in correction formalizations.

## Current receipts and limits

Sources have dated URL/status/hash receipts. The latest arXiv source version for330264 is v3,17Jan2020; the downloaded PDF hash is recorded. Recent current OpenAI registry head receipts were reused, and a recursive root tree at that head was fetched but GitHub marked it truncated: `sources/registry-screen.json` records its bounded path-name search. That is not a body-level or global novelty clearance. AIM's preprints URL returned Page Not Found; its empty matches provide no evidence and the receipt explicitly says so. No denied route was retried or bypassed.

All work stayed in this lane. No child agents, git operations, shared edits, author messages, publication or browser tabs. Lean used at most2 workers,2300MB memory limit and120-second per-build timeout, against read-only existing dependencies; no rebuild of mathlib. Earlier finite diagnostic processes used one BLAS thread and bounded execution.

## Recommended root handoff

Independently check330264's two exact graph witnesses and first discrepancy, compare the unread McKay/Godsil bodies and closest public counterparts, then decide whether to invest in a dedicated normal-form/spectral formalization. The normal-form recognition bridge is the largest Lean obligation; adding it as a hypothesis or redefining geodesic growth to mean the computed recurrence would not satisfy the task. No result from this lane can yet count toward20.

Registry correction: GitHub truncated the recursive root-tree response. The separately fetched `preprints` subtree is complete (`truncated:false`), with a dated hash receipt at `sources/registry-preprints-receipt.json`; its returned geodesic-named entries concern Riemannian geometry/first-passage percolation rather than RACG growth. This remains only a path screen.
