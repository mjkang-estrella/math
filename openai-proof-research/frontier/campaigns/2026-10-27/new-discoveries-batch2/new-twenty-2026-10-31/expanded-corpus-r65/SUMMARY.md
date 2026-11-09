# Expanded corpus r65 investigation

2026-11-01. No proposed discovery and no Lean endpoint. Campaign count remains **7/20 beyond 39 prior**, unchanged. All 40 reserved IDs have individual entries in `results.json`, exact cached statements in `extracted.json`, and byte-preserved raw JSONL lines in `raw/`. Each raw entry records its original chunk, one-based line, chunk hash, raw-line hash including newline, and statement UTF-8 hash.

The conclusions are 8 known full-scope resolutions, 3 sustained but unresolved routes, 4 entries with partial prior-art leads, 24 hard targets parked, and 1 material source-formulation gap. These are research outcomes, not acceptance decisions. Correction to the intermediate update: there are **eight**, not nine, known full-scope resolutions.

The known resolutions are:

* **369818:** Freedman–Lee, 2607.23423, Theorem 1.3 and Corollary 1.5: a 2-closed elusive group, contrary to the Polycirculant Conjecture.
* **369912:** pinned OpenAI/math paper *Polynomial removal fails for ordered binary matrices*: a fixed 66 by 66 pattern violates every polynomial removal estimate.
* **369926:** its own source, 2508.17682, Section 2: four 8-vertex counterexample pairs to Kromatic completeness.
* **370009:** current 2508.20593, Theorems 1.2 and 1.4: both path minimum and clique maximum, including equality.
* **370232:** its own source, 2509.06345, Theorem 3: Voss's conjecture, proved by the cycle-cover double count.
* **370265:** Steininger–Yurkevich, 2508.18475, Theorem 1: the Noperthedron.
* **370331:** 2610.13798, Theorem 1.1: dijoin deficits can be a positive fraction of arbitrarily large inversion sums, contradicting a deficit bound of 1.
* **370353:** Aires, 2609.30895, Theorems 1 and 2: the full Kahn–Saks balance assertion.

The most useful unresolved handoffs are **369819**, **370010**, and **369837**. `ATTEMPTS.md` gives the source definitions, independent mechanisms, actual diagnostic bounds, and precise missing lemmas. Bipartite equality was tested both on the graph atlas and by structured corona modifications. Graph contraction was checked exactly through order 6 and reduced across a bridge to a concrete rooted-subtree inequality. Interpolation was tested on admissible conjugate-pair grids, and the live registry's adjacent Schur-ratio refutation was read and distinguished from the uniform endpoint. No bounded search is used as a proof. The initial interpolation log includes inadmissible odd grids; the separate admissible run and its correction are preserved explicitly.

Important non-exclusions: the OpenAI prime-predecessor law is not silently extended from shift -1 to every nonzero shift in **369940**; generalized-spectrum determination does not settle adjacency-only **370208**; later pancake gap estimates do not settle the exact quotient equality **370305**; one claimed non-Rupert Archimedean solid does not settle all three in **370267**. The unweighted character identity's source counterexamples do not automatically refute the q-weighted **370116**. The digital-picture foreground alone is insufficient for **370130**, whose complementary adjacency/homotopy is essential.

Live GitHub `/commits/HEAD` receipts were saved before proof investment. OpenAI/math remains `4eaee87548250b2682affda7d05d947c05554bae`. Omega changed to `aff4ea20b63a0ed02b1bfdc8803946aaf0f6200e`. Its recursive root tree was truncated; fresh separate **complete** D5 and Problems trees were fetched and screened instead. `outputs/registry-screen.json` binds those scopes and the inherited complete OpenAI preprints listing by SHA-256. Registry screening is predominantly paths, with selected actual Lean/manuscript bodies read; it does not clear all proofs, historical deletions or worldwide prior art.

Primary HTML for every unique assigned source was retrieved successfully, with dated URL/status/body-hash receipts. Targeted statements, definitions and selected proofs were read. The report identifies unresolved semantic or literature gaps rather than treating source access or an open label as novelty clearance. The current live MathDB reply/solution state and every publisher revision/citing paper were not audited. History screening used exact IDs and titles in campaign prose and selected structured reports; it found reservations and incidental numeric matches, not a substantive earlier resolution of these routes in its bounded scope.

All mathematical diagnostics ran with the lane's resource wrapper: two CPUs, CPU 120 seconds, wall 140 seconds, sampled RSS 6 GiB, 12 GiB address-space ceiling, and bounded BLAS threads. Logs and sampled resource receipts are retained; these are not cgroup or transient-peak guarantees. An initial missing-networkx failure is retained; the diagnostic dependency was installed locally in `vendor/` and the successful run is separate. No Lean packet was fabricated: strict replay, leanchecker and local-declaration axiom audit are therefore not claimed. No child agents, git operations, shared ledger edits, browser tabs, external messages, publication or uploads were used. No research process remains running at handback.

Reproduction and artifact validation are in `RUN.md` and `scripts/validate.py`.
