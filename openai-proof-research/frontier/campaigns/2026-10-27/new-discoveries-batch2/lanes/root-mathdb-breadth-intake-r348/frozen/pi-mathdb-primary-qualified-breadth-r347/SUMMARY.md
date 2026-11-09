# pi-mathdb-primary-qualified-breadth-r347 — SUMMARY

Breadth review of the 50 MathDB records reserved for this lane in
`root-mathdb-c5-intake-r346/reserved-ids.json` (identical to the 50-id queue of
`root-mathdb-breadth-intake-r344/queue.json`, verified by direct comparison), with **zero**
hypothesis briefs: after screening and public-resolution checks, no remaining record had a
concrete tractable full-scope mechanism, and the task rule "at most 3 briefs, fewer if no real
mechanism" was applied.

## Pre-scientific integrity verification (done BEFORE reading any statement)

- Root manifest `root-mathdb-c5-intake-r346/manifest.json`: 34 payload entries; all SHA256+size
  re-verified against actual bytes; file set exact (manifest.json / verification-receipt.json
  excluded by design). PASS.
- Root receipt `verification-receipt.json`: PASS, 2026-10-31T05:12:08Z, coverage 383.
- Full corpus `pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-0001..0020.jsonl`:
  all 20 chunks re-hashed against the inventory manifest: 20/20 match (95,675 records). PASS.
  Flat immutable references only; no corpus copy beyond the frozen input set; no recursive
  history trees.
- Exclusions `root-mathdb-accepted-exclusions-r304/{accepted-exclusions,historical-dispositions}.json`
  re-hashed and matched. PASS.
- All scientific inputs were copied into `frozen/` and hashed into `frozen/input-hashes.txt`
  (29 entries, actual UTC 2026-10-31T05:13:41.330Z) BEFORE `work/reserved-records.json` or any
  statement was read. The 20 corpus chunks were additionally SHA256-verified in place against
  the inventory manifest before content processing (20/20 PASS). No late or reconstructed
  hashes are claimed anywhere.
- Amendment (2026-10-31T05:50:57Z, before manifest build): the frozen corpus byte-copies were
  REMOVED per the no-corpus-copy rule; `frozen/input-hashes.txt` now has 10 entries (the
  remaining frozen inputs) and `frozen/pi-mathdb-full-corpus-inventory-r301/
  corpus-verification.json` records the 20 chunk hashes with the flat immutable reference to
  `lanes/pi-mathdb-full-corpus-inventory-r301/` (no recursive history). The original 29-entry
  pre-content hash list is quoted in this lane's session history; the 20 chunk hashes are
  also immutably present in the inventory manifest itself.

## Reservation disjointness and dedup (verified by direct comparison)

- The 50 reserved ids are disjoint from the 383 ids in
  `root-mathdb-c5-intake-r346/coverage-delta.json` (0 overlap).
- Disjoint from all 33 `mathdb_lookup` entries of `accepted-exclusions.json` (0 overlap), from
  the 39 accepted families, and from the 118 mathdb ids inside
  `historical-dispositions.json` (previous/current excluded and holds; 0 overlap).
- All 50 records are `status=open`, `solution_count=0` in the verified corpus
  (43 `open_problem`, 7 `conjecture`). Open labels and empty solution arrays were NOT treated
  as novelty evidence; resolutions below were established against named public sources.

## Coverage of the fifty statements

- 50/50 records: full literal statement read from the corpus extract
  `work/reserved-records.json` (also rendered to `work/statements-50.txt`). Tags were never
  used as review.
- Evidence levels: `cached_full_statement_read` for all 50; `retained_primary_pdf_body_checked`
  for the 5 resolutions with retained bodies; `public_abstract_or_search` for 2 more
  (399772 ScienceDirect-hosted body excluded by access policy; 400177 identification only).
- No claim of exhaustive current-registry clearance is made. Current-registry gaps are stated
  per record in dispositions.json.

## Dispositions (dispositions.json, exactly 50)

- **5 REJECT publicly resolved**, each with a named public resolution and, where lawful, a
  retained body-checked primary PDF in `sources/`:
  - **398792** = Engbers–Galvin conjecture, proved verbatim as Theorem 1.2 of Gan–Loh–Sudakov
    (arXiv:1311.4147; CPC 24 (2015) 521–527) — retained PDF, body-checked.
  - **400244** (Alon's f(k) ≤ 1000k²): resolved by "Quadratic-size Random Permutations are
    Universal" (arXiv:2610.13530, 2026-10): a uniformly random permutation of length 32n² is
    n-universal w.p. ≥ 1−exp(−cn/log n) — retained PDF, body-checked; 32k² ≤ 1000k². Prior
    progress He (arXiv:1911.12878) and He–Kwan also recorded.
  - **400776** = the finite form of Reiher–Rödl–Ruciński–Schacht–Szemerédi (arXiv:1611.03118;
    Proc. LMS 2019): min vertex degree ≥ (5/9+o(1))C(n,2) forces tight Hamiltonian cycles,
    asymptotically optimal — retained PDF, body-checked.
  - **400867**: A(4, arccos(1/3)) = 14, proved by T. S. Tomar (Zenodo DOI
    10.5281/zenodo.23603434, 2026-10-23) by exact rational Lasserre level-2 — retained PDF,
    body-checked; supersedes the 16/15 two-/three-point bounds quoted in the record.
  - **399772**: the β–e linear-stability determination of elliptic Lagrangian equilateral
    solutions is classical: Danby (Astron. J. 1964) and G. E. Roberts (J. Dynam. Differential
    Equations, DOI 10.1006/jdeq.2001.4089). ScienceDirect body excluded by policy; DOI/abstract
    identification only.
- **11 REJECT famous-hard**: 398321 (43.52% local-algorithm optimality), 398322 (nonbipartite
  Ramanujan all d), 398403 (ropelength ≤ 24), 398482 (Minkowski), 399925/399926 (Ramos), 399983
  (explicit 2log n-Ramsey), 400257 (π(K₄³)), 400321 (generic cubic fourfold), 400795 (slicing),
  401011 (optimal points, Zilber–Pink scale).
- **16 REJECT deep** (no concrete tractable full-scope mechanism): 398348 (EH-type k≥4; related
  major progress Mubayi–Suk arXiv:1602.08716 read in bounded fashion — no clearance of the
  record statement), 398519 (Totaro CH), 398782 (P4 inducibility, open), 398788 (Bondy),
  398797, 398799, 399274/399275 (distinct circumradii), 400177 (K_n immersion at min degree n:
  best known is 11t+7, Dvořák–Yepremyan; K_{n,n} has K_n immersions, so no easy counterexample),
  400276 (IH¹⁰(A₄^Sat)), **400566** (house-Northcott: d=1 trivial, d=2 YES via
  Bombieri–Zannier/Widmer arXiv:1205.2491 retained; d≥3 open — and the 2026 preprint
  arXiv:2605.27232v1 claiming the general case was **WITHDRAWN** 2026-06-02 with a stated
  mistake, so it is not a resolution), 400774/400775 (Davies' 4/3 conjecture, see below),
  400780 (open even for C₄), 400929 (colorful Carathéodory complexity, open), 400976 (tilting
  characters).
- **6 REJECT programmatic/algorithmic**: 398566, 399745, 400230, 400231, 400616, 400621.
- **10 REJECT vague/open-ended**: 398297, 398547, 398678, 399002, 399464, 399956, 399965,
  400374, 400863, 400954.
- **2 REJECT statement-degenerate under the literal quantifiers**, each with a decisive small
  exact observation:
  - **398914**: an arrangement of n lines in general position has no multiple points, hence is
    vacuously stable with total multiplicity 0. The literal minimum is 0; the intended
    nontrivial version is missing from the record.
  - **400796**: literal c(d) = min over K ⊂ L of E V(P^K_{d+1})/E V(P^L_{d+1}) with no volume
    normalization. With K_ε = [0,1]^{d−1}×[0,ε] ⊂ [0,1]^d the slab is convex, so the hull of
    d+1 points of K_ε stays in it: E V(P^{K_ε}) = O(ε) → 0 while E V(P^L) is fixed; the literal
    infimum is 0. Numeric illustration in `work/comparison_constant_thin_demo.out` (ratio ≈ ε).
    No mechanism for the intended normalized version; not briefed.

## Small exact checks run in this lane (bounded, pinned env, failures preserved)

- `scripts/triangle_free_ratio_small_n.py` → `work/triangle_free_ratio_small_n.out`: exhaustive
  labeled triangle-free graphs on n ≤ 7 vertices (2+7+41+388+5789+133501 = 139,728 graphs;
  DFS with common-neighbor triangle pruning, exact bitmask DP for α and E|I|). Result: **all**
  ratios α/E ≥ 4/3; minimum 1.466667 = C₅ (n=5); n=7 minimum 1.477612. Sanity checks match
  hand values (C₅ = 2/(15/11); 3×K₂ = 3/2). This is finite evidence ONLY for Davies' Conjecture 1
  (400775/400774) — the smallest known ratio (1.43283) lives on 36 vertices — and does NOT
  clear the conjecture; a full-scope proof needs new hard-core/entropy machinery (any constant
  > 1 would improve R(3,k) per Davies), so no brief was issued.
- `work/comparison_constant_thin_demo.out`: numeric confirmation (exact slab argument) that the
  literal comparison constant of 400796 is 0.

## Why zero briefs

The five records whose concrete questions could be checked are all publicly resolved (above).
Every remaining open record is famous-hard, deep at absorption/flag-algebra/structure-theory/
complexity-separation scale, programmatic (deliverable = algorithm), vague/open-ended, or
statement-degenerate. Per the task rules ("Reject famous-hard/deep/programmatic cases
promptly"; "fewer if no real mechanism") no hypothesis briefs were manufactured. Root may
separately delegate hypotheses if it disagrees with any deep classification; the notes record
the exact best-known references to re-open any of them.

## Provenance

- All retained sources in `sources/` with exact URLs, sizes and SHA256 in `manifest.json`;
  retrieval timestamps in `sources/retrieval-utc.txt` (2026-10-31, before body reading);
  role of each file in `bindings.json`. Key statements extracted to `work/extracts/*.txt`.
- Access: lawful primary public HTTP and public web search only. No MathDB network requests
  (no 429-hold risk incurred), no Google, no GitHub API/raw/codeload/diffpatch, no ScienceDirect
  bodies, no browser tabs, no uploads, no account mutations. No 403/429/challenge routes hit.
- Abstracts/answer-mode text was used only to identify resolutions; retained PDFs were
  body-checked for the five resolved records.

## Failures / limitations (candid)

- No exhaustive clearance of current public registries is claimed for any record; negative
  search hits are not openness proofs. 399772 and 400177 rest on abstract-level identification
  (bodies inaccessible/excluded by policy).
- The r344/r346 frozen queue's own provenance was taken from the verified root manifest; this
  lane did not re-audit upstream corpus harvesting.
- No Lean, no manuscripts, no extended serial solving, no shared/index/ledger/git/public edits;
  counts 9 additional / 39 total / next 40 unchanged; no credit or shared edits.
