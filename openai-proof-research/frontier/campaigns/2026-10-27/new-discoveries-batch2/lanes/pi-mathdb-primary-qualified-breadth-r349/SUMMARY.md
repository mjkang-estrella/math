# Lane SUMMARY — pi-mathdb-primary-qualified-breadth-r349

Breadth review of the exact 50 MathDB IDs reserved in
`root-mathdb-breadth-intake-r348/reserved-ids.json` (all `status=open`,
`solution_count=0`, `statement_completeness=full`, retrieval source
`probxiv_2026-09-29`). No shared/index/ledger/git/public/browser/account edits;
no child agents; corpus read strictly in place (flat immutable refs, no copies).

## Input verification BEFORE content (all under fixed guard)

- r348 root manifest: all 47 listed files rehashed live — 0 mismatches; the
  scientific inputs used here (`reserved-ids.json`, `queue.json`,
  `coverage-delta.json`, `bindings.json`) match their recorded SHA256+size.
- r348 `bindings.json` (41 entries) rehashed against live originals — 0 failures.
- Corpus: all 20 files
  `pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-0001..0020.jsonl`
  rehashed IN PLACE (actual SHA256 + byte size) against the live inventory
  manifest `pi-mathdb-full-corpus-inventory-r301/manifest.json` — 20/20 OK.
  The live inventory manifest is byte-identical to the copy bound in the r348
  manifest; the live r304 exclusion files are byte-identical to their bound
  frozen copies.
- Dedup: the 50 reserved IDs are disjoint from the 433 IDs in
  `coverage-delta.json`, from the r304 `mathdb_lookup`, and appear nowhere in
  `accepted-exclusions.json` / `historical-dispositions.json` (string scan).

## Statement / body coverage

- 50/50 literal full statements read (in place, from the chunk files recorded
  per record in `dispositions.json`). 50/50 have `solution_count = 0`; no
  promotion from empty solution arrays or open labels anywhere.
- Dispositions: 46 `not_pursued`, 3 `publicly_resolved_reported`,
  1 `proposed`. Evidence level for all 50: `cached_full_statement_read`
  (tags were not treated as review).
- No extended serial solving; no Lean; no manuscript drafting.

## Publicly resolved (reported; abstract-level only — proof bodies NOT read)

- 402435 Benjamin–Ono below L²: Killip–Laurens–Višan, arXiv:2304.00124 /
  Inventiones 2024 — well-posed in H^s for s > −1/2 (covers the asked range).
- 402630 cycles of length divisible by 4 in tournaments: arXiv:2008.06577
  (c(ℓ)=1 iff 4∤ℓ) and arXiv:2608.06238 (resolves ℓ ≡ 0 mod 4; carousel).
- 403559 rainbow Turán of fixed even cycles: Janzer, arXiv:2006.01062 /
  Israel J. Math. 2023 — ex*(n,C_2k) = O(n^{1+1/k}), tight ⇒ Θ.

All five PDFs retained under `sources/` with SHA256+size recorded in
`manifest.json` and retrieval UTC in `sources/retrieval-utc.txt`. These are
reported resolutions, not independent root proof validation; chronology was not
compared in depth and no credit is claimed from them here.

## Proposal (1, exact ID)

- **404067** (generic singleton Gram spectrahedra): exact tangent-cone
  characterization; new unconditional upper bound
  m(n) ≤ N − w₁(n) with w₁(n) = min{w : w(w+1)/2 > n²(n²−1)/12}
  (m(2)≤1, m(3)≤2, m(4)≤4, m(5)≤5, m(6)≤6, m(7)≤8, m(10)≤14,
  asymptotically ~0.0918n² + n/2), improving the recorded m(n) < binom(n+1,2);
  exact m(2)=1 (self-contained) and m(3)=2 (upper unconditional; lower =
  recorded n−1 ≤ m(n), cross-consistent with the typical-case theorem of
  arXiv:2305.06860). Executed vs planned calculations, certificate size,
  Lean dependencies, prior-art status, and four explicit objections are in
  `proposals.json`. Interpretation risk (standard vs q_i-relative Gram
  spectrahedron) is flagged there and must be settled against the OWR 2023/14
  p.52 text before acceptance.

## Retained sources / provenance / bindings

- `bindings.json`: 27 live-upstream entries (r348 inputs, r304 exclusions,
  inventory manifest, all 20 corpus chunks) with actual SHA256+bytes.
- `sources/`: 5 PDFs + retrieval UTC. `work/`: build scripts.
- All helpers ran under the fixed guard
  (`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
  python3 .../helper_guard.py python3 -B ...`); peak group RSS ≤ ~30 MiB,
  wall < 1 s per run; no raises; no failures.

## Failures (see failures.md)

- One early working extract of the 50 reserved rows was written to /tmp before
  the in-place discipline was applied; it was deleted unused by any payload and
  all final payloads re-derive strictly in place. Disclosed in failures.md.
- ems.press OWR pages were not accessed; MathDB live site was not accessed
  (no network hold issues encountered); the two deferred verification items are
  listed in proposals.json.

## Counts

Zero new mathematical credit claimed in this lane. Counts **9 additional /
39 total / next 40 unchanged**. Root allocates each hypothesis separately; the
single proposal (404067) is offered for root adjudication with its objections.
