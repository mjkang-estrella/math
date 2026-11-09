# SUMMARY — pi-mathdb-full-corpus-inventory-r301 (first checkpoint, explicitly PARTIAL)

MathDB-wide technical triage for low-hanging fruit: complete accessible problem
universe established, normalized/deduplicated corpus built, deterministic
screening tags + disjoint review shards delivered. **This is a phase checkpoint,
not a completeness claim and not technical review.** No shared/git/public/MathDB
mutations; no Lean/manuscript; counts 9 additional / 39 total / next 40 untouched.

## Headline numbers (exact, 2026-10-31)
- **Authoritative accessible universe: 95,669 live problem IDs**
  (sitemap-problems-1..5.xml = 20,000×4 + 15,669; independently matches the API
  `total` field on `/api/posts`).
- **+6 historical IDs** present only in the probxiv 2026-09-29 mirror
  (336437, 378095, 381024, 405400, 405401, 405693) → **95,675 known distinct
  problem numbers**, which is exactly the earlier 95,669 + 6 difference root
  flagged in root-mathdb-corpus-reconciliation-r307.
- **Retrieved with full record: 87,990** (87,530 mirror + 460 live API); 87,940
  `full` statements + 50 `short` (<40 chars). 495 mirror records lack a
  `solutions` key entirely.
- **Not retrieved (sitemap-only stubs): 7,685** — exact IDs in
  `raw/remaining-ids.json` (range 405906–414238 with gaps).
- 0 duplicate IDs, 0 malformed rows. Independent root reconciliation r307 and
  the separate lane verifier (PASS) agree on all of these.

## Record schema (corpus/mathdb-normalized-chunk-0001..0020.jsonl; 5,000 rows each, ascending mathdb_id)
`mathdb_id` (int), `uuid`, `canonical_url` (https://mathdb.com/p/{id}/{slug}),
`title`, `statement` (null iff not retrieved), `statement_completeness`
(full|short|missing|not_retrieved), `post_type` (conjecture 68,085 | open_problem
19,269 | theorem 176 + new-records mix), `status` (open 84,685 | claimed_solved
1,238 | claimed_progress 603 | solved 622 | refuted 363 | partial 15 |
special_case 4 + nulls for stubs; counts from the mirror), `tags`, `importance`,
`source_name`, `source_url`, `first_stated_year` (+source), `documented_by_year`
(+source), `references`, `solutions` (array, may be null), `solution_count`,
`has_formal_statement`, `has_bounty`, `created_at`, `edited_at`, `lastmod`,
`in_sitemap`, `historical`, `retrieval_source`
(probxiv_2026-09-29 | mathdb_api_live | sitemap_only).

## Official routes established (verified live 2026-10-31)
- `GET /api/posts?limit=100&offset=N` — list, metadata + excerpt only, `total`
  field; `limit=1000` → 422; no server-side date/createdAfter filter.
- `GET /api/posts/{number}` — full record incl. statement, solutions,
  formulations, references. This is the workhorse for backfill.
- `GET /sitemap.xml` → sitemap-problems-{1..5}.xml (authoritative ID list),
  sitemap-static.xml, sitemap-users-1.xml. robots.txt: public read-only pages
  welcome identified crawlers at reasonable rates; only /new /bookmarks
  /moderation /search disallowed (none used).
- No official bulk export exists (/api/export, /api/dump, /api/posts/export,
  /api → all 404). Best bulk source is the dated third-party mirror
  probxiv.com/datasets/2026-09-29 (raw/mathdb/problems.jsonl.gz, 34,079,050 B,
  sha256 3cb02a11…, verified byte-exact), self-described as local snapshots +
  normalized candidates, **not** an official MathDB product.

## Acquisition / reproduction (all via sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py, OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1; fixed512MiB AS / groupRSS CPU210 wall230 per invocation)
1. `raw/download_probxiv.py` — resumable mirror download + sha256 verify.
2. `raw/fetch_sitemaps.py` — all 5 sitemap-problems files → `raw/sitemap-problems-index.json`, diff vs mirror → `raw/new-since-snapshot.json`.
3. `raw/fetch_new_seq.py` — **sequential** `GET /api/posts/{id}` at 1 req/1.1 s, immediate STOP+preserve on 403/429; resumable state `raw/api-new-state.json`; output `raw/api-new/part-*.jsonl`. (A first concurrent attempt at ~8 req/s drew sustained 429s — preserved in `failures.md`; do not repeat it.)
4. `raw/normalize.py snapshot|api|emit` — idempotent staged normalization → `corpus/*.jsonl`.
5. `raw/tag_and_shard.py` — screening tags, 48 disjoint shards, ranked queue.
6. `raw/make_manifest.py` then `raw/verify.py` (separate guarded verifier) → `verification-receipt.json` = **PASS**.

## Screening tags & shards (first-pass heuristics — NOT technical review)
- Every one of the 95,675 records is `reviewed: false` with reason
  `first_pass_tags_only_technical_review_pending`. Keyword tags never count as
  technical review and no fixed twelve-family substitution was applied.
- 48 disjoint deterministic shards (`tags/shard-000..047.jsonl`, ascending
  mathdb_id, 2,000 each, last 675) + `tags/shard-index.json`.
- Ranked review queue `tags/review-queue-top.jsonl` (top 2,000 of 95,675,
  deterministic score toward small exact certificates / few parameters /
  explicit constructions / elementary inequalities & identities / low proof
  infrastructure; top score 78). Score formula is documented in the script.
- Disjoint special flags: 33 `campaign_duplicate_of_accepted_family` (exact
  join to frozen root r304 accepted-exclusions index — all 33 accepted-family
  associations matched; related-ID association is NOT an exact-scope claim),
  70 `prior_exclusion_or_hold_lead` (historical dispositions, leads only),
  1,158 `stale_resolved_record`, 1,952 `claim_unverified_status`,
  3,687 `hard_structural`, 50 `incomplete_statement`,
  7,685 `statement_not_retrieved`, 6 `historical_absent_from_current_sitemap`.
- Per root r304 README: historical exclusions/holds are leads, not exhaustive
  history or live novelty clearance; scope-literal comparison against the frozen
  index is required before any shortlist promotion.

## Provenance
- All input hashes: `frozen/pre-existing-snapshot-sha256.txt` (49 pre-existing
  snapshots, frozen before reading), `frozen/root-r304-frozen-sha256.txt`
  (frozen root r304 accepted-exclusions + historical-dispositions copies), and
  `manifest.json` (127 lane files + frozen list; manifest excludes itself and
  the receipt).
- Mirror file byte-verified against probxiv manifest sha256; live fetches carry
  per-record UTC timestamps. No Google routes, no denied GitHub API/raw/codeload
  routes, no ScienceDirect; 403/429/challenge → stop, no retry/bypass.

## Continuation (resumable, no restart needed)
- Reusable downstream partition: root's `lanes/root-mathdb-coverage-queue-r309`
  (built from the immutable r307 snapshot) partitions the same 95,675 IDs into
  384 unassigned batches of ≤250 with missing/incomplete/full-labelled queues,
  source-URL sharing hints and the 33 accepted-associated IDs flagged for scope
  comparison; all review statuses there are `not_reconciled`. This lane's
  checkpoint remains authoritative for actual inventory/coverage; use r309 for
  batch assignment logistics.
- Backfill the 7,685 pending IDs: rerun step 3 after the 429 cooldown window,
  then re-run steps 4–6. State files make every stage idempotent.
- Backfill 495 missing `solutions` keys from the mirror era via the same route.
- Inherited statement labels (`full`/`short`) are not independently reviewed
  (root r307 concurs); reviewers consuming shards should treat statements as
  cached records, verify scope literally against `source_url` before promotion.
- The two parallel subject reviewers can start from `tags/shard-*.jsonl` +
  `corpus/` now; shard content is immutable at this receipt
  (original chunks verified drift-free by root r307 and by this lane's verifier).

## Failures preserved
See `failures.md` (r299 lane absence; 429 timeline; nonexistent export routes;
list-endpoint limitations; 6 sitemap dropouts; 495 missing-solutions; two
guard-killed memory-overflow runs, rewritten streaming).
