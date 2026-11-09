# Failures and access events — pi-mathdb-full-corpus-inventory-r301

Preserved verbatim; nothing silently dropped.

## 1. Interrupted predecessor lane (sol-mathdb-corpus-inventory-r299)
- Searched the whole `openai-proof-research` tree for `*r299*` and `mathdb-corpus`:
  no lane directory, no preserved output was found. Nothing to read or freeze
  from r299; this lane re-derived the inventory from immutable snapshots + live
  routes. (Only coincidental filename hits, e.g. `C7R00288.lean`, exist.)

## 2. MathDB API 429 rate limiting (2026-10-31)
- First attempt used 4 concurrent workers (~8 req/s aggregate): 325 records OK,
  then sustained `HTTP Error 429: Too Many Requests` (1019 fails recorded, kept
  in `raw/api-new-state.json` `fails`). Per access discipline (stop on 429, no
  bypass/proxy/retry-under-load), workers were stopped immediately.
- Switched to sequential 1 req/1.1 s. One later run again hit a 429 after 13
  records; all subsequent runs stopped instantly on 429 (`stopped:
  "http_429_STOP"`). 885 fail entries remain in state (they overlap the
  remaining queue and are retried only after a cooldown, in later scheduled
  invocations).
- mathdb.com/terms (fetched 2026-10-31) permits crawlers that follow robots.txt,
  identify themselves, and use a reasonable request rate; no numeric limit is
  published. robots.txt (fetched, archived in `raw/probe-robots.json`) disallows
  only /new /bookmarks /moderation /search — none used.

## 3. Routes that do not exist (404, verified 2026-10-31)
- `https://mathdb.com/api/export`, `/api/dump`, `/api/posts/export`, `/api` (docs)
- `https://mathdb.com/posts/{id}` (HTML route is `/p/{id}/{slug}`)
- `limit=1000` on `/api/posts` → HTTP 422 (max accepted limit appears to be ≤ some value ≤ 1000; 100 works)

## 4. List endpoint limitation
- `/api/posts?limit=100` returns metadata + `excerpt` only; no full statement,
  no solutions array. Full records require per-id `/api/posts/{id}`.
- `sort=newest` and `createdAfter=2026-09-29` parameters are accepted (200) but
  do not change ordering or filtering (total stays 95,669) — no server-side
  date filter found.

## 5. Sitemap vs snapshot discrepancies (exact)
- 6 snapshot IDs absent from the live sitemap (2026-10-31): 336437, 378095,
  381024, 405400, 405401, 405693. probxiv's own manifest (2026-09-29) lists
  405400/405401 as deliberately retained historical records; the other four
  dropped out of the sitemap after 2026-09-29. All six are retained in the
  normalized corpus with `historical: true` and full inherited statements.
- 8,145 sitemap IDs postdate the 2026-09-29 snapshot; 460 retrieved with full
  records, 7,685 remain (exact list: `raw/remaining-ids.json`).

## 6. probxiv snapshot internal flags (inherited, not independently re-fetched)
- manifest issue_counts include `not-in-early-snapshot: 495`,
  `uploader-is-not-conjecturer: 87530`,
  `no-unambiguous-40-category-mapping: 68102`,
  `not-explicitly-recorded: 107393`; meta line `complete: false, total: 560`
  refers to an earlier partial fetch. 495 records lack a `solutions` key
  entirely (vs empty array). Inherited `full`/`short` statement labels are not
  independently reviewed (see root-mathdb-corpus-reconciliation-r307).

## 7. Guard/kill events
- One `normalize.py emit` run and one `tag_and_shard.py` run were killed by the
  512MiB guard (MemoryError) while holding the full corpus in RAM; both were
  rewritten to stream and then completed under cap. No data was corrupted
  (chunks are rewritten atomically per run).
