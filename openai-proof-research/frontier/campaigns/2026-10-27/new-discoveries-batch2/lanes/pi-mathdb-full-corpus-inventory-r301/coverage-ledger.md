# Coverage ledger — pi-mathdb-full-corpus-inventory-r301 (first checkpoint, explicitly PARTIAL)

All counts are exact at the stated provenance dates. This is NOT a claim of
live-corpus completeness; MathDB grows continuously and 7,685 records await
retrieval.

## Authoritative universe
| Quantity | Value | Source |
|---|---|---|
| Live sitemap problem URLs | 95,669 | mathdb.com sitemap-problems-{1..5}.xml, 2026-10-31 (20,000+20,000+20,000+20,000+15,669) |
| API reported total (`/api/posts` `total` field) | 95,669 | mathdb.com/api/posts, 2026-10-31 — matches sitemap exactly |
| Historical IDs (snapshot only, absent from current sitemap) | 6 | probxiv 2026-09-29 mirror minus sitemap diff |
| **Known distinct MathDB problem numbers** | **95,675** | union of the two above |
| probxiv 2026-09-29 mirror records | 87,530 (87,528 "ready" + 2 historical per its manifest) | raw/mathdb/problems.jsonl.gz, sha256-verified |

## Retrieval state (normalized corpus, 20 chunks, 95,675 rows, 0 duplicate IDs)
| State | Count |
|---|---|
| Full record from probxiv 2026-09-29 mirror | 87,530 |
| Full record from live API 2026-10-31 (post-snapshot new IDs) | 460 |
| Full statements total | 87,940 (`full`) + 50 (`short` <40 chars) = 87,990 |
| Statement inherited but record otherwise historical | 6 |
| **Not retrieved (sitemap-only stub, statement null)** | **7,685** |

## Reconciliation with root check
- root-mathdb-corpus-reconciliation-r307 independently froze these 20 chunks:
  95,675 rows / unique IDs, no malformed or duplicate rows, 7,685 empty
  statements, provenance 87,530 mirror + 460 API + 7,685 sitemap-only, all 33
  accepted-associated IDs matched; separate verifier passed. Point-in-time
  check, not a final handback or completeness claim.
- Difference from the earlier API total 95,669: the corpus carries 6 additional
  historical records (336437, 378095, 381024, 405400, 405401, 405693) present
  in the probxiv mirror but absent from the current sitemap; 95,669 + 6 = 95,675.

## Exact remaining work (resumable)
- 7,685 IDs to fetch via sequential `GET /api/posts/{id}` after 429 cooldown:
  `raw/remaining-ids.json` (range 405906–414238, gaps included; 885 entries
  carry recorded fail reasons in `raw/api-new-state.json`).
- Resume command (bounded, resumable): rerun
  `helper_guard.py python3 -I raw/fetch_new_seq.py` repeatedly; state advances
  in `raw/api-new-state.json`, output appends to `raw/api-new/part-*.jsonl`,
  then rerun `raw/normalize.py api` and `raw/normalize.py emit` (idempotent),
  then `raw/tag_and_shard.py` to regenerate tags/shards.
- 495 mirror records lack a `solutions` key (inherited gap; backfillable via
  the same per-id route).
- No independent verification of inherited statement correctness; metadata-only.

## Screening/shard summary (deterministic, first-pass only — NOT technical review)
- 95,675 records tagged; every record `reviewed: false` with reason
  `first_pass_tags_only_technical_review_pending`.
- 48 disjoint shards of ascending-ID order, 2,000 each (last 675).
- 33 records flagged `campaign_duplicate_of_accepted_family` (exact r304 join);
  70 `prior_exclusion_or_hold_lead`; 1,158 `stale_resolved_record`;
  1,952 `claim_unverified_status`; 3,687 `hard_structural`;
  50 `incomplete_statement`; 7,685 `statement_not_retrieved`.
- Ranked queue: `tags/review-queue-top.jsonl` (top 2,000 by deterministic
  score; top score 78). Keyword tags are heuristics, not technical review.
