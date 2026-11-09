# r504 Claude MathDB primary-qualified breadth: 50 literal reviews, 0 proposals

Lane: `claude-mathdb-primary-qualified-breadth-r504`. Assignment: `queue-r504.json` / `reserved-ids-r504.json` from intake r503. No substitute IDs. No sibling statements were read; sibling reservations were used as ID sets only.

## Outcome
- **Coverage:** 50/50 reserved records were read as literal full statements (`dispositions.json`). Each entry carries its corpus chunk and line, the exact UTF-8 statement, the statement SHA-256, the raw line SHA-256 and the canonical record SHA-256 (`ensure_ascii=False, sort_keys=True, separators=(',',':')`). These are literal reviews. They are not proof audits, novelty clearances or registry clearances.
- **Proposals:** 0 (`proposals.json` = `[]`). No row has a full-scope, non-public, non-routine route surviving bounded screening.
- **Credit:** 0 for every row. Counts are unchanged.

| Disposition | n |
|---|---|
| RETIRE_SOURCE_RESOLVED (cited source claims proof or answer) | 15 |
| RETIRE_SOURCE_REFUTED (cited source counterexample) | 9 |
| RETIRE_PUBLIC_RESOLVED (+ routine corollary) | 3 |
| Partially resolved by source; hard residual (383363, 405149, 405171) | 3 |
| Other retire: source-reported or public proof recorded (405372, 374929, 406237) | 3 |
| NO_ROUTE_HARD_OPEN (14) + exact-value residual 383300 (1) + parameter-family scope 391926 (1) | 16 |
| HOLD_STATEMENT_INCOMPLETE (383181) | 1 |

Exact counts are in `coverage.json`.

## Evidence levels (candid)
- **35 rows: arXiv abstract metadata** (one batched export.arxiv.org API call). A retirement at this level relies on the source's claimed result. No proof body was audited.
- **1 row (406512): primary body passage read.** arXiv:2610.20135v1 Problem 1.3, Theorem 1.5 and Corollaries 1.6–1.8. I checked Cor. 1.8 by hand for moduli 50/98/242, giving residues {37,47}, {47,61,89} and ten residues respectively. A bounded computation for n≤8000 (`runs/oustar.r2.json`) agrees; it is evidence only. The literal "determine which APs" also covers even n, which Thm 1.5 does not classify. That residual is a source-method adaptation and was not pursued.
- **2 rows: third-party primary pages.** For 383714, OEIS A080170 plus the arXiv:2606.22997 abstract show the exact criterion proved, with a Lean formalization. For 405261, erdosproblems.com/848 records Sawhney's large-N stability theorem, which immediately implies the upper-density bound.
- **12 rows: corpus statement only.** These are famous or hard open problems, the incomplete 383181, or rows whose own record reports a resolution (374929, 405372, 406237).
- Metadata discrepancies noted. For 383300 the record names Keevash–Sudakov, but the arXiv author is Żak. For 383302 the record names Eppstein–Karpov, but the arXiv author is Heejae Jung.
- Wording defect noted (no credit): for 405483, the literal reading with ordinary transpositions gives TD(16)=15 trivially. The intended object is block transpositions, and the source claims a proof of TD(16)=9.

## Gates
- **Gates passed:**
  - Intake r503 manifest (sha `8bc1f5df…`, 46381 B): exact payload (224 files) with no extra files.
  - 208 original/copy pairs checked in place.
  - r301 manifest matches its intake-bound copy.
  - All 20 corpus chunks and 8 frozen inputs checked in place against it.
  - The 50 IDs are disjoint from the 3733 coverage IDs, the 100 sibling reservations, the protected IDs and the r503 adjudications (338290, 339564, 372627, 337963).
  - The r304 and r363 originals match their intake-bound copies, and none of their numeric ID tokens intersects the reservation.
  - None of the 50 rows overlaps the 39 accepted families.
  - The upstream verify.py was not executed.
- **Not checked:** the current proof registry. That is irrelevant to promotion here (nothing is promoted), and no absence-of-hits inference is made.

## Access
- **Requests made:** zero MathDB requests. Seven public requests in total: arXiv API ×3, arXiv PDF ×1, OEIS ×2, erdosproblems ×1, all HTTP 200.
- **Not used:** GitHub, Google, browser, ScienceDirect and accounts. There were no 403/429/challenge responses.
- **Binding order:** the PDF and every derived view were bound before being read (`fetch-log.tsv`, `derived-bindings.tsv`).

## Failures and deviations (`failures.json`)
- **F01:** one bare `python3 -c` schema peek of the intake manifest ran outside the guard.
- **F02:** the first arXiv API request's User-Agent contained the user's email. It was not repeated.
- **F03:** the first ou* computation misread the generating function from pdftotext layout. The result was invalid; it is kept as a record, and the corrected r2 was rerun.

## Artifacts
- **Mathematical:** `dispositions.json`, `proposals.json`, `coverage.json`, `source-provenance.json`.
- **Integrity and records:** `flat-bindings.json`, `failures.json`, `verify.py`, `manifest.json`, `final-receipt.json`.
- **Bindings:** `initial-bindings.tsv` (first-touch hashes, including ledger/context/NEXT; NEXT.md was not read).
- **Verifier contract:** `verify.py` is read-only. Run `python3 -B -I verify.py`; it exits nonzero on any mismatch. The manifest covers all files except `manifest.json` and `final-receipt.json`.
- **Receipt:** `final-receipt.json` holds the verifier output plus bounded negative tests run on temp copies; no originals were touched.
