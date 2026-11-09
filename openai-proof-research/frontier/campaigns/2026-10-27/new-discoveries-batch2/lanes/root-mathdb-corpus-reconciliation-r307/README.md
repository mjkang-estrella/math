# Partial MathDB corpus reconciliation

This root orchestration check copied 20 normalized chunks from the still-active
inventory assignment and the accepted-family routing index before parsing them.
The copies were hash-checked against originals before and after copying. They
are a point-in-time snapshot, not the delegate's completed or final inventory.

The snapshot contains 95,675 rows and distinct positive integer IDs, with no
duplicates or malformed rows. Its provenance labels report 87,530 records from
the 2026-09-29 ProbXiv mirror, 460 from the live MathDB API, and 7,685 sitemap-only
records. The last group has no statement text. Inherited completeness labels
are 87,940 full, 50 short and 7,685 not retrieved; these labels have not been
independently validated against full primary-source statements.

All 33 MathDB IDs associated with the 39 accepted campaign families appear in
the snapshot. `accepted-id-matches.json` supplies exact file/line references
and scope cautions for downstream dispatch. An ID match does not retire a
different hypothesis sharing that record.

No mathematical statement or primary proof body was technically reviewed here.
These counts must not be described as 95,675 problems investigated. Nor is this
a live-corpus completeness certificate: the earlier API probe reported 95,669
posts, whereas this snapshot combines sources and dates. Reconcile actual ID
sets and historical records before interpreting that difference.

`available-record-ids.json` is a deduplicated routing list, not a difficulty
ranking. The two triage handbacks remain the source of technical selection.
No scientific result or acceptance credit is added. No worker file was changed.
Run `reconcile.py` under the existing campaign helper guard to reproduce the
counts from the retained snapshot. Final integrity verification is separate.
