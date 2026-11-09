# MathDB 381433: draft manuscript and Lean dossier

The six-page AI-assisted DRAFT proves that the cyclic Latin square graph of
order 6 is adverse and non-Q: alpha = 5, upsilon = 6 and least eigenvalue = -3,
with both latter invariants unchanged after every open-neighbourhood deletion.
It also covers the noncomplete variant. No priority claim is made. Accepted
credit is zero; root alone performs final replay, manuscript review and acceptance.
Campaign context remains 15/20 beyond the historical 39.

The 13 original proof modules and original Audit.lean are byte-identical to
adverse-formal-r2. Reviewer.lean is hash-identical and explicitly reviewer-authored.
The FINAL source-only ZIP was safely extracted afresh and fully replayed: strict
-j1 -DwarningAsError=true builds, leanchecker for all 14 proof modules plus audit,
a full 167-declaration audit, and seven expected negative controls all PASS.
Only propext, Classical.choice and Quot.sound are permitted transitive axioms.
See fresh-replay/receipts/replay.json and logs/full-audit.log.gz within that tree.
The earlier completed preliminary replay is superseded by the final-archive replay.

All 1466 frozen bindings remain unchanged. The exact raw MathDB line is in
inputs/raw/381433.jsonl with its own hash receipt. Every final PDF page was rendered
and visually inspected; six PNGs and receipts/pdf-qa.json are retained. Every Lean
call had a sampled total process-group RSS watchdog, two-CPU affinity, CPU 120 s,
wall 140 s and MALLOC_ARENA_MAX=2. Peak sampled RSS was
5319368704 bytes; longest call was
23.75 seconds. All limits passed.

Deliverables: paper/adverse-latin6-draft.pdf and paper/manuscript.py; PROOF.md;
STATEMENT-CORRESPONDENCE.md; REPRODUCE.md; results.json; both manuscript ZIPs;
MODULE-HASHES.json, SOURCE-MANIFEST.json, INPUT-COPY-MANIFEST.json,
DOSSIER-MANIFEST.json and archive-hashes.json; receipts/, qa/, frozen source copies,
historical review/access receipts and the fresh extracted replay sources and logs.
The full ZIP excludes compiled artifacts, temporary PDF dependencies and the superseded preliminary replay.
DOSSIER-MANIFEST covers payload files; archive hashes are a separate sidecar to avoid self-reference.

Luz 2020 remains explicitly unread. Its abstract-level description and same-issue
context do not clear subsumption. Other inherited access/final-version/current
registry gaps remain; no fresh literature search or novelty clearance is claimed.
The source bibliography identifies the versions and passages actually read.
Cached dependency oleans are trusted and RSS monitoring is sampled.

All writes stayed in this lane. No children, git, shared-ledger edits, browser,
publication, uploads, accounts or external messages were used. No task-owned
background jobs remain. Historical copied receipts retain their original claims
and private-RSS terminology; this lane's final replay uses total VmRSS.
