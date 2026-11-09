# Validation receipt — round 6 partial packet

All 148 modules passed a fresh extracted strict serial build and individual leanchecker run. The replay started with no build products or success markers in fresh-extraction. The full driver log is fresh-extraction/replay-driver.log; uniquely named per-call logs are in fresh-extraction/logs. Root development logs are in logs.

The final audit reports inventory = audited = 282349 declarations, including 6911 LOCAL declarations. It checks exact set equality with the endpoint's full imported module inventory, including generated constants and opaque proof bodies. Every forbidden LOCAL metadata and transitive-axiom count is zero. The root and fresh replay audit6.jsonl files are byte-identical. Upstream implementation metadata is reported separately in results.json and is not represented as LOCAL proof metadata.

Every endpoint prints precisely propext, Classical.choice and Quot.sound. The intended endpoint has three explicit Prop hypotheses; these are hypotheses, not added axioms. No unconditional intended theorem is claimed.

All 144 inherited hashes match before and after. Source equality between delivery and fresh replay is checked by scripts/finalize6.py. The final source archive is extracted again into fresh-final-source and its Lean sources are compared byte-for-byte with those already replayed; documentation and receipt additions do not change a Lean source.

The independent regression verifies 118004 successor swaps among permutations of sizes 2 through 7 and 3380 innermost closed faces among all diagrams through four chords and all chord-monochromatic assignments. It tests both the exact orbit-count sign and the connectivity toggle. This is numerical evidence only, additional to the Lean proofs.

All five negative controls are rejected: wrong empty-annulus count, wrong n=4 count, wrong representative pairing, wrong successor-swap count, and wrong connectivity. controls.log retains the diagnostics.

Peak sampled RSS across retained capped runs is 3506408 KiB, below 6 GiB. Each Lean/Python/checker process ran with the specified two-CPU, CPU and wall limits and lane-local temporary/cache directories. All command sessions and watchdogs are reaped before handback. No background job is left.

No child agents, git operations, shared-ledger edits, browser tabs, network calls, publication, uploads, or external messages were used. This is not acceptance; root decides.
