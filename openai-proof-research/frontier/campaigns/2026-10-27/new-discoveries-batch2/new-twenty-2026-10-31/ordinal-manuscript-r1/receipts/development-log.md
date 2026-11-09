# Development log (ordinal-manuscript-r1, 2026-11-01)

All work by Claude Opus 5.5, no child agents, no git, no network access, no browser.

1. Read TASK.txt, the three AGENTS.md files and the PDF skill. Read the author proof, Lean module, review (366371 parts) and root adjudication.
2. Bound frozen inputs (`frozen-before.json`: 356 files, aggregate 18a3e22f…). Copied 366371-only inputs into the lane; identity in `copied-evidence-identity.json`.
3. Wrote reviewer supplements `proof/ReviewAudit.lean`, `proof/ReviewSanity.lean`, the stdlib diagnostic, the replay driver and the packaging tools (adapted from the yip-manuscript-r1 model).
4. Development replays in a scratch copy (since deleted) found and fixed: (a) `Nat` annotation needed for counters in the audit's `run_cmd`; (b) `fin_cases` unavailable under the module's imports, replaced by `Fin.forall_fin_two` + `norm_num` + `decide` in the two-point embedding example. All dev Lean runs went through `tools/capped.py` or the replay driver (caps: 2 CPUs, CPU 120 s, wall 140 s, AS 64 GiB, private RSS 6 GiB, MemoryMax=6G scope). Receipts for the ad-hoc runs are in `receipts/dev/`.
5. Packaged `source-only-proof.zip` (17 members), extracted it with `safe_extract.py` into the new directory `fresh-extraction/`, and ran `replay.py` there: REPLAY PASS.
6. Built the paper with ReportLab (cached read-only runtime, `-I -B`), rendered and inspected every page; QA iterations in `qa/receipt.json`.
7. Re-bound frozen inputs (`frozen-after.json`): identical. Packaged the full dossier and verified it by fresh safe extraction.
