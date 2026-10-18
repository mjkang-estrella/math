# Checkpoint: RCS128 contribution review, round 1

Status: **complete. Classification SUBSTANTIAL at full unchanged scope, conditional on the separate full-proof gate.** Campaign count is unchanged at 12/20. Uploads are stopped. No commits, staging, nested agents or publication. The author packet is unmodified: `git status` of r37 was identical before and after, and the hashes are in `author-identity-replay.json`.

Steps done:

1. Read AGENTS.md, the pin, and the parent brief.
2. Verified the author hashes. Inspected all author scripts, then ran the author verifier: positive PASS with replay; zero anchor and last-digit-changed anchor both FAIL.
3. Read candidate.md in full, the r37 supporting notes, and the r36 screen and limits.
4. Read pinned source sections 01–07 in full and the whole Yamano–Shibuya extraction.
5. Searched the catalogue, the complete tree, campaign history, upstream GitHub (read-only) and the literature (bounded).
6. Independent finite checks: recomputed the template obstruction, recomputed the r36 minimum-cost orientations, and found a new composite-route instance.
7. Wrote the review, findings, limits, verifier and manifest. Ran the pre-seal controls (`integrity-controls.json`) and the final positive and wrong-anchor controls (reported to the parent).

Did not read the proof-gate directory `rcs128-proof-r1/`. Open items for the parent: R1–R5 in `findings.json`. If the proof gate requires changes to items 3, 5, 6 or 7, dispatch a new contribution round. Do not reuse this verdict.
