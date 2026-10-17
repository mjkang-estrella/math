# TS132 independent full proof review

Verdict: **PASS_FULL_TS132** against the exact final author packet and unchanged full scope. Read review.md, read-limits.md, status.json and authentication.json together. This is an internal proof gate only; no contribution, formalization, acceptance or count is asserted.

Read-only replay from this repository:

    python -I frontier/campaigns/2026-10-14/ts132-proof-r1/verify.py --anchor EXTERNALLY_SUPPLIED_REVIEW_MANIFEST_SHA256

The manifest inventories every other review file and every subdirectory. Supply the detached hash delivered by the reviewer/parent. A locally recomputed hash is not a substitute for the trusted external anchor. The verifier checks this review, the exact final sibling author inventory, unchanged scope/candidate, all seven pinned source blobs against sources/preprints-tree.json, and the source revision. It rejects wrong anchors, missing/changed/extra files, unexpected directories and symlinks. It performs no mathematical computation or verdict inference. It writes no files.

Replay requires the original repository layout, retained author packet, and original complete source tree. No third-party bodies are copied into this review. A future public release can retain these historical identity receipts without pretending that a source-less archive can rerun the private dependency check.

Author: Myeongjin Kang, no affiliation. Original prose CC BY4.0; original verifier MIT. See RIGHTS.md and LICENSE-code.txt. No publication was performed.
