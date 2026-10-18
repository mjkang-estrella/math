# T224G proof review r1

Start with review.md, then reading-log.md and review-status.json. Verdict: PASS_FULL_T224G after required repair R1 (supplied in review.md). The frozen author text needs revision R1. Not counted; the contribution gate is separate.

Reproduce from this directory:
- `python3 -I -B checks/independent_checks.py`: reviewer-written exact finite support (local table, telescoping, shared-label identity, path inclusion-exclusion, pairings, counterexample, exponent bookkeeping). This is support only.
- `python3 -I -B verify_review.py --manifest-sha256 <EXTERNAL> --author-root ../fresh-analytic-discovery-r103 --canonical-tree ../../../../sources/preprints-tree.json`: read-only integrity check.
- `python3 -I -B review_controls.py --manifest-sha256 <EXTERNAL> --author-root ../fresh-analytic-discovery-r103`: copied positive control plus 7 reason-checked negative controls under /var/tmp. Private bodies are not copied.

Also replayed (not modified): the author's check_support.py, negative_controls.py (8/8) and verify.py with --private (24 payloads, 48 source receipts, 3 PDFs). A wrong anchor rejects.
