Independent formal review round 1: PASS_SCOPED_SUPPORT
Myeongjin Kang; no affiliation. Original prose CC BY 4.0, original code MIT.

Read review.md for the verdict, exact scope, evidence and limits.
No full crossing certificate, actual evaluation injection, acceptance or count.
Only optional improvements remain for the requested scoped formal gate.

Frozen verification (no writes/resealing):
  python3 -B verify_review.py

Optional fresh replay, with all source copies, objects and complete logs in a
NEW .replays/timestamp subdirectory of this review:
  python3 -B replay.py
This reads the pinned dependency libraries and compiler, checks frozen review
records and pins, compiles fresh copies of all author/review Lean sources and
queries, and runs the author's integer/Fraction controls. It never uses author
support objects or rewrites frozen manifests. The original independent runner
subprocess tests and rational-matrix calculations are retained in support-checks.json
and logs/. Replay does not claim to formalize upstream U4 or the full theorem.

run_review.py, run_controls.py, check_support.py and authenticate.py are the
original evidence-producing authoring drivers. Their output paths identify the
original independent execution. For a subsequent non-destructive build use replay.py.
finalize_evidence.py authored this review's output inventory; it is not frozen
verification and is never used to repair mismatching author or review hashes.

input-manifest.json authenticates immediate review references. authentication.json
also contains every author payload/fixed-input and original source-map record.
output-manifest.json inventories all frozen review payloads including fresh build
objects, query sources, exact logs and receipts, excluding only itself and future
.replays/. Third-party publisher texts and dependency files are not copied.
