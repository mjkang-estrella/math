# T250P contribution review r1

Independent contribution/eligibility gate for `fresh-arithmetic-discovery-r35/` (external manifest `90c944f17915ef689c69139cda49b2b95f9174c1a84c1a2e4c70da7dc84d821d`). Verdict, operation-level comparison, objections and read limits: `review.md`. Verdict: **TECHNICAL** for the full unchanged T250P scope. No proof verdict, no count.

Verify this sealed directory with

    python3 -B verify.py --expected-manifest-sha256 CALLER_SUPPLIED_HASH

The anchor must come from the reviewer's final handoff message, not from this directory. The verifier rejects a mismatched anchor, any inventory change, symlinked or non-directory ancestors, symlinks, hardlinks, nonregular nodes and nested manifests. It establishes identity only.

`checks/canonical_compare.py` replays the author-packet identity work read-only (external anchors first, then canonical `sources/preprints-tree.json`). `checks/own_controls.py` runs mutation controls on disposable copies under `/var/tmp` only. Records are in `records/`. This directory contains no third-party bodies.
