# T197H proof review r1

Independent adversarial proof gate for the frozen r49 T197H candidate. Verdict: PASS_FULL_T197H, 0 required and 6 optional objections. See review.md, read-limits.md and status.json. No contribution verdict is given.

Verify this sealed directory with a separately supplied manifest hash:

    python3 -B verify.py --expected-manifest-sha256 CALLER_SUPPLIED_HASH

The verifier rejects symlinks at the root, at any ancestor of the root and at any payload. It also rejects hardlinked files, nonregular nodes, inventory differences and hash mismatches. It establishes identity only, not mathematics.

checks/reviewer_controls.py re-runs the author-packet controls on disposable copies under /var/tmp. It needs the author packet path and sources/preprints-tree.json, and it never writes into the author packet. checks/verifier_controls.py runs mutation controls for this directory's verifier on disposable copies under /var/tmp.
