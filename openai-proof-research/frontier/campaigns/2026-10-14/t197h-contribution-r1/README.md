# T197H contribution review r1

Independent contribution/eligibility gate for `fresh-structural-discovery-r49/` (manifest `819bc0a77c9ae52ca8a1b2193f64fc2f84754c17b6d5e0750c0be0ae351fd8b2`). Verdict and objections: `review.md`. Verdict: TECHNICAL for the full unchanged scope.

Verify this sealed directory with

    python3 -B verify.py --expected-manifest-sha256 CALLER_SUPPLIED_HASH

The anchor must come from the separate reviewer handoff. The verifier rejects a mismatched anchor, inventory changes, symlinks, hardlinks and nonregular nodes at the root, its ancestors and payloads. It establishes identity only. Third-party bodies under `private/` are ignored and must not be published. Identity controls run only on disposable copies under `/var/tmp` (`checks/own_controls.py`, `checks/author_copy_controls.py`).
