# T115E109 independent contribution r1

Read `review.md` for the standalone TECHNICAL assessment conditional on correctness, and `reading.md` for exact provenance and limitations. The complete unchanged target is in the review. This gate assigns no finding number, acceptance or campaign credit; independent correctness and all downstream gates remain unset.

Replay from this directory:

```sh
python -B verify.py --expected-sha256 DETACHED_HASH_FROM_REVIEW_HANDOFF
python -B independent_checks.py
python -B private/author-checks.py
```

The verifier requires a caller-supplied detached SHA256 of `manifest.json`. Do not derive the trusted value from the same manifest. It is read-only, has no network, executes no payload code, checks exact packet membership, all external input anchors, unchanged author membership, the immutable upstream pin and complete-tree source identities. For relocation pass `--repo-root /absolute/path/to/openai-proof-research`; original author/prior-report inputs must remain available at their anchored relative paths. External shared-context edits cause a legitimate mismatch. This is an in-place evidence packet, not a portable standalone source distribution.

`finite-controls.json`, `author-checks-replay.json`, `integrity-controls.json` and `author-preservation.json` record finite controls and byte checks only. `private/` holds third-party evidence, temporary-control receipts and the copied author check script. It is not a redistribution or release directory. The proof and contribution gates remain distinct from all integrity checks. No uploads, browser UI, staging, commits, resets, PR work, contacts or nested agents were performed.
