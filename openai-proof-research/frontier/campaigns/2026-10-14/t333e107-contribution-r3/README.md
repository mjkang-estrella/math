# T333E107 contribution review, round r3

**TECHNICAL, conditional on correctness.** There is no substantial-contribution
PASS. No count, R-number, or acceptance is entered, and the proof gate is not
decided here. The supplied campaign state remains 18/20. The parent integrates
and decides.

Files:

- `review.md`: the standalone verdict. It contains the exact target, the paid
  source labels, my own step-by-step reduction (including a tube-free chord
  route), the reassessment of every original objection and every r1 draft
  observation, presentation notes, and the source334 relevance check.
- `paid-unpaid-comparison.md`: allocation of each author step to source
  operations, elementary steps, or the single residual observation. It also
  covers failing alternatives and the family333 chains.
- `reading-limits.md`: actual reading extents, hash checks, unread material,
  and limits.
- `checks.py` and `checks.json`: deterministic finite checks. They cover the
  exact hostile two-jet, an exact convex-combination example, exact random
  complement-duality trials, and a floating-point toy of the projection
  mechanism. **They are illustrations, not proofs.** `checks.py` reads and
  writes nothing; `checks.json` is its stdout (`python3 -B checks.py`).
- `status.json`: the machine-readable status and no-count boundary.
- `integrity_controls.py` and `integrity-controls.json`: 2 positive and 16
  negative controls for `verify.py`, all as expected. Every mutation acts on
  copies inside a scratch directory, which is removed at the end. The receipt
  records a run against the pre-receipt manifest named in its
  `manifest_under_test` field. The bundle was then resealed to include the receipt, and the same controls were
  rerun against the final manifest; that result is reported in the handoff
  rather than stored, because a receipt cannot contain its own seal.
- `build_manifest.py`: writes only `manifest.json` and `seal.sha256` here.
- `manifest.json`, `seal.sha256` (a convenience copy only), and `verify.py`.

Verify offline from this directory, using the detached manifest SHA256 from
the parent-facing handoff:

    python3 -B verify.py --expected-manifest <DETACHED_SHA256> --repo-root /home/mj-kang/Documents/Dev/math/openai-proof-research

The verifier is read-only. It checks:

- exact bundle membership and payload hashes;
- the status boundary;
- 36 author files and their exact directory membership;
- context files: AGENTS.md, upstream.json, the complete tree, the r5/r17/r92
  bodies, and the six r1 draft files;
- the retained third-party evidence, by hash, in place;
- 13 pinned Git blobs (12 source333 build files and the source334 main file)
  against the complete 13,223-entry tree.

Success authenticates bytes only. This directory holds no third-party copies.
No author, r1, parent, or shared-ledger file was modified. No staging, commit,
upload, browser UI, contact, or nested agent was used.
