# RCS128 contribution and eligibility review, round 1

This is an independent reviewer's packet for the frozen author packet `../fresh-structural-discovery-r37` (manifest `a81ea2335db99c097423af9baf5abd272fa556ab6f08d870b8d184ee23bb96a6`). Original prose CC BY 4.0, original code MIT. It contains no third-party bodies.

Start with `review.md` (verdict SUBSTANTIAL at full scope, conditional on the proof gate), then `findings.json`, `reading-limits.md` and `checkpoint.md`.

Supporting files:

- `author-identity-replay.json`: author verifier controls.
- `independent_checks.py` and `independent-checks.json`: reviewer-written finite diagnostics.
- `history-search.json` and `literature-search.json`: bounded searches.
- `integrity-controls.json`: pre-seal controls of this packet's verifier.

Verify read-only with an anchor obtained from the parent handoff, not from this packet:

    python3 -B verify.py --anchor EXTERNAL_SHA256 [--replay] [--author-root ../fresh-structural-discovery-r37]

`--replay` reruns `independent_checks.py` and requires byte equality with `independent-checks.json`. `--author-root` rechecks the frozen author hashes in place. A wrong anchor fails before any payload check. Passing establishes identity and finite diagnostics only. It is not a proof, acceptance or priority claim.
