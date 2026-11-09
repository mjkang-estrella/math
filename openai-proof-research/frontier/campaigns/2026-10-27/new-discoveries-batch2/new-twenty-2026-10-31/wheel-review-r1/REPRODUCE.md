# Review reproduction

Run from this directory. Do not execute downloaded author programs. All input lanes and the shared package cache are read-only.

- `python3 -I scripts/extract_packet.py NEW_EMPTY_DESTINATION` safely extracts the hash-pinned source packet to a new review-local directory. The recorded replay is in `replay/`.
- `scripts/run.py` sets the assigned pinned Lean binary and read-only LEAN_PATH, then launches the resource guard inside a systemd MemoryMax=6G scope. Run `python3 -I scripts/run.py build MODULE` for each module, in `replay/modules.json` order. Run `check MODULE` for leanchecker. Existing replay oleans here were produced during this independent review; use a fresh extraction for a clean recheck and adjust the local replay path in a copied run script.
- `python3 -I scripts/make_audits.py` creates reviewer audit modules. Run `audit ReviewAuditMODULE` for each proof module. It enumerates all declarations whose originating module is MODULE, including generated/private ones.
- Run `audit ReviewRestatement` and `audit ReviewSourceCorollary` (expect exit 0). Run `audit ReviewNegativeFalse`, `audit ReviewNegativeWrongValue`, and `audit ReviewNegativeNoRange` (expect exit 1).
- Run computations under the same guard, for example `systemd-run --user --scope -p MemoryMax=6G python3 -I scripts/guard.py logs/recheck-computations.log python3 -I scripts/computations.py`. `pairing_check.py` checks all nonempty deleted sets through t = 6. Neither needs external Python packages.
- `fetch.py`, `prior_refresh.py`, and `literature.py` document public HTTP collection. The delivered dated bodies and receipts are the evidence for this review. Do not blindly rerun HTTP scripts: known denied routes must never be retried, and live heads may change. No author code is executed.
- `python3 -I scripts/finalize.py` checks input hashes against `receipts/inputs-before.json`, source manifest hashes, strict-build and checker receipts, full declaration audit, negative controls and resource receipts; it writes review.json and final-summary.json.

All meaningful initial failures are retained: lack of numpy led to a pure-Python replacement; leanchecker needed the pinned binary directory on PATH. Those are environmental failures, not failed mathematical certificates. Source Lemma 4.2 subsumption, documented in REVIEW.md, is the reason for the rejection recommendation.
