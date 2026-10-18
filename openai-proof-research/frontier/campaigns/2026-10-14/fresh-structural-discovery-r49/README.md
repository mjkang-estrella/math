# r49 T197H

Read original-scope.txt, candidate.md, operation-ledger.md and reading-limits.md. This is a complete author candidate awaiting independent gates.

Verify a received immutable packet with:

    python -B verify.py --expected-manifest-sha256 CALLER_SUPPLIED_HASH

The hash must come from the separate parent handoff. The verifier checks every file and directory including private source identities; it rejects links, hardlinks and nonregular entries. It does not establish mathematics or novelty. checks/integrity_controls.py uses disposable copies under checks and removes them; do not run seal.py on an authenticated immutable packet. Third-party bodies remain private/ignored.
