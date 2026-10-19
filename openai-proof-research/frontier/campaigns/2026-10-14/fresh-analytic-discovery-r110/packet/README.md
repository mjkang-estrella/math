# Analytic r110 unresolved research packet

Read public/research-report.md and public/frozen-target.md. T271D110 remains open; no nominee or mathematical gate is assigned. public/prefreeze-screening.md records three distinct family screens and the feasibility calculations preceding the freeze. public/reading-ledger.md states exact reading limits.

Original prose: CC BY4.0. Original/adapted integrity code: MIT. Upstream and third-party bodies in private/ retain their original rights and are not part of a public manuscript. Nothing here is uploaded.

Run the READ-ONLY verifier with a separately supplied detached final manifest digest:

    python public/verify_inventory.py --manifest-sha256 DETACHED_FINALHASH --root .

The digest is not inferred from the packet. The verifier checks the exact files/directories and frozen scope. It does not certify mathematics. public/test_integrity_controls.py is the recorded PRESEAL copy-test harness; it writes a receipt and should not be rerun against sealed originals. Its14 expected-outcome cases ran on disposable copies before the final manifest.
