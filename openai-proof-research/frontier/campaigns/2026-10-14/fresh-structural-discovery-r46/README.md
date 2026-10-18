# r46 handoff

No nominee; no frozen full target. Start with report.md. The exact support obstruction is in permutation-support.md; bounded fractional transport and its limitations are in weighted-transport.md. Original exploration is preserved in working.md and supplemented by final reading-limits.md/checkpoint.md.

Replay only against the external manifest SHA256 supplied by the parent/caller:

```sh
python3 -B verify.py --expected-manifest-sha256 EXTERNAL_HASH
```

This verifies inventory and source identities, not theorem truth or contribution. checks/seal.py is author preparation only; the read-only verifier never calls it. checks/integrity_controls.py mutates disposable copies inside an explicitly supplied new scratch directory, then removes them. It does not modify the sealed payload. Private originals stay ignored. No independent review or acceptance is claimed.
