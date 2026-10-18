# r55 sealed bounded screen

Outcome: pre-freeze no nominee;303 false extension,297 technical external-primary deduction. Read report.md and reading-limits.md. Source bodies under private/ are ignored and must not be staged or published.

Run `python -B verify.py --expected-manifest-sha256 EXTERNAL_ANCHOR` using the anchor supplied separately by the author/parent. The verifier is read-only and does not trust a self-reported anchor. It checks exact files and directories, rejects links/nonregular nodes/hardlinks and nested manifests, and replays21 canonical source identities and4 primary pairs. These are integrity checks only.

checks/integrity-controls.json records13 disposable copied-packet controls against an intermediate seal; the final seal is verified separately with the external anchor and a wrong-anchor rejection. checks/seal.py is author tooling, not a source of trust.
