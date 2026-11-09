# Actual verification receipt

The fresh source-only replay passed. The extraction initially contained no
prebuilt artifacts. Its actual receipt is `replay-receipt.json`; the complete
extraction and logs are under `verification/fresh/`. Every proof build emitted
an empty diagnostic log. All interface, exhaustive type/axiom audit, and
module-origin/safety logs reproduce the development build byte-for-byte.

Maximum sampled process-tree RSS in this replay: **3110004 KiB**,
below the supplied 3145728 KiB guard. Total retained replay diagnostics:
**109048 bytes**, below 512 MiB. No address-space cap was used.

Source-only deterministic archive SHA-256:
`dc7a93b6b331744a7e693fa4a83e2aec9300198075ade7f7b8fcb3b6779cc032`.

`packet/replay-receipt.json` is a deterministic normalized attestation; the raw
receipt retains actual timing, sampling and RSS measurements. The archive was
regenerated in memory with identical bytes. `fresh-log-comparison.json` records
the output hashes. `frozen-source-check.json` verifies original import hashes
before/after and byte identity of their lane copies.

Only propext, Classical.choice and Quot.sound occur in the actual axiom
reports for all five new mathematical modules, including generated auxiliaries.
All module-origin declaration safety flags are false. There are no mandatory
formal gaps in this component. Full SourceClaim assembly remains outside scope.
