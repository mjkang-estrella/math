# Round 6 validation

See results.json and verification/replay-report.json for the exact outcome.
The source archive is safely extracted into verification, an initially empty
lane-local directory, and every module is strictly compiled and leanchecked.
Audit6 verifies equality of inventoried and audited declarations, independently
for the endpoint closure, including generated declarations and opaque values.
LOCAL and upstream metadata are recorded separately in the audit JSONL/report.
Only propext, Classical.choice and Quot.sound are permitted for LOCAL proofs.
Four inherited negative controls test exceptional lattice isomorphism claims,
a non-equitable partition and the source order direction.
All 38 frozen sources are bound by before/after SHA-256 manifests.
Development failures are retained as failures, not counted as certificates.
This is implementation validation only. Root decides acceptance and credit.

Resource compliance qualification: see RESOURCE-NOTE.md for the brief development
audit/replay overlap, which was stopped and excluded from certification. The final
replay itself executes heavy invocations serially; perfect session-wide serial
compliance is not claimed.
