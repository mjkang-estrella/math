# Terminal manifest exclusions

MANIFEST.sha256 hashes every own completed file present at terminal generation, including all completed earlier receipt JSON/output files, frozen helpers and inputs, all GET/search plans and outcomes, guard hashchain/lock, search charge ledger/lock/budget, original literal records/provenance, handoff files and frozen-after evidence.

Exactly three terminal noncircular self-exclusions: MANIFEST.sha256; manifest_finish.receipt.json; manifest_finish.output.txt. The latter two are emitted by the immutable runner only after its child has generated the manifest. No other file is excluded. No further research or mutation is planned after terminal manifest generation. These exclusions are not an assertion that those two receipts have a hash within themselves.
