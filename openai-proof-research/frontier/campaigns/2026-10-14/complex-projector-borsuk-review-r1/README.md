# Full B8C proof and contribution review, round 1

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; code MIT.
Third-party copies remain private with their original rights.

Mathematics **PASS_FULL_B8C**. Contribution **UNRESOLVED**. Counted=false;
campaign remains 4/10. Read review.md for explicit B1–B5 answers and the
full symbolic check. operation-comparison.md and
primary-reading-source-contracts.md distinguish antecedents and reading limits.
No blocking proof repair was needed; original editorial/provenance errors
are identified for a future author revision. No frozen/shared file was edited.

original-scope.md preserves the exact frozen B8C bytes. Input receipts bind
the external author package, complete pinned catalogue and original parent
historical brief. Mutable contexts are internal snapshots only. All external
mathematical primary copies are under inputs/primary/ and are private.

manifest.json lists every payload file with role, size and SHA256, and
every directory including empty directories and the root with a role.
The two metadata members are manifest.json and seal.json: the manifest is
authenticated by seal.json, whose digest must be obtained OUTSIDE this
directory. This avoids a self-hash cycle. Input/output roles share one exact
membership manifest; the exact external input list is additionally in
inputs/fixed-reference-baseline.json. The output inventory is not an
acceptance or mathematical truth certificate.

Run the inspected verifier from any working directory:

    python3 -I -B /absolute/path/to/this/review/verify.py --seal-sha256 EXTERNAL_HASH

It authenticates the external seal before JSON parsing, then the manifest
before payload parsing; rejects unsafe/noncanonical or duplicate paths and
JSON keys, symlinks/special files, bytecode, and missing/extra members; checks
the scope and all 14 pinned blobs against the complete catalogue; and
authenticates all 35 author files and five other fixed originals. It never
executes payload code, fetches network content or binds future live ledger
updates. An audit hook forbids writes, subprocesses and network connections.
Positive and wrong-anchor controls are recorded in verification-controls.json;
the final seal and replay results are reported externally at handoff.

Integrity is not proof truth or contribution acceptance. This review produces
no manuscript, Lean package, publication, upload, commit or count increase.
