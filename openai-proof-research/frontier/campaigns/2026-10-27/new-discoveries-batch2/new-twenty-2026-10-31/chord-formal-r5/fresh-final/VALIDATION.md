# Validation receipts

The initial strict merged rebuild log is `logs/merge-rebuild.log`. It compiled and leanchecked all 138 inherited modules and the new erasure setup. The first graph compilation exposed API and warning errors; its failed log is retained, and its erroneous elaboration was never marked successful. The corrected graph and final endpoint passed in `logs/new-rebuild.log`. The end-face bridge and resulting final endpoint/audit rebuild are in `logs/endface-rebuild.log`.

Every successful marker is a source digest written only after both strict Lean compilation and explicit-module leanchecker success. Module hashes and line counts are in results.json. All inherited hashes must match frozen/manifest.json.

The audit checks the exact import closure of Chord5Final using opaque bodies and generated declarations, rejects forbidden LOCAL flags and transitive axioms, and separately records upstream metadata in audit5.jsonl. Results totals and exact-closure status are in results.json. Endpoint axiom prints are retained in the strict compiler logs.

Fresh extracted replay status is recorded in results.json and `logs/fresh-final-replay.log`. Source ZIP extraction includes no build artifacts or success markers. All compiler/checker/Python calls use the lane-local RSS watchdog wrapper with the prescribed caps. No child agents, git operations, publication, uploads, browser tabs or external messages are used. Root alone decides acceptance.

The preliminary extracted replay was intentionally stopped at a module boundary after the five-chord rigidity preparation was added. It is not counted as a completed replay. `logs/rigidity-rebuild.log` records the successful new finite-dihedral and chosen-triangle proofs, final endpoint and renewed audit. The final frozen packet is extracted into the separate, initially empty `fresh-final` directory for the complete replay. No build artifacts or markers are seeded into that directory.
