# Detached artifact report — r138

This report is outside the manifest payload and has its own detached SHA256 anchor, as does FINAL.md. It is not an independent mathematical review or an acceptance report.

The packet is newly selected and sealed for fresh-arithmetic-discovery-r138. private/MANIFEST.json lists every payload file by exact relative path, byte length and SHA256. The four envelope files FINAL.md, REPORT.md, private/MANIFEST.json and ANCHORS.json are deliberately outside that payload. FINAL, MANIFEST and REPORT must be authenticated using the explicit external anchors in the handoff. ANCHORS.json is a convenience copy, not a trust source used by the verifier. No inherited manifest is attached to this selection.

Before sealing, all23 canonical SOURCE203 objects (443522 bytes) and4 fetched companion objects were rechecked against their saved pinned-tree size/Git-blob/SHA256 bindings. This authenticates copied artifacts; it does not test source truth. The complete-tree identity and exact semantic read limits are in private/READING.md. Protected source, primary, history, search and metadata objects are private/local under their original rights. Copied controls also stay private.

A tiny copy of the canonical field main was used for six artifact-only controls: valid copy, one-byte corruption, missing payload, path escape, wrong detached anchor, and restored copy. The verifier accepted the valid/restored copies and rejected each deliberately invalid case. The original source and the original project history were never mutated. Control observations are in private/controls/observations.json; source binding observations are in private/artifact-observations.json. No expanding test suite or mathematical self-gate was created.

The final read-only verification command uses verify_packet.py with --root and the three explicit --final-sha256, --manifest-sha256 and --report-sha256 arguments. It reads all listed files, rejects symlinks/unsafe paths/duplicates, checks exact payload membership and all hashes, and writes no files. The manifest was generated once after these notes and controls were final; the external tool response records the subsequent read-only verification. No report mutation is needed to record that response.

Research outcome: PREFREEZE/no nominee, with a complete local finite-precision feasibility calculation and explicit uniform denominator, but without the additional global effective realization/recognition construction. No mathematical grade, acceptance or count is assigned.
