# Detached review seal report — R162BM proof round 1

Correctness-review verdict: PASS for the entire unchanged statement/proof relative to stipulated Source146 operative truth. No contribution, acceptance or count is assigned. Detailed reasons and actual reading limits are in FINAL.md and the private review notes. Integrity results below are not mathematical gates.

This REPORT is outside the MANIFEST payload and inside the exclusive review root. FINAL, MANIFEST and REPORT each require their own explicit detached SHA256 in verify.py. The verifier reads only the selected root and writes nothing; it does not obtain trusted anchors from an object being authenticated. Its own full mode is read-only (0444 permission bits, regular-file type).

The SAME check() implementation passed the complete main-packet preflight before this seal, including exact safe membership, sorted unique records, all SHA256 values/lengths, FULL file and directory modes, frozen statement/proof hashes, all twelve source Git blobs, all four source directory Git trees, and the captured pinned-commit/root-tree binding. Preflight used the final payload bytes and manifest; only this separately anchored report was provisional. No sealed byte has been changed to make verification pass.

Preflight result: {"directories_including_root": 9, "payload_bytes": 2262559, "payload_files": 57, "review_bindings": true, "total_files": 59}

Tiny copied controls passed using the same read-only check(): valid fixture accepted; each of three wrong detached anchors rejected; one-byte copied-payload mutation rejected; restored fixture accepted. All fixture mutations and control-result writes preceded main preflight and sealing. Their exact results are in private/control-results.json. No unexpected preflight/control failure occurred.

An earlier reviewer source-directory authentication code failure and its recovery are separately preserved in private/authentication-recovery.txt. It occurred before preflight, came from incorrectly selecting the root as its own child, and did not reflect a source byte mismatch. The initial outer output truncation and full recovery of the author reading record are disclosed in private/READING-LIMITS.md. No failed network access occurred: only two exact pinned GitHub metadata requests were made, both successful.

Immediately before seal preparation, all 69 author originals were rehashed and compared with the initial records: bytes, lengths, full modes, file/directory membership and the authorization metadata were unchanged. Hash-only exclusions were not decoded or used as mathematical premises. No author verifier was executed, and no linked older original or peer was read.

FINAL SHA256: 477230d5e755df6dc3d44a079819dfa1671925033499aa2365772cd1b023a099
MANIFEST SHA256: 8ecbfecab4729a24f878ac6d178d53a7fbcb6670960ea52215de92a1a454c706

REPORT SHA256 is detached in the tool/final handoff, not placed into itself. The finished packet is verified once more read-only against all three detached anchors. After issuance of those anchors, no packet byte or mode is changed. The final handoff contains the verification outcome without creating a post-seal file.
