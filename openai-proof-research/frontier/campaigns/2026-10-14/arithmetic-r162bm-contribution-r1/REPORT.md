# R162BM contribution review integrity report

Role verdict: TECHNICAL, conditional on full correctness of the entire unchanged theorem. This report concerns artifact integrity only and assigns no correctness or acceptance/count gate.

All mathematical work is complete in FINAL.md and private/ASSESSMENT.md, with actual-primary comparison and reading limits alongside. All author originals were rehashed at the end: exactly 69 regular files match their supplied SHA256, lengths and full st_mode, and the exact authorized membership is unchanged. Hash-only excluded bodies were not semantically admitted. The user-supplied detached author FINAL/MANIFEST/REPORT anchors also match, as recorded in the private integrity records.

The read-only verify.py uses an exact, unique, sorted membership manifest, full integer st_mode for every file and directory including root, byte lengths and SHA256 for payload files. It rejects symlinks, hard links, nonregular members, unsafe paths, duplicate JSON keys/records, extra or missing members, altered bytes/modes, and wrong explicit detached anchors. It reads only the selected packet and never opens author inputs or writes files. FINAL is both a payload record and independently anchored. MANIFEST.json and this outside REPORT.md are intentionally excluded from recursive payload hashes; their exact membership/full modes are recorded and their contents are bound by separate explicit detached anchors. No inherited manifest is used.

Tiny copied controls use exactly the same verify function: valid fixture accepted; wrong detached manifest anchor, one-byte copied-payload corruption and changed full mode each rejected; restored fixture accepted. The fixture contains only two 128-byte copied snippets and its own small manifest/report. Control outcomes and fixture anchors are recorded in private/control-results.json. These are integrity controls, not mathematical evidence.

Before issuing any seal, the SAME verifier logic was run against the complete actual packet with mutable draft manifest/report. It returned:

    {"directories": 4, "files": 25, "integrity": "MATCH", "mathematical_gate": false, "payload_files": 23}

Only this detached report was finalized after that preflight; its new explicit anchor is checked in the seal call. The manifest and all payload bytes remained fixed. The packet is sealed once, when the final three anchors are issued. No byte or mode is changed thereafter to make a verification succeed.

Detached FINAL SHA256: `700f2be828c96125bd0ad833c2a5f00242c73e29bc93c2bd50c16bd27573a926`
Detached MANIFEST SHA256: `50f47982776d04f4b8b7b9f68876faa380c5e9500810ef5ec00272ba53d0dda1`
This outside REPORT SHA256 is furnished separately in the final handoff to avoid a self-reference.

Run from the project root (read-only):

    python frontier/campaigns/2026-10-14/arithmetic-r162bm-contribution-r1/verify.py --root frontier/campaigns/2026-10-14/arithmetic-r162bm-contribution-r1 --final-sha <detached FINAL SHA256> --manifest-sha <detached MANIFEST SHA256> --report-sha <detached REPORT SHA256>

All protected source/primary material and named metadata remain private/local under original rights. No publishing, uploads, git operations, peer consultation, history scan, nested agent or downstream manuscript/formal/release work was performed. See private/READING-LIMITS.md for actual extents, recovered truncation, late BXY chronology, network and ancestry limits.
