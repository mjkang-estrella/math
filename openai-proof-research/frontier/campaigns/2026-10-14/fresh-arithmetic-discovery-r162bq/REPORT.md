# R162BQ detached artifact report

Disposition: PREFREEZE/no nominee. No mathematical gates or campaign change.

FINAL SHA256: b8245a0343d4eac09380349f74b379052301ac84bd502673ae61ee9541c325c6
MANIFEST SHA256: 1c4f3ebdb701ba6144c0d52a1ee9818c039f9854fe1afd6d355d391d5e809254

Manifest: private/MANIFEST.json. REPORT.md is outside its payload and is bound by a separately supplied SHA256 anchor. All three explicit anchors are required by private/verify.py.

Payload: 67 files, 9895981 bytes. Total sealed root: 69 files and 14 directories including root. Records are sorted and unique; exact safe membership, full modes, lengths and hashes are checked. Pinned bindings cover all 13 source blobs and six complete selected trees against the expressly authorized complete-tree anchor. Six primary acquisitions and five exact completed original/copy pairs are checked. Original modes are compared with the copy-time record, not an invented pre-read snapshot.

Before creation of either reserved file, the SAME verify_packet core checked the in-memory final manifest/report and every payload/binding, with only the two not-yet-created reserved paths absent. Tiny copied controls exercised that same core, including explicit-anchor, modified-byte, mode, membership and unsafe-path rejection. The report records artifact authentication only. Final on-disk verification is read-only and uses the detached anchors printed at sealing; no sealed payload is edited to fit it.

No publication, release, mathematical correctness/contribution grade or acceptance is represented by this seal. Protected bodies and named metadata remain in private/ under original rights.
