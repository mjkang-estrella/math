# Artifact verification

Use the detached FINAL SHA256 and outside REPORT SHA256 supplied in the handoff, not values recomputed from an untrusted candidate packet. From any working directory:

    python -B ROOT/packet/code/verify.py --root ROOT --tree PROJECT/sources/preprints-tree.json --final-sha256 DETACHED_FINAL --report-sha256 DETACHED_REPORT

The verifier reads only. Its audit hook rejects writes, mutation and network/process initiation by the verifier. The complete external tree must match the fixed SHA256 and contain exactly 13,223 untruncated entries. The verifier checks full canonical records and raw URLs, retained Git blobs and SHA256, primary/text pairs, context copies and renders. The exact manifest lists every payload file, byte length, SHA256 and permission mode, and every directory including packet root. Symlinks and multiply linked payload files are rejected. FINAL binds the manifest, verifier, public report and outside REPORT. Modes for FINAL/REPORT/MANIFEST themselves are not anchored; their bytes and single-link regular-file type are checked.

For copied controls, run code/controls.py with the same four arguments. It creates only ROOT/control-work, copies the sealed inputs, and invokes each copied, unchanged verifier. Fourteen cases comprise an intact baseline and thirteen rejection controls. Every copied input is snapshotted before and after verification. The actual author root is compared before and after all replays, excluding only the transient control directory; the receipt is written afterward at ROOT/integrity-results.json. That receipt is outside the sealed packet and must be separately hashed. Rejection controls use the original detached anchors and are not independent tests against an adversary able to change trusted anchors. No exhaustive OS sandbox or audit-denial probe suite is claimed.

All these checks concern artifacts. They do not check a theorem, establish contribution, assign a count, or license publication. There are no finite mathematical experiments in this round.
