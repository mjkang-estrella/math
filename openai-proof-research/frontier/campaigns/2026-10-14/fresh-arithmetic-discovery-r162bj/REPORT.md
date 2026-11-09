# Detached artifact report: r162bj

Disposition: PREFREEZE / no nominee. No mathematical grade or count.

FINAL SHA256: 259a81d279b9d5389763e59f6849d3d81536b7ac8a6369c7902cb1a45ea32729
FINAL bytes: 2947
FINAL full mode: 0o100644
MANIFEST SHA256: 78d645f3a2f0772faa32bdb2da46766183067148b9fd05bb27beecbff52e73f7
MANIFEST bytes: 18145
MANIFEST full mode: 0o100644

Payload records: 65
Payload bytes: 4889217
Directories including root: 20
Whole-root files including this report and manifest: 67

The manifest binds the exact sorted unique file membership, lengths, SHA256 and full modes of every payload, including FINAL and the read-only verifier. It also binds directory membership and full modes. This report is outside the manifest to avoid a circular hash. The report SHA256, byte length and full mode are detached in the terminal handoff.

The same verifier logic is preflighted before the seal declaration. Thereafter no sealed payload is edited. Its source checks authenticate all selected Git blobs AND tree nodes. Its completed-original checks compare the five exact copies with the originals, initial hashes/lengths/permissions and the explicitly later full-mode record. The initial full-mode limitation remains disclosed.

Verifier: private/verify_packet.py, using explicit --root, --project, --final-hash, --manifest-hash, --report-hash, --manifest-bytes, --report-bytes, --manifest-mode and --report-mode. It is read-only and rejects membership or binding mismatches. Tiny copied controls are preserved under private/controls. Artifact checks are not mathematical review gates.
