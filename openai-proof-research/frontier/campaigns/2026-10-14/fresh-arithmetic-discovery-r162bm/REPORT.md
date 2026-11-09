# Detached seal report: r162bm

This report is outside the MANIFEST payload and inside the exclusive r162bm root. Its SHA256 is supplied separately in the handoff, together with the FINAL and MANIFEST anchors. The final verifier requires all three explicit anchors and the explicit project path; it does not obtain an anchor from the object it purports to authenticate.

Before seal issuance, records were sorted and uniqueness asserted. The SAME verify.py logic passed a complete preflight of exact safe file/directory membership, SHA256, byte lengths, FULL st_mode, original/copy equality for the seven explicitly permitted direct/completed inputs, all12 pinned-source Git blobs against the16 selected tree entries, and the unchanged frozen statement. No whole journal/catalogue read or hash was involved. FULL initial original modes are recorded; later observations of other generated files are not presented as initial capture.

Preflight result: MATCH 67 payloads, 69 total files, 10 directories including root, 5273454 payload bytes. MANIFEST.json and REPORT.md are the two control files excluded from the payload; their modes are bound in the manifest and their bytes by detached anchors. The final report replaces only the provisional preseal report; no sealed payload was altered.

Tiny copied controls used the same read-only verifier: a valid fixture matched; each of three incorrect detached anchors was rejected; a one-byte copied-payload mutation was rejected; the restored fixture matched. Exact outcomes are in private/control-results.json. The controls and all fixture mutations preceded the main seal. There was no unexpected verifier failure. These are artifact checks, not mathematical gates.

One final read-only invocation using the detached anchors verifies these finished bytes. No file is changed after seal issuance. The invocation output and detached report hash are carried in the final handoff, avoiding a self-referential report hash.

FINAL SHA256: 1b7719ac5b3f13b663d43917c3b417a39d035c729f923c2ec786ea0c3db10cdc
MANIFEST SHA256: 7b562aea83231352144c9628d01e147a58c6c2fc0c14d557c4a3b22e163d275f
STATEMENT SHA256: 6f1c7eed54c4bee7b80a56494fddfb0e5e0bcd66f0e4b9acc2a2fdb6458f5127

Author-proof nominee only. No independent correctness/contribution outcome or campaign increment. Parent alone adopts gates/counts. All protected bodies and their named metadata remain local/private. No downstream work or publication.
