# Read-only verification

Run `python -B packet/notes/verify_packet.py --root <exclusive-root> --final-sha256 <FINAL-anchor> --manifest-sha256 <MANIFEST-anchor> --report-sha256 <REPORT-anchor>`.

Supply all three detached hashes from the handoff/ANCHORS.json explicitly. The verifier does not discover or trust an anchor file, write files, repair inputs, inspect originals or contact any service. It checks the three detached objects and exact packet membership, bytes and modes, including directories and exclusion of symlinks. This is artifact integrity only.

`controls/` outside packet contains three tiny copied reviewer-text fixtures. Their results are in packet/private/artifact-controls.json. They do not copy source or author bodies, do not mutate the actual sealed packet, and do not constitute mathematical tests. The selected author input manifest in packet/private authorizes exact inputs; it is not the review's manifest. MANIFEST.json outside packet is the sole fresh manifest of this review selection.
