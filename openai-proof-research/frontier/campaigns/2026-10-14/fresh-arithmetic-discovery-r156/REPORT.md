# Detached artifact report

This report is outside the selected payload manifest, while remaining inside the exclusive r156 root. The manifest was created once for this exact packet. It selects 85 files, including the author's frozen statement/proof, private original evidence and the read-only verifier. MANIFEST.json, this REPORT.md and the detached ANCHORS.sha256 are the three exterior objects, avoiding a circular self-hash.

FINAL.md SHA256: f54cbec3628425053feba7f617cb95e64e5bf6cdc21c164c2592413d075c4973
MANIFEST.json SHA256: f965e1aaac429f391c81020529247a7e0f3fe960861116fa1b22ff006fdd815a
FROZEN.md SHA256: 91e62de24ee1198647e25cc0ee946b8043c480a6a975280bad046be581ed7e3c

The read-only verify_packet.py requires independently supplied --manifest-sha, --final-sha and --report-sha arguments. It checks the three anchors, each selected file's size/hash and the exact selected file set, and rejects symlinks, unsafe paths and duplicate entries. It never modifies the packet. ANCHORS.sha256 is a convenience copy of detached values, not an independently trusted source for its own authentication.

Before sealing, three tiny copied controls were run with the clean control's explicit anchors. The clean copy was accepted; a changed frozen file and a missing frozen file were rejected. The original FROZEN.md and FINAL.md hashes were unchanged. Full outputs are in private/controls/RESULTS.json. These are artifact controls, not mathematical tests or review gates.

The final exact-packet verification is run after writing this detached report and anchors; its output is returned with the handoff. No post-seal payload rewrite is planned. Protected bodies/metadata stay local under their original rights. No public release, formalization, manuscript, external write, grade, acceptance or campaign count is implied.
