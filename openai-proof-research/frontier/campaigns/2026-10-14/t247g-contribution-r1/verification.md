# Verification of this packet

The final MANIFEST.json SHA256 is reported OUTSIDE this packet, in the reviewer's message to the parent. A packet cannot authenticate itself.

    python3 -B verify.py --expected-manifest-sha256 <externally reported hash>

`verify.py` requires the anchor argument and rejects any value that is not 64 lowercase hex digits. It then checks the following:
- No symlinks, FIFOs or other nonregular nodes, and no hardlinked files.
- No nested MANIFEST.json.
- The exact file and directory inventory, and every payload's size and SHA256.
- The classification line of review.md and the recorded author anchor.
- The three primary PDF/text receipts.
- The three upstream receipts, including Git blob SHA1s and pinned URLs.

These checks cover identity only. They establish no mathematics, contribution status or acceptance.

`private/` holds third-party and upstream bodies and is git-ignored (`.gitignore`). The verifier requires these files, so it passes only on the full local packet, not on a git checkout without `private/`.

## Controls

    python3 -B checks/controls.py --root <packet> --expected-manifest-sha256 <hash> --scratch <new dir outside packet>

The script authenticates the packet first. It then runs 19 cases on fresh disposable copies and checks each rejection reason against the mutation that caused it. The cases are:
- `positive_copy` (expected to pass).
- Wrong anchor and malformed anchor.
- Changed review and changed private body.
- Missing payload, extra file, extra private file and extra empty directory.
- Root symlink, payload symlink, payload hardlink, FIFO and nested manifest.
- A self-resealed copy checked against the original external anchor.
- Four resealed semantic mutations, each checked against its own new manifest hash: classification line, author anchor record, a primary body and an upstream body. These are rejected by the corresponding semantic check, not by the hash check.

The scratch directory is removed afterwards.

`checks/controls-result.json` records the run on the intermediate packet, which was sealed in `/var/tmp` before that file was added. The controls and the positive/wrong-anchor checks on the final sealed packet are reported externally with the final hash.

`checks/seal.py` writes MANIFEST.json only when none exists. It was run once, on this unsealed packet. It was never run on the author or intake packets.

The author-packet controls replay (run in an authenticated `/var/tmp` copy) is recorded in `author-controls-replay.json`.
