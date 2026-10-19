# Read-only integrity reproduction

Obtain detached FINAL.json and REPORT.md SHA256 values from the handoff, independently of the packet. From any directory run:

    python -B /absolute/r85/packet/public/verify.py --root /absolute/r85 --finalhash FINAL_SHA256 --reporthash REPORT_SHA256 --tree /absolute/repository/sources/preprints-tree.json

The verifier reads only. It rejects a missing anchor, mismatched exact file/directory inventory, symlinks/hardlinks, changed report/manifest, noncanonical source blobs/URLs, incomplete or unanchored tree, and inconsistent private source/primary/history receipts. Its own bytes are manifest-bound. The external tree must have the recorded canonical SHA256; authenticity of the initial detached anchors remains a trust input.

Copied controls can be rerun using the same arguments with controls.py in place of verify.py. That runner writes ONLY temporary copies under the owned root's controls-work/ and controls.json, which is outside the packet. It invokes the ORIGINAL verifier, never a mutated copy. It compares the whole original root's byte/mode/link inventory before/after, excluding only those two control-output locations. It does not reseal the original. Sixteen cases are configured: one baseline and15 expected rejections. Read controls.json for the observed result; the configured list is not itself evidence of success. Wrong external tree tests its anchored digest first, not isolated parser branches.

MANIFEST.json lists every packet file and directory. FINAL.json binds the manifest, outside REPORT.md and verifier. The handoff also gives the report hash outside packet. Neither script uses network, reruns research acquisitions or mutates shared files. No numerical mathematical test was run. Integrity says nothing about proof validity, substantiality, novelty, eligibility or campaign count. Private evidence must not be redistributed under the public original-work license.
