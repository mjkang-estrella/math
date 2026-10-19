# Artifact verification

Run the selected `packet/public/verify.py` with Python3 and `-B`, supplying:

    --root /absolute/path/to/fresh-arithmetic-discovery-r91
    --tree /absolute/path/to/sources/preprints-tree.json
    --final-sha256 DETACHED_FINAL_HASH
    --report-sha256 DETACHED_REPORT_HASH

Use hashes supplied outside the packet, not hashes freshly derived from an untrusted copy. FINAL.json authenticates REPORT.md outside the packet and MANIFEST.json inside it. The manifest then binds the exact packet, including the verifier and control runner. Verification does not write or repair files.

`packet/public/controls.py` takes the same arguments. It creates disposable copies only under this owned root's control-work, applies18 baseline/mutation cases, invokes the selected copied verifier, checks copied input preservation, removes the disposable copies and writes integrity-results.json outside the packet. It compares the whole original root before/after, excluding only its transient control-work and the receipt. That receipt has a separate detached hash.

The18 cases comprise baseline success and17 rejections: payload change/deletion, extra file/directory, manifest/FINAL/REPORT changes, wrong detached anchors, verifier change, canonical metadata/primary/copied-tree/history changes, symlink, hardlink and file-mode change. Most tampering cases are rejected by an enclosing byte seal. They do not independently exercise every semantic metadata parser, nor prove a hostile-code sandbox or resistance to concurrent filesystem changes. No mathematical finite tests were run. The prose calculations are author reasoning, not independent mathematical review.
