# Reproduction and integrity boundary

The archive payload is exactly packet/. MANIFEST.json records every payload file, SHA256, size and mode and every directory. FINAL.json binds that manifest, the outside REPORT.md, the public report and the two outside original programs verify.py/run_controls.py. The final response supplies detached FINAL and REPORT hashes; do not derive trusted anchors from a potentially modified packet. ANCHORS.json is an outside convenience receipt, not an independent trust source.

Use Python3 with standard library only, with the supplied detached values:

    python -B verify.py --root /absolute/path/to/this/archive --finalhash FINAL_SHA256 --reporthash REPORT_SHA256

The verifier requires both anchors, executes only from its own selected root, checks root ancestors, rejects special files/symlinks/hardlinks and exact-membership changes, checks full canonical records against the fixed-hash COMPLETE tree, recomputes Git blob/SHA256/pinned URLs/labels, and binds primary/history/search artifacts. An audit hook denies writes, process launches and network creation. It produces stdout only. Do not run a verifier from another archive against this root.

Copied controls:

    python -B run_controls.py --root /absolute/path/to/this/archive --out /absolute/path/to/this/archive/NEW-disposable-controls --finalhash FINAL_SHA256 --reporthash REPORT_SHA256

The output directory must not exist and must be inside this owned root. The runner invokes each copied verifier, preserves each copied input during verification, removes only its disposable test copies, and stores a receipt. It compares original files/directories/bytes/modes/link counts before/after, excluding only the new output directory. Cases include baseline, denied write/process probes, absent/wrong anchors, report/payload/code/manifest changes, extra/missing paths, symlink/FIFO/hardlink/root-link, a coherent reseal with the OLD anchor, and four isolated metadata/path tests using explicit synthetic NEW TEST anchors. These synthetic anchors are not evidence about the authentic archive's mathematical claims. No network or upstream body executes.

The optional public/algebra-check.py independently expands one integer polynomial identity and detects a specified wrong formula. It writes no files unless its stdout is explicitly redirected. Its receipt was generated before sealing. It is neither a universal theorem proof nor a mathematical/contribution gate.

Scratch work/ is outside the sealed payload and is not needed to verify it. Final search path lists were copied privately into packet/ and bound there. No massive snapshot of other campaigns is included: only15 selected history bodies. Private evidence retains its original rights; public originals and outside original code are the shareable boundary subject to the user's stopped-publication instruction. No upload is performed by these programs.
