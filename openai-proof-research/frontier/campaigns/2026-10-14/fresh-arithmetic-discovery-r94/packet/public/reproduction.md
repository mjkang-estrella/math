# Artifact verification

Use the detached FINAL SHA256 and outside REPORT SHA256 supplied in the handoff, not values recomputed from an untrusted packet.

    python3 -B ROOT/packet/code/verify.py --root ROOT --tree PROJECT/sources/preprints-tree.json --final-sha256 DETACHED_FINAL --report-sha256 DETACHED_REPORT

The verifier reads only; an audit hook rejects writes, filesystem mutation, process creation and network connection. It checks: detached FINAL and REPORT bytes; FINAL bindings (pin, tree digest, outside REPORT, manifest, verifier, public report, controls script); the exact MANIFEST set of every payload file (bytes, SHA256, permission mode) and every directory including the packet root; rejection of symlinks and multiply-linked files; the complete external tree (13,223 entries, untruncated, fixed SHA256); every canonical record against the tree, its pinned raw URL, retained body SHA256 and Git blob; primary pdf/text pairs; context/history copies; renders.

Copied controls: `python3 -B ROOT/packet/code/controls.py` with the same four arguments. It creates only ROOT/control-work, copies the sealed inputs per case, runs each copied unchanged verifier, snapshots copied inputs before/after, compares the actual author root (excluding control-work) before/after all cases, removes control-work, then writes ROOT/integrity-results.json (outside the packet; hash it separately). Fourteen cases: one intact baseline and thirteen expected rejections.

These are artifact checks only. They test no theorem, establish no contribution, assign no count. There are no finite mathematical experiments in this round.
