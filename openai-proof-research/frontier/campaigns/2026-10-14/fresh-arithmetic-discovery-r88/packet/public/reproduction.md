# Read-only authentication

From the assigned r88 root, use the detached hashes supplied separately in the handoff:

    python -B verify.py --root . --finalhash DETACHED_FINAL_SHA256 --reporthash DETACHED_REPORT_SHA256

The verifier authenticates FINAL.json before parsing its anchors, checks its own bytes and the control program, outside report/manifest, exact packet membership/modes, the complete canonical tree, full source records and retained Git blobs, primary representations and historical copies. It never downloads, writes, reseals or executes research code. Optional --tree PATH additionally compares an external complete tree to the sealed tree. It returns JSON on stdout; redirection by the caller is separate from the verifier.

Copied controls:

    python -B run_controls.py --root . --finalhash DETACHED_FINAL_SHA256 --reporthash DETACHED_REPORT_SHA256 --out controls-replay

The output path must be new and within the selected root. The runner uses disposable copies, runs the copied OWN verifier with the detached anchors, checks copied inputs and every preexisting original-root file/directory remain unchanged, removes only its disposable copies and writes one receipt. Do not rerun acquisition/search/register helpers on the sealed packet. They are scratch provenance, not verification entry points.

All checks are artifact integrity only. No mathematical theorem, reading completeness, contribution gate or campaign count follows from them.
