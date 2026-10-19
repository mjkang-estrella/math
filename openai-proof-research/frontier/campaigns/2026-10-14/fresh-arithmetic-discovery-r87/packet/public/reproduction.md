# Artifact boundary and reproduction

Original public research prose is provided for local parent integration, with original prose CC BY4.0 and original verification code MIT; author attribution Myeongjin Kang, no affiliation. Third-party and pinned source bodies under private/ retain their original rights and are not licensed by this notice. Public registers contain factual URLs, hashes and reading extents, not copied proof bodies. No publication is authorized by this archive.

From the owned root, run:

    python -B verify.py . --finalhash DETACHED_FINAL_SHA256 --reporthash DETACHED_REPORT_SHA256 --tree /home/mj-kang/Documents/Dev/math/openai-proof-research/sources/preprints-tree.json

The caller must obtain both detached anchors independently from the handoff. The program never infers trust from a convenience hash inside the packet and never reseals. FINAL.json is outside packet; its detached hash binds MANIFEST.json, REPORT.md, the packet report, verify.py and run_controls.py. The manifest checks exact regular-file and directory membership, modes, lengths, SHA256, links and special files. Source receipts are also matched to FULL records in the complete external tree and their Git blob SHA1, size and pinned raw URL. Primary/history/context copies are cross-checked against their registers. Read-only audit guards reject writes, process creation and network use during verification.

run_controls.py ROOT --finalhash ... --reporthash ... --tree ... creates only disposable copies beneath ROOT/controls and refuses to overwrite an existing controls receipt. It invokes the COPIED verifier with the final anchors, checks expected diagnostics, and removes only its own disposable copies. Its receipt and original-root before/after snapshots remain outside packet. Every control checks copied-input immutability, and the whole original owned root outside the controls-output subtree is checked unchanged. These are integrity tests, not mathematical tests, proof review, contribution gates or semantic reading certificates.

The construction notes are full author feasibility calculations where explicitly stated, with exact remaining gaps. They have not received independent mathematical review. No full theorem is offered for nomination and no formal or manuscript workflow should be inferred from the existence of a sealed archive.
