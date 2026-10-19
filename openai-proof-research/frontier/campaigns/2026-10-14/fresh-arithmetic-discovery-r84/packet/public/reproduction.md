# Integrity reproduction

From the owned r84 directory, use the DETACHED FINAL and REPORT SHA256 values supplied in the handoff, not hashes freshly derived from untrusted replacement anchors:

    python -B packet/public/verify.py --root . --tree /home/mj-kang/Documents/Dev/math/openai-proof-research/sources/preprints-tree.json --finalhash FINAL_SHA256 --reporthash REPORT_SHA256

The verifier is read-only: it uses no network, subprocess, bytecode output or repair. It authenticates exact packet files/directories, single-link regular files, all bytes, its own code, the complete external tree,32 pinned source records, seven primary pairs and retained context/history/search identities. Context identities without a copied snapshot are references, not recursively rechecked live files. It does not authenticate mathematical truth or semantic reading.

Optional copied integrity controls:

    python -B packet/public/run_copied_controls.py --root . --tree /home/mj-kang/Documents/Dev/math/openai-proof-research/sources/preprints-tree.json --finalhash FINAL_SHA256 --reporthash REPORT_SHA256

The runner writes only controls/ inside this root, creates full disposable copies without hardlinks to the original, invokes the original verifier on them and removes the copies. Sixteen cases cover baseline and missing/wrong anchors, changed/missing/unlisted payloads, unlisted directories, symlinks/hardlinks, manifest/report/verifier changes, an incorrect external tree and coherent resealing against the old detached anchor. It compares original bytes, modes and link counts before/after; its receipt is outside packet. Integrity controls are not mathematical gates. Historical initial acquisition scripts remain private and are not portable/full research replay tools.
