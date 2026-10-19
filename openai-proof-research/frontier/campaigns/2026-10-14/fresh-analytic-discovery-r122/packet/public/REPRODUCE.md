# Integrity reproduction

Obtain the detached FINAL and report SHA256 values from the parent handoff or author message outside this packet. Do not compute a fresh FINAL hash from an untrusted archive and treat it as the trust anchor. `HANDOFF.md` is a convenience record outside the packet, not a substitute for an independently received anchor.

From the project root, using the actual absolute owned directory as ROOT:

```sh
python -B "$ROOT/packet/public/verify.py" "$ROOT" \
  --finalhash DETACHED_FINAL_SHA256 --reporthash DETACHED_REPORT_SHA256 \
  --tree /home/mj-kang/Documents/Dev/math/openai-proof-research/sources/preprints-tree.json
```

The verifier requires both anchors; binds FINAL to the exact manifest and report; checks every packet file, byte length, mode and directory; rejects nonregular files, symlinks and hard links; and independently matches retained source bodies to the canonical complete tree and pinned raw URLs. It checks primary pairs and historical/context receipts. It does not run acquisition scripts, network requests or mathematics. An audit hook denies ordinary writes, mutations, process creation and network calls.

The copied-control runner takes the same anchor arguments plus `--out` pointing to a **fresh** directory inside ROOT, outside packet, with an existing parent directory. The author used `work/final-controls`. It constructs and runs each case on a disposable copy, compares that copy before/after verification, deletes the disposable copy, and retains the receipt. The original preexisting tree is compared before/after, excluding only the new output directory; directory timestamps and link counts affected by creating that output are not part of this comparison. File bytes, types, modes, regular-file link counts and existing membership are included.

The cases comprise one successful baseline and rejection of wrong anchors, changed/missing/extra payloads, extra directories, file/directory mode changes, symlink, hardlink, FIFO, changed manifest/FINAL/source/primary/history/verifier, wrong tree, and coherent resealing with the old detached anchor. Two injected probes in copied verifier scripts test actual write/process denials before normal verification. The probes are deliberately modified copies, never the original verifier. Rejection from a first hash check is not claimed as isolated coverage of every deeper parser branch.

```sh
python -B "$ROOT/packet/public/controls.py" "$ROOT" \
  --out "$ROOT/work/a-fresh-controls-directory" \
  --finalhash DETACHED_FINAL_SHA256 --reporthash DETACHED_REPORT_SHA256 \
  --tree /home/mj-kang/Documents/Dev/math/openai-proof-research/sources/preprints-tree.json
```

The manifest does not cover the external anchors, scratch work or generated receipts; FINAL binds the exact packet manifest, and the detached FINAL hash binds FINAL. This avoids a circular self-authentication claim. No integrity result is a mathematical gate.
