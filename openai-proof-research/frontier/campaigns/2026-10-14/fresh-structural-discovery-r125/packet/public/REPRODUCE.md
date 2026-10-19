# Read-only authentication

From any directory, run Python3 on public/verify.py with --root pointing to the owned r125 directory and BOTH --finalhash and --reporthash copied from the external handoff. Do not derive trust by reading purported expected hashes from inside the packet. FINAL.json is outside packet and binds its exact MANIFEST.json, the outside REPORT.md and the principal payloads. The verifier uses the private complete canonical tree at its fixed SHA256; network access is unnecessary.

    python /path/to/r125/packet/public/verify.py --root /path/to/r125 --finalhash DETACHED_FINAL_SHA256 --reporthash DETACHED_OUTSIDE_REPORT_SHA256

To reproduce copied integrity controls, use a NEW output name under that root:

    python /path/to/r125/packet/public/controls.py --root /path/to/r125 --out fresh-replay --finalhash DETACHED_FINAL_SHA256 --reporthash DETACHED_OUTSIDE_REPORT_SHA256

The controls runner writes disposable copies and a receipt ONLY in that new output subtree. It does not modify the original sealed inputs. A before/after snapshot includes every preexisting owned file and directory except the new output subtree, including original scratch. The root directory is snapshotted after creation of the new output directory so its link count is stable. Permission-denied copied files and inaccessible copied directory entries are recorded as unreadable when the host honors their mode. The original tree has no such inaccessible payloads.

For the optional finite diagnostic:

    python /path/to/r125/packet/public/finite_disintegration.py

Compare stdout with finite-disintegration.json. This exhaustive tiny-grid check is not a mathematical gate. Neither verifier nor controls executes it. The proof, full scope and contribution comparison require independent mathematical review regardless of all integrity results. No formal or manuscript build is included.

The first control-run preparation stopped because its snapshot tried to lstat children of a deliberately non-executable copied directory. The runner was corrected to record inaccessible entries, and the packet was resealed before the final controls. Scope and proof bytes did not change. The failed disposable copy was removed only inside this owned root.
