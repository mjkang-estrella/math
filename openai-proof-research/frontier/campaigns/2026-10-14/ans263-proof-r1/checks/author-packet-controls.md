# Author-packet integrity controls (reviewer-run, 2026-10-17)

Packet: `frontier/campaigns/2026-10-14/fresh-analytic-discovery-r32` (not modified).

Pre-execution inspection: `verify.py` was read in full before running. It requires `--anchor` (argparse `required=True`), checks lowercase-hex form, refuses symlinked root/ancestors and an unsafe manifest, and compares the manifest SHA256 with the caller's anchor BEFORE parsing any other input. It then checks the exact file/directory inventory (no symlinks, no hardlinks, no nonregular files), the 55 pinned Git blobs against the retained complete tree (13223 entries, `truncated: false`), the Lean doc blob, two primary PDF→text regenerations via `pdftotext -layout`, the scope/proof freeze hashes, and a subprocess replay of `exponent_checks.py`. It writes nothing. `exponent_checks.py` was read in full; it uses `assert` and must run without `-O` (verify.py invokes it with `sys.executable` without `-O`).

Direct SHA256 of anchored files (reviewer `sha256sum`):

- manifest.json `0e1af1b06709a0585a8724e3a15e59e228a65f4c88ee363ef88e7aa482c73cf2` (matches external anchor)
- 263-working-proof.md `eef51e8d50cfaf29c971e346cc4f2957f40dfe033bda3de3d2543586879c7a48` (matches)
- 263-scope.md `03dd0d2eb2987fbc87bf130b7fe1978caa1755e7eb0286f616fc6ccfe13cf5fc` (matches)

Runs (`python3 -B verify.py ...` from inside the packet):

| Control | Anchor | Result |
|---|---|---|
| positive | external manifest hash | exit 0, `PASS_INTEGRITY_ONLY`, 79 payload files, 17 dirs, 55 pinned preprint blobs, 1 doc blob, 2 PDF bindings, arithmetic replay PASS_NONPROOF |
| wrong anchor | 64 zeros | exit 1, `FAIL: external anchor mismatch` |
| wrong anchor | hash of 263-working-proof.md | exit 1, `FAIL: external anchor mismatch` |
| missing anchor | none | exit 2, argparse error |
| copied positive | external hash, `--root` = copy under this review's `checks/` | exit 0 |
| mutated copy | one trailing space appended to copy's proof | exit 1, `FAIL: exact file inventory/hash mismatch` |

The copy was made under `ans263-proof-r1/checks/author-copy` (not /tmp) and deleted immediately after these two runs. `exponent_checks.py` stdout equals `exponent-checks.json` (reviewer comparison: True).

Independent cross-checks: `sources/preprints-tree.json` and the packet's `private/context/preprints-tree.json` have identical SHA256 `eeecc1da…dc5e09b`, and the two `upstream.json` copies have identical SHA256 `3784eb61…b5f30c` (pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). All 41 `263-source-receipts.json` local bodies re-hash (git blob SHA1) to the project tree's blob ids.

These are byte-integrity controls only. They do not validate any mathematics.
