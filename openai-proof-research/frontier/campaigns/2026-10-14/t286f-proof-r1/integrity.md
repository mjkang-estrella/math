# T286F proof r1: inventory and reproduction

Exact inventory: no subdirectories. There are eight regular files: `report.md`, `reading-limits.md`, `author-packet-checks.json`, `independent-source-check.py`, `verify.py`, `control-tests.py`, `integrity.md`, and `manifest.json`. `manifest.json` lists every other file with its byte size and SHA256, plus the (empty) directory list. Its own SHA256 must be taken from the parent's external record (reported in the reviewer's final message), not recomputed and trusted from this directory.

Run these commands, using absolute paths:

    python3 -B /abs/t286f-proof-r1/verify.py EXTERNAL_MANIFEST_SHA256
    python3 -B /abs/t286f-proof-r1/verify.py EXTERNAL_MANIFEST_SHA256 /abs/fresh-arithmetic-discovery-r39
    python3 -B /abs/t286f-proof-r1/control-tests.py EXTERNAL_MANIFEST_SHA256

What each command checks:

- **verify.py**: rejects symlinked ancestors, hardlinks, non-regular entries and nested manifests. It requires the exact file and directory inventories. With the optional second argument, it also checks the author packet's manifest and four named files, read-only, against the fixed dispatch hashes.
- **control-tests.py**: runs 13 copied controls with reason checks: canonical, unchanged copy, payload change, deletion, extra file, extra empty directory, root symlink, ancestor symlink, hardlink, FIFO, nested manifest, adversarial self-reseal and wrong anchor. Its scratch directory is created under the system temp directory, outside this review directory and every frozen packet, and is removed on exit. Output goes to stdout only.
- **independent-source-check.py** (PACKET_DIR REPO_ROOT): read-only. It re-derives the 64 canonical blob identities from the repository's own complete `sources/preprints-tree.json`. Run it only on an authenticated disposable copy of the author packet.

All of these are byte checks. They are not mathematical evidence and do not bear on the proof verdict.
