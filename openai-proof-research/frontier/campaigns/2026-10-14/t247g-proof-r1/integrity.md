# T247G proof r1: inventory and reproduction

This directory has no subdirectories and exactly nine regular files:

- `report.md`
- `reading-limits.md`
- `integrity.md`
- `author-replay.json`
- `independent-checks.py`
- `independent-checks.json`
- `verify.py`
- `control-tests.py`
- `manifest.json`

`manifest.json` lists every other file with its byte size and SHA256, plus the empty directory list and the verdict. Take its own SHA256 from the parent's external record, which is reported in the reviewer's final message. Do not recompute it here and trust the result.

Run these commands with absolute paths:

    python3 -B /abs/t247g-proof-r1/verify.py EXTERNAL_MANIFEST_SHA256
    python3 -B /abs/t247g-proof-r1/verify.py EXTERNAL_MANIFEST_SHA256 /abs/fresh-structural-discovery-r61
    python3 -B /abs/t247g-proof-r1/control-tests.py EXTERNAL_MANIFEST_SHA256
    python3 -B /abs/t247g-proof-r1/independent-checks.py /abs/fresh-structural-discovery-r61 /abs/openai-proof-research

## What each file does

- **verify.py** requires the external anchor. It rejects symlinked ancestors, hardlinks, non-regular entries and nested manifests, and it requires the exact file and directory inventories. With the optional second argument, it also checks the nine dispatch-named r61 files read-only, including the author MANIFEST.json `38b748ab…4907fd`.
- **control-tests.py** runs 13 reason-checked copied controls: canonical, unchanged copy, payload change, deletion, extra file, extra empty directory, root symlink, ancestor symlink, hardlink, FIFO, nested manifest, adversarial self-reseal, and wrong anchor. Its scratch directory is under `/var/tmp`, outside this directory and every frozen packet, and is removed on exit.
- **independent-checks.py** is read-only. It verifies the `sources/preprints-tree.json` anchor `eeecc1da…dc5e09b` and re-derives all 31 Git blob identities from that complete, nontruncated tree. It then runs reviewer-chosen finite illustrations: alternation in non-closed noncommutative subspaces of M₃(F₂) with threshold controls, exact height-sum arithmetic, and certified stopping-level samples. Its recorded output is in `independent-checks.json`.
- **author-replay.json** records the replay of the author's checks. The r61 packet was copied to `/var/tmp` and the copy was authenticated with the external anchor. The author verifier then ran with the positive and wrong anchors, followed by all 13 author integrity controls (scratch inside the copy's `checks/`, as that script requires) and `finite_diagnostics.py`, whose JSON equals the saved file. The copy was re-authenticated afterward and then deleted. `seal.py` was never run.

All of these are byte or finite checks. They are not mathematical evidence for Lemma 1, the orbit partition or universal termination, and they do not bear on the proof verdict.
