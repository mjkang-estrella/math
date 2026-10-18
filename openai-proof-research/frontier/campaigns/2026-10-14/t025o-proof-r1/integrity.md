# T025O54 proof r1: inventory and reproduction

This directory has no subdirectories and exactly eight regular files:

- `report.md` (the verdict, PASS_FULL_T025O, and the full audit)
- `reading-limits.md`
- `integrity.md`
- `independent-checks.py`
- `independent-checks.json`
- `verify.py`
- `control-tests.py`
- `manifest.json`

`manifest.json` lists every other file with its byte size and SHA256, plus the empty directory list and the verdict. Take its own SHA256 from the parent's external record, which is reported in the reviewer's final message. Do not recompute it here and trust the result.

Run these with absolute paths:

    python3 -B /abs/t025o-proof-r1/verify.py EXTERNAL_MANIFEST_SHA256
    python3 -B /abs/t025o-proof-r1/verify.py EXTERNAL_MANIFEST_SHA256 /abs/fresh-arithmetic-discovery-r54
    python3 -B /abs/t025o-proof-r1/control-tests.py EXTERNAL_MANIFEST_SHA256 /abs/fresh-arithmetic-discovery-r54
    python3 -B /abs/t025o-proof-r1/independent-checks.py /abs/fresh-arithmetic-discovery-r54 /abs/openai-proof-research

## What each file does

- **verify.py** is adapted from `t247g-proof-r1/verify.py` (SHA256 `7e627001…0ced2e`); only the author table and labels changed. It requires the external anchor. It rejects symlinked ancestors, hardlinks, non-regular entries and nested manifests, and requires the exact file and directory inventories. With the optional second argument, it also checks read-only that the seven dispatch-anchored r54 files match, including the author `manifest.json` `e32e49cd…ddd3`.
- **control-tests.py** is adapted from `t247g-proof-r1/control-tests.py` (SHA256 `482b9673…69642f`). It runs 14 reason-checked copied controls: canonical, unchanged copy, payload change, deletion, extra file, extra empty directory, root symlink, ancestor symlink, hardlink, FIFO, nested manifest, adversarial self-reseal, wrong anchor, and a mutated copy of the author packet. Each rejection must contain its expected reason string. Scratch lives under `/var/tmp` and is removed on exit. Its output is reported externally, not stored here, so that the seal is not circular.
- **independent-checks.py** is reviewer-written. It is read-only on its inputs, and its author-verifier replay uses a `/var/tmp` copy. It checks the seven author anchors and recomputes the 12 non-PDF source025 Git blob identities from the repository's `sources/preprints-tree.json` (anchor `eeecc1da…dc5e09b`, 13223 entries, nontruncated). It then runs exact checks of the constant slack and the templates, plus finite illustrations: a toy valuation-separated merge, constrained-step interval equivalence against brute force, odd-prefix invariants with a small T, and small-k obstruction inequalities. Finally it replays the author verifier (positive, wrong anchor, payload mutation). The recorded output is `independent-checks.json`.

All of these are byte or finite checks. They are not mathematical evidence for the asymptotic theorem and do not bear on the proof verdict, which rests on `report.md`.
