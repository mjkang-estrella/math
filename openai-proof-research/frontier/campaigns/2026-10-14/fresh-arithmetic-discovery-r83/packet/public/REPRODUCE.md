# Read-only authentication

The verifier and copied-control harness are adapted from arithmetic r82, preserving its MIT / Myeongjin Kang attribution. They authenticate bytes and exact packet membership, not mathematics.

From the repository root, use the detached FINAL hash in the handoff (do not derive the supposedly trusted hash from the untrusted packet):

```sh
python -B frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r83/packet/public/verify.py --root /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r83 --finalhash DETACHED_FINAL_SHA256
```

`FINAL.json` authenticates the outside-packet REPORT.md and MANIFEST.json. The manifest requires every packet file and directory, rejects additions/deletions/symlinks, and binds the verifier itself. Canonical-selection.json records the complete tree digest and selected entries; source identities are recomputed with Git blob headers. Primary and history identities are checked separately. The verifier performs no writes, retrieval, repair, reseal, or mathematical test.

The copied controls run with the SAME ORIGINAL verifier and the same detached hash. They mutate only disposable copies under this root's controls directory; a coherent local reseal must still fail against the old anchor. The harness inventories the whole original root excluding its controls output before/after, including work files, sealed packet and detached anchors.

```sh
python -B frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r83/packet/public/run_copied_controls.py --root /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r83 --finalhash DETACHED_FINAL_SHA256
```

These are integrity controls only. Their success assigns no correctness, contribution, eligibility, formal, publication or acceptance gate.
