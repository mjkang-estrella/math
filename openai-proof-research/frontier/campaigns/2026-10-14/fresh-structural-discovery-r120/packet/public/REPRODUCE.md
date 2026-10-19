# Integrity reproduction

Use the detached FINAL and outside-packet REPORT hashes from the handoff, not values inferred from files in an untrusted copy. From the project root:

```sh
python3 -B frontier/campaigns/2026-10-14/fresh-structural-discovery-r120/packet/public/verify.py \
  --root frontier/campaigns/2026-10-14/fresh-structural-discovery-r120 \
  --tree sources/preprints-tree.json \
  --finalhash DETACHED_FINAL_SHA256 \
  --reporthash DETACHED_REPORT_SHA256
```

The verifier is read-only. It authenticates the manifest/report, exact packet files and directories, external complete tree,26 canonical Git blobs, seven primary PDF/text pairs and eight selected historical copies. It does not fetch anything, prove a reading occurred, or assess mathematics.

The copied-control runner takes the same four arguments. It writes disposable copies and results.json only under the root's controls/ directory and runs the unchanged original verifier against each copy. Eighteen cases cover a clean copy and missing/wrong anchors, absent/changed tree, payload changes, missing/extra membership, symlinks, hardlinks, report/manifest/verifier changes, and coherent resealing against the old detached anchor. The runner checks original packet/anchor identity before and after. Its receipt remains outside the sealed packet.

No formal proof, manuscript build or mathematical finite-test reproduction is implied. The general supporting derivation and the unresolved full interface are in artin-search.md; reading-limits.md controls all semantic reading claims.
