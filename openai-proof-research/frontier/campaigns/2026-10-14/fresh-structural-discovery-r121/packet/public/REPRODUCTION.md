# Read-only authentication

Use independently supplied detached hashes, not values discovered from a modified packet. From the repository root, run:

```bash
python frontier/campaigns/2026-10-14/fresh-structural-discovery-r121/packet/public/verify.py \
  --root frontier/campaigns/2026-10-14/fresh-structural-discovery-r121 \
  --tree sources/preprints-tree.json \
  --finalhash DETACHED_FINAL_SHA256 \
  --reporthash DETACHED_REPORT_SHA256
```

Both external anchors are mandatory. The verifier does not write, repair or reseal anything. It checks the external complete tree's fixed hash before parsing all13223 entries, every retained pinned Git blob/raw URL, all acquisition retention metadata, primary PDF/text hashes, history copy hashes, exact packet files/directories, modes, single-link regular files and its own running bytes. It rejects symlink paths/ancestors and nonregular payloads. These are archive checks, not proofs, eligibility assessments or priority searches. It does not authenticate a changed source by fetching a fresh webpage.

To reproduce mutation controls on temporary copies inside this OWNED archive:

```bash
python frontier/campaigns/2026-10-14/fresh-structural-discovery-r121/packet/public/run_copied_controls.py \
  --root frontier/campaigns/2026-10-14/fresh-structural-discovery-r121 \
  --tree sources/preprints-tree.json \
  --finalhash DETACHED_FINAL_SHA256 \
  --reporthash DETACHED_REPORT_SHA256
```

This writes only controls/integrity-controls.json and temporary copies beneath controls; the copies are removed. It always executes the ORIGINAL verifier against copies. Some isolated provenance controls deliberately reseal a COPY with a new TEST anchor to reach the relevant internal check; those test hashes are not author anchors. A separate coherent-reseal control retains the old detached anchor and must reject. Wrong/truncated-tree controls fail the fixed tree hash, not an isolated completeness parser test. The original protected archive inventory is compared before/after, excluding the designated controls output directory. Byte hashes, sizes, modes, file types and link counts are protected; incidental access times are not.

FINAL-ANCHORS.json is outside packet and records FINAL, manifest, REPORT, controls and final replay hashes. The final response supplies the detached FINAL hash separately. No finite mathematical tests are claimed. This is a prefreeze archive without a theorem statement to modify or a proof to certify.
