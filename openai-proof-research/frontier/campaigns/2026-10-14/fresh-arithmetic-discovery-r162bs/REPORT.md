# R162BS detached artifact report

PREFREEZE / no nominee. No mathematical gate, contribution grade, acceptance or count.

This REPORT is outside the payload manifest and has its own detached SHA256 anchor. The manifest is also detached from its payload. All three anchors must be supplied explicitly to the read-only verifier; a hash embedded in this report is not a substitute for its external anchor.

Payload: 52 files, 10575776 bytes. Whole root including manifest/report: 54 files and 8 directories including root. Records are sorted and unique. Full file/directory modes are recorded. Source12blobs/15entries and the five exact completed original/copy pairs are bound. Primary acquisition bytes are bound separately within the payload.

FINAL SHA256: 298f80af61499201df1e01ee36218d8bfe374fdbe51d325edb008297c3251611

MANIFEST SHA256: 3e7903cf07a3a12a4b9fc4b7cc87c9f0179c84ba742f1b16be628403af0161fb

The identical final validation logic was preflighted with the exact manifest/report bytes in memory before writing either detached file. Tiny copied byte/mode controls, three wrong-anchor controls, and duplicate/unique-unsorted record controls were rejected; baseline and restored baseline matched. See private/CONTROL-RESULT.md. The final seal is written once using exclusive file creation. The immediate post-seal verification result and detached REPORT SHA256 are returned in the handoff; no sealed payload is edited to fit the verifier.

Run from /home/mj-kang/Documents/Dev/math/openai-proof-research:

```bash
python -B frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bs/private/verify.py \
  --root frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bs \
  --final-sha256 298f80af61499201df1e01ee36218d8bfe374fdbe51d325edb008297c3251611 \
  --manifest-sha256 3e7903cf07a3a12a4b9fc4b7cc87c9f0179c84ba742f1b16be628403af0161fb \
  --report-sha256 REPORT_ANCHOR_FROM_HANDOFF
```

The verifier reads only this root, the explicitly authorized complete tree metadata, and the five exact completed originals. It does not read/hash a shared journal, inventory other task namespaces, perform network calls or write files. Use -B to suppress Python cache creation. Artifact authentication does not establish mathematical correctness, substantial contribution or exhaustive isolation.
