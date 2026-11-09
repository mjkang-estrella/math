# R162BZ detached artifact report

Disposition: PREFREEZE/no nominee. No theorem or diagnostic frozen; no self-assigned mathematical gate or campaign count. Parent alone adopts gates/counts.

This REPORT is outside the payload manifest but remains inside the exclusive authorized root. Its own SHA256 is detached in the final handoff. The manifest includes FINAL, the read-only verifier, mathematical notes, reading limits, bindings, private source/primary/completed materials and tiny copied controls. Manifest and REPORT are the only reserved non-payload files; their full modes and exact membership are checked.

FINAL SHA256: `2c77405fc52fee37cb57316736a2a6bc23f60a7d42fc0166715f1b8e77af3de3`

MANIFEST SHA256: `f3a44315a692109055cca9eae68e457a2be349e6c69e30bfdf50989022cdb4d7`

Use the actual detached REPORT SHA256 from the final handoff as REPORT_ANCHOR below. All three anchors are mandatory arguments; the verifier does not infer them from its own inputs.

```sh
python frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bz/private/verify_packet.py \
  --root /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bz \
  --final-sha 2c77405fc52fee37cb57316736a2a6bc23f60a7d42fc0166715f1b8e77af3de3 \
  --manifest-sha f3a44315a692109055cca9eae68e457a2be349e6c69e30bfdf50989022cdb4d7 \
  --report-sha REPORT_ANCHOR
```

Run from `/home/mj-kang/Documents/Dev/math/openai-proof-research`. Verification reads only this root, the complete expressly permitted tree metadata, exact direct files/fragments and the five exact completed originals. It checks sorted unique safe membership, bytes, SHA256, full modes, copies and raw Git-blob bindings against the authenticated complete tree. Journal and catalogue access remains bounded to the authorized byte intervals. It creates no files and changes no files or modes.

The same final verifier is used for pre-seal preflight and final read-only verification. Tiny copied controls are documented in private/CONTROL-RESULTS.md. No sealed file is edited to fit verification. Authentication is not a mathematical gate.
