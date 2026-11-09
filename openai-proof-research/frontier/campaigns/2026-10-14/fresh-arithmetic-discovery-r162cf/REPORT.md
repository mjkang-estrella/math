# Detached artifact report — r162cf

Disposition: PREFREEZE/no nominee. No mathematical gate or campaign increment.

The exact payload manifest contains 68 files totaling 8062087 bytes and 14 directories including the root. MANIFEST.json and this REPORT.md are detached from that payload list, giving 70 whole-root files. Both detached files have full regular-file mode 0100644; the verifier checks that mode explicitly. Payload files and every directory have their full modes recorded.

FINAL SHA256: d171f1499625ad97b57b743a0050380beb683aad8a04f2a3ff8380114ac710fa
MANIFEST SHA256: 0f1868c6340c1332071a355594a3141ccdcc0e91c7590a15b7215459809f4c1d

The REPORT SHA256 is supplied outside this file in the handoff. No self-hash is asserted. All three explicit detached anchors are required by private/verify.py.

Before the seal boundary, the SAME verifier logic checks sorted unique exact membership, SHA256, lengths, full modes, all 26 Git blobs and 8 Git trees against the authenticated complete tree, the five exact completed originals and copies, primary acquisition bindings and the two authorized binary slices. Tiny copied controls accept the exact/restored fixture and reject byte, full-mode, extra-member and unique-unsorted mutations. Their original remains unchanged. No source truth or mathematical correctness is tested by these controls.

The seal boundary occurs only after the full explicit-anchor preflight succeeds. No sealed file is modified afterwards. The separate final verifier invocation is read-only. All artifacts, including this report outside the manifest, remain inside the exclusive r162cf root.

Read-only invocation (substitute the externally supplied REPORT anchor):
python frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cf/private/verify.py --final-sha256 d171f1499625ad97b57b743a0050380beb683aad8a04f2a3ff8380114ac710fa --manifest-sha256 0f1868c6340c1332071a355594a3141ccdcc0e91c7590a15b7215459809f4c1d --report-sha256 REPORT_ANCHOR
