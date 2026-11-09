# Detached review integrity report

Correctness verdict: PASS; mathematical reasons are in REVIEW.md and private/DERIVATION.md.
Artifact results are independent of that verdict.

This is the first and only seal of the review selection: 19 exact payload files,
sorted safe unique membership, lengths, SHA256 and FULL regular-file modes.
FINAL.md is in the payload. MANIFEST.json and this REPORT.md are detached outside
that payload, inside the assigned review root. Their full modes are 33188.
The same validate_payload logic passed preflight before final detached writes.
Tiny copied controls accepted a valid packet and rejected a changed payload,
changed full mode, extra file, wrong detached anchor and unsafe membership;
the copied fixture was restored and matched its original. No author verifier ran.

All 68 exact admitted author files matched the sidecar on initial and final reads.
The source authentication record binds 10 copied blobs and 5 reconstructed trees
to the supplied complete metadata and pin. This does not audit source truth.
The verifier is read-only and requires all three explicit detached anchors.
After this seal, no packet file is edited. No copied control changes occur after it.

FINAL SHA256: c611c086fc283f396300742ec632544666b3f9ebe5157dca4591738df361e1b2
MANIFEST SHA256: 4a28dc259e7cd932f37d612701d7d50709cdbf2a1d533b1b6d2fb305ebe522c5
REPORT SHA256: supplied detached in the final handoff (no self-hash).

Run from /home/mj-kang/Documents/Dev/math/openai-proof-research:
python frontier/campaigns/2026-10-14/arithmetic-r162cp-proof-r1/verify_packet.py --root frontier/campaigns/2026-10-14/arithmetic-r162cp-proof-r1 --final-sha256 FINAL_ANCHOR --manifest-sha256 MANIFEST_ANCHOR --report-sha256 REPORT_ANCHOR
