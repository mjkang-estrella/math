# Outside-manifest report envelope

This report, FINAL.md and MANIFEST.json are the three direct-root envelopes, excluded from the payload manifest and bound by three detached SHA256 anchors supplied in the final handoff. This is a discovery archive, not a publication/release artifact. No inherited original manifest is used.

Outcome: PREFREEZE/no nominee. Main mathematical note:DERIVATION.md. Exact obligation:GAPS.md and DERIVATION(D). Limits:READING-LIMITS.md and ISOLATION.md. Authenticated metadata:SOURCE-AUTH.json,PRIMARY-AUTH.json,ORIGINALS-AUTH.json. Private copied sources/history/search material retains original rights.

The verifier checks exact regular-file membership, lengths, SHA256 hashes, symlink absence and file hard-link multiplicity. It does not check empty-directory membership, modes, timestamps, rights or mathematics. All three detached anchors are mandatory. From the actual project root, run:

    python -B frontier/campaigns/2026-10-14/fresh-analytic-discovery-r151/scripts/verify.py frontier/campaigns/2026-10-14/fresh-analytic-discovery-r151 --manifest-sha256 <detached-MANIFEST> --final-sha256 <detached-FINAL> --report-sha256 <detached-REPORT>

The copied control is deliberately a two-payload selection with its own manifest and three envelopes. Baseline/restoration pass; changed payload, missing payload, hidden extra and incorrect detached manifest anchor fail. The verifier preserved every tested state. This control is not passed off as a full original packet. Incoming primary objects were independently re-decoded to reproduce their selected members. Original rule/history copies were re-compared to their unchanged originals; pinned object sizes/Git blobs/SHA256 were rechecked against the complete authenticated tree.

No independent correctness/contribution review, acceptance, count, formal support, manuscript, release, browser UI, publication, upload, submission or contact is claimed. The incomplete mathematical obligation and navigation/isolation defects remain visible in the sealed payload. Parent alone determines subsequent work.
