# T298P full manuscript review, round 4

Verdict: **PASS_FULL_MANUSCRIPT_T298P** for the active `t298p-manuscript-r2` manifest `afc2c2ad6ecd45ef9958092c343e99b9d2804cb8f771a3d54cccae3e426393dc`. Required list is explicitly empty. See review.md for both old required-item resolutions, the full retained theorem and proof audit, and one optional prose finding; verdict.json is machine-readable. Reading-extents.md records actual reads and limits. This is no acceptance/count decision or exhaustive novelty/formal certificate.

Obtain this review's MANIFEST.json SHA256 from the external final handoff. It is intentionally not self-anchored inside this package.

```bash
python3 -I -B verify.py --anchor EXTERNAL_REVIEW_MANIFEST_SHA256
python3 -I -B verify.py --anchor EXTERNAL_REVIEW_MANIFEST_SHA256 --repo /path/to/openai-proof-research
python3 -I -B verify_controls.py --anchor EXTERNAL_REVIEW_MANIFEST_SHA256
python3 -I -B check_revised_score.py
python3 -I -B check_pairing.py
```

Verify.py is read-only: exact safe membership, regular single-link files, lengths and SHA256; with --repo it also rechecks the bound input hashes and upstream pin. Only top-level tmp/ is excluded. Empty directories are not payloads. The verifier authenticates files, not mathematics or the truth of receipts. Controls create and mutate only temporary copies inside this review's tmp/, then delete those copies; every verifier invocation is checked for read-only behavior.

Checks contain active/input authentication, fresh build receipt/logs, byte-identical reproduction, original and new finite score diagnostics, copied author and own verifier controls, and per-page visual hashes/observations. The fresh PDF and all 18 PNGs are reproducible scratch. Their hashes are recorded, but the scratch is not sealed payload.

The build was replayed from the inspected author's build.py into tmp/build, using its fixed SOURCE_DATE_EPOCH and installed Tectonic. It reproduced the active sealed PDF without warnings. The original code and external TeX bundle are needed to replay that build. No author directory was used as an output destination.

Code attribution: check_pairing.py is an unchanged copy of manuscript-review-r3/check_pairing.py; audit_inputs.py adapts r3/audit_inputs.py to the active r2 object and all ten supplied anchors. Verify.py and verify_controls.py adapt the inspected author's r2 integrity verifier/controls (MIT, Myeongjin Kang; LICENSE-CODE.txt retained). Check_revised_score.py is newly written for this round. Reused diagnostics are explicitly reused evidence, not a claim of independent implementation. The new general polynomial proof, matrix normalization and analytic limit checks are documented independently in review.md.

No Lean build was rerun. Formal evidence is limited to the authenticated support package and independent formal review. The complete analytic theorem is not formalized; toolchain and pinned dependency oleans remain trusted. The broader literature screen remains incomplete. No third-party full paper is redistributed in this packet.
