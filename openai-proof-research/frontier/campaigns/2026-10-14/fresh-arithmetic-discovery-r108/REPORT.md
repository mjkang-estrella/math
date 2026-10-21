# r108 outside-manifest artifact report

This report is outside MANIFEST.json and independently anchored. It is not an independent mathematical review. Mathematical disposition: PREFREEZE/no nominee, with the exact gap in FINAL.md and notes/visibility-feasibility.md.

## Observed controls before the final seal

- Complete pinned tree:13223 entries, truncated=false, expected SHA256.
-67 canonical pinned TeX/bibliography files matched tree sizes, Git blob identities and acquisition SHA256; four retained primary PDF/text pairs matched their acquisition receipts. This authenticates bytes; source truth and operative operations are stipulated, not audited.
-15 named current-original/control comparisons matched: three earlier-retained controls and12 late original snapshots. Six late-snapshot paths also had matching earlier search digests. Other originals have only late baselines. A wrong r19 path was recorded missing before the correct payload/checkpoint.md was separately captured. This does not certify first-read preservation or an entire parent tree.
-80 finite row-capacity cases matched exhaustive periodic gcd enumeration, with three explicit CRT witnesses also checked. These checks do not prove the working asymptotic question.
-Nine copied verifier controls behaved as expected: intact copy accepted; changed, extra hidden JSON, missing payload rejected; separate FINAL, REPORT and MANIFEST mutations rejected against supplied anchors; payload symlink rejected; restored copy accepted. The verifier did not change the copied payload. All mutations were inside scratch/copied-controls. Exact observations are in notes/copied-control-results.json.

No additional mathematical acceptance, contribution, correctness, formal or manuscript tests were conducted. The controls were proportionate artifact diagnostics, not self-gates.

## Exact inventory contract and replay

MANIFEST.json inventories every regular payload file under this root, including original notes/code and all private inputs/metadata. The only root file exclusions are MANIFEST.json, FINAL.md, REPORT.md, SHA256SUMS and detached-anchors.json. The only subtree omitted from inventory is scratch/copied-controls/, which contains disposable copies and control fixtures. Symlinks and unexpected payload files are rejected. The two convenience checksum files are untrusted copies of the detached anchors; verification never obtains its trust from them.

Run with the three full hashes supplied in the terminal handoff:

    python -B controls/verify.py --root . --manifest-sha MANIFEST_HASH --final-sha FINAL_HASH --report-sha REPORT_HASH

This performs only reads. The final invocation/result is provided in the tool handoff after the one-time seal; no sealed file is rewritten to incorporate that output.

Optional named-original/input replay, also read-only:

    python -B controls/authenticate_inputs.py --project /home/mj-kang/Documents/Dev/math/openai-proof-research

The latter compares only the named originals against recorded baselines. It does not search or enter other active roots. Earlier search controls and acquisition scripts are retained for provenance, not automatically rerun by verification. The copied-control runner intentionally refuses to overwrite an existing copy run.

All writes for this task, including downloads, extracts, the inspected render, captures and test copies, were confined to the exclusive r108 root. No git/staging/commit, nested agent, shared ledger edit, publication or browser UI action was used. Coarse search omissions, initial false admissions, truncations and prospective-only exclusions are disclosed in READING.md, not converted into an isolation certificate.
