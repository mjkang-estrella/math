# Reproduce the arithmetic, graph verification and manuscript

All commands run in this directory, in the foreground. Do not execute any script inside the reused Lean packet for this task. No network, solver, Lean, lake, leanchecker, git, browser or child agent is needed or authorized here.

1. Verify `manifest.sha256` using `sha256sum -c manifest.sha256`. The manifest intentionally excludes itself, manifest.json, the full dossier ZIP and its external receipt to avoid circular hashes. The external archive receipt binds the ZIP; the ZIP includes the internal manifest.
2. Run the exact fresh checker under isolation and caps (replace the absolute path below only if the dossier is relocated):

   `python3 -I cap.py python3 -I /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/nanostar-manuscript-r1/recompute.py`

   This standard-library checker imports no discovery code. It recomputes every table factorization and totient, the complete orbits and exact graph isomorphism, the layer profiles, and the D_2 and D_3 controls. It checks all ordered label pairs in the formal certificate. `recomputation.json` holds the exact results, all control rows, canonical strings and explicit isomorphisms.
3. `build_paper.py` is the complete executable PDF source; `paper.md` is a human-readable companion source. Use Python 3.12 with ReportLab installed. The local bundled interpreter used here is:

   `python3 -I cap.py /home/mj-kang/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3 -I /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/nanostar-manuscript-r1/build_paper.py`

   ReportLab was already present locally; nothing was installed or fetched. PDF timestamps may vary across reruns; mathematical content and the output table are deterministic.
4. Render with `python3 -I cap.py pdftoppm -scale-to 1200 -png paper.pdf qa/page`. Inspect every page, as recorded in receipts/page-qa.json. `pdftotext -layout paper.pdf qa/paper-text.txt` supplies searchable layout text. Re-rendering changes the artifact receipt hashes; regenerate manifests after intentional rebuilding.
5. `prepare.py` documents original input selection, hash freezing, copying and the safe extraction algorithm. It needs the original read-only sibling lanes, so it is a provenance reconstruction step rather than a standalone dossier dependency. `receipts/safe-extraction.json` records preflight validation of all entry paths, types, sizes, duplicate names and CRC reads before extraction. The extracted files in packet-extracted are evidence only; none was executed. The archive SHA-256 must be 5aa1150cb685221b2f9dbfbab4cd9eff9f503d917add10b62a491a1e19d81fac.

`cap.py` serializes heavy subprocesses with a lane-local lock, uses at most two affinity CPUs, sets MALLOC_ARENA_MAX=2, CPU rlimit 120 seconds, wall timeout 140 seconds and address-space ceiling 6 GiB. It additionally samples process-group RSS every 0.05 seconds and kills above 6 GiB. It waits for its foreground subprocess and writes a resource receipt. TMPDIR, TMP, TEMP and cache all point inside this lane. RSS sampling is not a guarantee against undetected transient peaks. All script paths are real filesystem paths; no script derives paths from stdin.

## Reading the evidence

- `frozen/expanded-corpus-r162/sources/` includes the preprint, publisher and accessible chemistry PDFs and text, with their original retrieval receipts. This dossier made no new retrieval.
- `frozen/expanded-corpus-r162/raw/349177.jsonl` is the exact MathDB raw line. `receipts/raw-record.json` binds its byte hash, including the line ending; the provenance entry is in mathdb-entry.json.
- `frozen/nanostar-review-r1/` retains the original review, numerical witness and audit logs, and the two source page renderings. The review's HOLD and the later root ruling are distinct records.
- `receipts/parent-final-status.json` records whether root replay-result.json and registry-refresh.json existed at final packaging; missing receipts mean pending, not passed.
- `inputs-before.json` and `inputs-after.json` bind the same frozen original input set. `receipts/input-integrity.json` checks both the original paths and dossier copies. Ongoing parent work is not treated as an immutable directory; only final named receipts, if present, are frozen separately.
- The original packet BUILD.md explains its environment-specific Lean replay procedure. It is retained for future authorized reviewers, not executed here. It trusts prebuilt dependencies at original absolute paths, so it is not a fully vendored toolchain.

The source registry/prior-art review is bounded, cached evidence. No new literature clearance or root acceptance is implied. Campaign credit remains zero for this lane.
