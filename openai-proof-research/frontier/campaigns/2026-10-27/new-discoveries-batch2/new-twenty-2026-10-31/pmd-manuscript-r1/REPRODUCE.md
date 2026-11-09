# Offline reproduction (no Lean execution in this preparation)

Run from this dossier directory. Python 3 standard library suffices for arithmetic and archive inspection. No solver, network, account or browser is needed. All writes must remain here.

```
python3 -B cap.py arithmetic-reproduce python3 -B verify.py
```

This reconstructs Cartesian adjacency and checks all four certificates, including complete partitions, nonempty disjoint matchings, selected sums exactly 1, and strict negativity on every other residual edge. Output: receipts/arithmetic.json. The cap receipt uses a different name so it cannot overwrite the arithmetic data.

The exact raw line is raw/366974.jsonl; raw/366974.sha256 binds every byte, including its newline. Original discovery results are excerpted under evidence/discovery/results-366974.json; their old unread-thesis gap is superseded by evidence/review/REVIEW.md and evidence/root/ruling.json. No historical receipt has been rewritten to appear current.

The original lean-packet.tar.gz is reused byte-identically. receipts/safe-extraction.json records actual extraction into safe-extracted/: all member names were checked for absolute paths and parent traversal; only regular files/directories were accepted, with every link/device rejected. Python tarfile.extractall(filter='data') was used. The extracted TorusPMD.lean equals the frozen source byte for byte. verify.py repeats the packet hash and member-policy checks without executing any archive content. prepare.py records how source copies and the extraction were made; it is a one-time preparation script and expects the original sibling lanes and a fresh extraction directory.

For PDF generation use Python with ReportLab and DejaVu fonts:

```
python3 -B cap.py pdf-reproduce /home/mj-kang/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3 -B build_pdf.py
python3 -B cap.py render-reproduce pdftoppm -scale-to 1250 -png paper.pdf qa/page
```

build_pdf.py uses paper.md as its narrative template and frozen JSON certificate data for tables; paper-source.md is the fully expanded readable source. PROOF.md includes the same complete proof. The font directory is set in build_pdf.py to the available local runtime; adjust that path on another host. PDF creation metadata may change, so a regenerated PDF need not have identical bytes. Check the final page count (6) and visually inspect every regenerated page. No package installation or downloads occurred in this preparation. The default Python lacked ReportLab; an existing local runtime supplied it.

The cap wrapper sets at most two CPUs, MALLOC_ARENA_MAX=2, CPU 120 seconds, wall 140 seconds, address-space 6 GiB and sampled aggregate process-group RSS 6 GiB. One heavy process ran at a time. Small read-only inventory and file-authoring commands were lightweight and completed synchronously. Resource receipts include commands, affinity, sampled peak RSS and exit status.

No Lean, lake or leanchecker was run. For the previously completed Lean checks, consult evidence/root/replay-result.json and the original logs; they report Lean 4.34.1 and mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. Imported packages were not rebuilt here. The endpoint is TorusPMD.refutes_conjecture_4_7. The exact-value lower bound remains a prose theorem, and extra certificates have no additional formal endpoint.

inputs-before.json and inputs-after.json bind all 314 frozen input files, with equality recorded in receipts/input-integrity.json. They are relative to the original parent campaign directory; only selected source copies are included in this dossier. SHA256SUMS binds the deliverable payload. Verify it with `sha256sum -c SHA256SUMS`. Full-dossier ZIP member paths are relative and its decompressed contents are checked byte-for-byte against the payload. ARCHIVES.sha256 binds both ZIPs and the original tar.gz externally. Archive creation and its resource receipt are excluded from the embedded self-manifest as explained in receipts/package-check.json.

This is a draft with modest significance and bounded prior-art review, not a priority certificate. Accepted credit is zero. Root reads the manuscript and decides.
