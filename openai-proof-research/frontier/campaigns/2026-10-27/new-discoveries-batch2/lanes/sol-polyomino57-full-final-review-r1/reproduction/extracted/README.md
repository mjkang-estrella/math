# Reproducible final-review candidate

Credit 0. Counts unchanged: 5/30 additional, 35/60 total. Root acceptance and independent integrated final review remain pending. Refreshed source/prior review found no matching result but recommends substantive EXCLUDE; root explicitly retained eligibility for final review only. Author-code404 and fresh-history gaps remain. Do not infer acceptance from a build.

Read paper.pdf (seven pages), paper.txt (human proof and editable source), inherited/ADOPTION.json, and PROVENANCE.json. The candidate proves a(11) <= 57, refuting the full all-n formula of OEIS A395495. It makes no optimality, first failure, asymptotic or algorithm performance claim.

## Formal replay

With the exact Lean binary and eight package checkouts/build caches at the paths in pins.json:

```
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 replay.py /absolute/new/replay-directory
```

Use a new output directory. The driver creates a deterministic source archive, extracts it, and compiles 2022 mathematical modules plus FinalAudit from scratch, using only upstream pinned caches. No candidate prebuilt is packaged. The driver checks all eight revisions from metadata, binary SHA/version, manifest hashes, closed endpoint records, 5924 unique actual declaration records, actual origins/types/axioms/flags, logs and measured limits. The generated .olean files are outputs only. The Lean launcher is fixed at -j1, warningAsError=true, autoImplicit=false, CPU210, wall230, 2800MiB sampled group RSS at .045s. Helpers use AS512MiB; the launcher boundary removes that virtual-address constraint only for Lean, which has the group RSS policy. Never run this driver beneath an inherited hard 512MiB AS cap: it must be able to establish the distinct child policy. Python helper work is capped in the script itself. BLAS/OMP threads are one. No resource threshold is raised to accommodate a failing stage.

The receipt and exhaustive actual declaration inventory appear in the output directory only after complete success; logs and completed.txt remain on failure. Run time is substantial (the inherited worker replay took about 51 minutes); this is not a performance guarantee. This lane's complete fresh extracted replay passed; its evidence is in replay-evidence/. All5924 actual records match the frozen inventory, including types and origins. inherited/REPLAY-RECEIPT.json belongs to the original formal worker and is labeled accordingly.

## Deterministic PDF and ZIP

Use Python 3.14, ReportLab 5.1.0, and the included fonts. Install dependencies into an environment outside the packet, for example:

```
python3 -m venv /absolute/path/pdf-environment
/absolute/path/pdf-environment/bin/python -m pip install --no-cache-dir reportlab==5.1.0 pillow==13.0.0
/absolute/path/pdf-environment/bin/python build_pdf.py
python3 pack.py /absolute/path/polyomino57-final-review.zip
```

Authoring and packaging stages apply CPU210/AS512MiB/wall230 limits. The replay orchestration spans the serial stage sequence; each Lean stage has its own wall230 limit, rather than a 230-second limit on the whole multi-stage replay. The PDF includes a vector figure, also emitted as container.svg. A fixed ReportLab invariant timestamp makes the PDF byte-identical under the recorded runtime; this timestamp is a reproducibility setting, not a chronology claim. pack.py creates MANIFEST.json covering every other file with byte lengths and SHA-256, then emits sorted fixed-time/fixed-permission ZIP entries. zlib/runtime versions are recorded with the reproduction receipt; cross-version compressed-byte identity is not promised.

To reproduce from extraction, unzip the packet into a new directory, run build_pdf.py there, check the PDF hash against the delivered manifest, and run pack.py to an output ZIP outside that directory. Compare its SHA-256 with the delivered archive. The combined offline check is `/absolute/path/pdf-environment/bin/python verify_packet.py /absolute/packet.zip /absolute/new/reproduction-directory`, using the Python environment with ReportLab. It validates every manifest entry, formal closure, replay receipt and all actual declaration records, then rebuilds PDF and ZIP from extraction. It does not substitute for a new Lean replay. Do not copy generated replay outputs or __pycache__ directories into the packet. pack.py rejects prebuilt Lean and development/cache artifacts.

## Trust and audit

Read formal/FinalAudit.lean and the actual audit log, not merely its printed total. All 5924 actual-origin declarations must be unique and axiom-closed over propext, Classical.choice and Quot.sound. The lone inherited exception is Polyomino57.attachCheck._unsafe_rec, with actual unsafe=false, partial=true, axiom=false. Every other declaration must have all those flags false. The audit module is an observation tool, outside the mathematical origin list; its full source is included. No new axiom, sorry, admit, native_decide or unsafe declaration is permitted.

Formal sources and FinalAudit are byte-identical to the root-frozen 2023-entry source manifest. Packaging scripts were replaced rather than running development generators. No development artifacts, original enumeration payload, nested development archives or candidate prebuilt modules are needed or shipped. Inherited provenance/reviews/failure descriptions are documentary evidence, not imports or new clearance. The earlier mathematical reviewer PASS did not review this integrated formal packet. Full final independent review and root acceptance replay are outstanding.

## Visual QA reproduction

The delivered QA.json hashes the final PDF and seven rendered page PNGs, all visually read. To regenerate renders with Poppler, create a new QA directory and run `timeout 230 pdftoppm -scale-to 1150 -png paper.pdf /absolute/new/qa/page` under shell CPU210/AS512MiB limits. Font coverage was also checked programmatically. The reproducibility check compares PDF bytes; it does not replace visual reading. CASE-MAP.json links all70 canonical triples to their actual frozen theorem and source hash.
