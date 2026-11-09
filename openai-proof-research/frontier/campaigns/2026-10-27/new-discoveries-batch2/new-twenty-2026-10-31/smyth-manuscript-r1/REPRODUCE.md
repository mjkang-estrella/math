# Reproduction without Lean in this lane

All commands below are run from this dossier directory. Python uses only its standard library, in isolated mode. Required system tools for PDF: groff with eqn/tbl and PostScript device/fonts, Ghostscript, and Poppler. A local macros.tmac avoids a dependency on groff's optional ms package. The editable manuscript source is paper.ms; scripts/paper.py is the generating source. Do not run the historical patch/polish scripts on the final generator.

For each command use `MALLOC_ARENA_MAX=2 python3 -I scripts/capped.py LABEL COMMAND...`. The wrapper limits affinity to two available CPUs, CPU to 120 seconds and address space to 6 GiB, samples process-group RSS, enforces wall time below 140 seconds and reaps the process. Run commands serially. TMPDIR is dossier-local.

1. `python3 -I scripts/audit.py certificate` recomputes compositions, generators, lists, row counts, type and reversed flows.
2. `python3 -I scripts/hk.py` recomputes element-level matching.
3. For each A from 3 to 10, separately run `python3 -I scripts/batch.py sweep A`.
4. For each b from 19 through 43, separately run `python3 -I scripts/audit.py family b`. Do not put the entire family into one capped process: a development batch reached its CPU cap after b=42. b=43 subsequently completed in its own capped process.
5. `python3 -I scripts/metadata.py` verifies seven definitions, module count and every Lean row numeral by reading text only.
6. `python3 -I scripts/paper.py` regenerates paper.ms, paper.ps and paper.pdf. To edit manuscript text, edit the generator or edit paper.ms directly and run groff -e -t -Tps macros.tmac paper.ms, then Ghostscript pdfwrite, saving both outputs only inside this directory.
7. `pdftoppm -r 110 -png paper.pdf qa/page` renders all pages. Inspect each page again after any edit. The supplied final render was visually reviewed page by page.

The packet safe-extraction receipt and stage.py document traversal, symlink, duplicate-name, size, content and required SHA-256 checks. Source ZIP is never regenerated. No Lean execution is part of this manuscript workflow. The upstream packet REPRODUCE.md records Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; running its replay belongs to root. Supplied formal and root reports are evidence, not worker replays.

Evidence copies retain source-relative paths and receipts. Exact MathDB line is evidence/expanded-corpus-r151/raw/332037.jsonl. Its SHA-256 is recorded in audit-correspondence.json. Before/after manifests hash all selected frozen inputs, and a separate pair binds the final root receipts when they appeared.

Dossier packaging is performed by scripts/package.py after QA and all receipts settle. MANIFEST.sha256 excludes itself and the outer ZIP/ZIP hash receipt to avoid self-reference. full-dossier.zip includes the manifest; full-dossier.zip.sha256 binds the outer ZIP. Hash identity checks also ensure the copied sources match their originals.
