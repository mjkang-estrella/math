# Reproduction — lane common-basis-manuscript-pi-r2 (DRAFT)

All Python below uses `python3 -I -B` with actual paths, run from this lane directory.
No dependency was installed or repaired; the reportlab import reuses the already-present
venv site-packages from latin-manuscript-r1 via an explicit sys.path entry, and fonts come
from the system liberation-serif package plus the r1-lane Symbola copy (hashes recorded).

## What was run here (logs in logs/, receipts in receipts/)

1. Frozen-input verification, BEFORE (998/998 OK): inline sha256 check -> receipts/frozen-before.json
2. Ordinary recheck of every mathematical number, from the frozen certificate:
       python3 -I -B archive-staging/source-only/ordinary_check.py > logs/author-ordinary-check.log
   (exit 0; also shipped inside both archives)
3. Paper build:
       python3 -I -B paper-src/build_paper.py     # writes paper.pdf
4. PDF QA: `pdftoppm -png -r 100 paper.pdf qa/pg` and page-by-page visual inspection
   (glyphs, tables, margins); zoomed crops for the title diacritics and math symbols.
   pdfinfo: 6 pages, 612x792pt.
5. Zip construction and integrity (`python3 -I -B`, zipfile testzip) and per-file SHA-256
   manifest -> archive-manifests.json, MANIFEST.sha256.json, hashes.txt
6. Frozen-input verification, AFTER (998/998 OK): receipts/frozen-after.json

## What was NOT run here

- The 12-module Lean strict replay. The independent strict Lean-fidelity audit was running in
  common-basis-fidelity-pi-r2; polling or duplicating it was out of scope, and the frozen lane's
  author-side replay-record (expanded-corpus-r250/replay-result.json, 24 stages) is quoted in the
  paper as author-supplied evidence only. `source-only-proof.zip` ships `replay.sh`, verified for
  syntax (`sh -n`) and portability (env LEAN_BIN / LEAN_PACKAGES, fresh LEAN_PATH, sanitized
  PATH, MALLOC_ARENA_MAX=2), but its full execution is left to the audit, the root final replay,
  or the reader. Any replay performed from it is a new replay, not the independent audit.

## Resource discipline

Only light processes ran here (python, pdftoppm, zip); no heavy Lean compilation. The caps
(2 CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB, AS 12/64 GiB guard, MALLOC_ARENA_MAX=2)
are documented in the paper and bind any future replay via replay.sh's environment settings.

PDF skill operation marker

The skill's `mark_artifact_operation_started.mjs --operation-kind create` marker was run once before the first authoring
command (exit 0; it is silent by design). See receipts/artifact-operation-marker.txt.

## Integrity rules honored

- The 12 Lean modules are byte-identical to expanded-corpus-r250/lean-source-manifest.json
  (verified before packaging; see logs/lean-identity-check.txt).
- No source file was modified to make anything pass; issues would be reported to root.
- No git, no uploads, no browser tabs, no external contacts, no shared-ledger writes.
- No prebuilt oleans or large caches in either archive; archives contain no symlinks.
