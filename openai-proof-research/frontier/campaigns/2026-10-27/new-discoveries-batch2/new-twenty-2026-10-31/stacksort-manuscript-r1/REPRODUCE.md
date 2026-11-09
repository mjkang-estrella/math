# REPRODUCE: MathDB 345545 manuscript dossier

This is a DRAFT dossier with zero accepted credit; the root decides. Run all commands from this lane directory. This lane ran no Lean, lake, leanchecker or solver. Every process below was run through `scripts/cap.py`, which gives two-CPU affinity, RLIMIT_CPU 120 s, a 140 s wall limit, MALLOC_ARENA_MAX=2, a sampled process-tree RSS kill at 1.5 GiB and a lane-local TMPDIR. Commands were run one at a time. Receipts are in `logs/<label>.cap.json`.

## 1. Lean packet (source only)

`lean/stacksort-source6.zip` is a byte-identical copy of `../stacksort-formal-r6/stacksort-source6.zip`, with SHA-256 9b734e2fe521651fd33bbf92bdf05f1b542a6aeb82f90d2cd1e13399d6cf5c2f (`lean/ZIP-RECORD.json`). It contains 92 Lean modules and 8 scripts, and the endpoints are in `src/StackSortFinal6.lean`, namespace `StackSort.Round6`.

The safe-extraction test does not run Lean:

    rm -rf safe-extraction safe-extraction-report.json
    python3 -I scripts/cap.py safe-extract -- python3 -I scripts/safe_extract.py lean/stacksort-source6.zip safe-extraction ../stacksort-formal-r6/results.json safe-extraction-report.json

To replay the build itself, Lean 4.34.1 with the pinned Mathlib packages is needed. Follow `evidence/formal-r6/REPRODUCE.md` (round-6 driver `scripts/replay6.sh` inside the archive), which uses `scripts/run.sh` with the same caps and `lean -j1 -M3500 -DwarningAsError=true`. The decisive fresh replay is the root's job, in lane stacksort-parent-final-r1.

## 2. Mathematical diagnostics (not proof)

    python3 -I scripts/cap.py check-math-N82 -- python3 -I scripts/check_math.py data/stack_pairs_P_1_82.json safe-extraction/src/StackSortCertificate.lean safe-extraction/src/StackSortControls.lean evidence/math-check.json 82
    python3 -I scripts/cap.py gen-tables -- python3 -I scripts/gen_tables.py data/stack_pairs_P_1_82.json paper-src

The first command takes about 90 s and peaks at about 31 MB RSS. It brute-forces P_1..P_8, checks T1–T4 on all tuple pairs with M ≤ 6, recomputes P_1..P_82 by the top-max recursion, and checks the root-split and doubling inequalities, the G_130 = `lower130` linkage, the certificate and controls, the seed-depth thresholds (13 → 910, 14 → 446, 16 → 230, 20 → 130) and the exact a = 82 bound. That bound is 1.8046832…: it is above 1.80468 but NOT above 1.8047. `data/stack_pairs_P_1_82.json` is a byte-identical copy of `../expanded-corpus-r133/outputs/stack_pairs_P_1_82.json`. (The original run read that path directly; both have SHA-256 recorded in `SOURCE-COPIES.json`.)

## 3. Paper

    python3 -I scripts/cap.py render -- python3 -I scripts/render.py
    python3 -I scripts/cap.py rasterize -- pdftoppm -r 110 -png paper.pdf qa/page

`scripts/render.py` expands `paper-src/paper.src.md` (tables from `paper-src/table-*.md`, status sentences from `paper-src/status.json`) into `paper.md` and renders `paper.pdf`. It uses the lane-local reportlab copy under `tmp/pdf-deps/` and the fonts in `fonts/`. The reportlab copy is a byte-identical copy of `../chanlevine-manuscript-r1/tmp/pdf-deps/`, hash-bound in `hashes/renderer-inputs.sha256`; it is not included in the full ZIP. The fonts are Liberation Serif and Mono, plus Symbola for missing math glyphs. Every page image in `qa/` was visually inspected; see `qa/receipt.json`.

## 4. Packaging

    python3 -I scripts/cap.py package -- python3 -I scripts/package.py

This writes `SOURCE-COPIES.json`, `DOSSIER-MANIFEST.json` and `stacksort-full-dossier.zip`. Receipts that would hash themselves (`DELIVERY.json`, the packager's own cap receipt and the after-hash files) are written after the ZIP and are listed in `DELIVERY.json`.
