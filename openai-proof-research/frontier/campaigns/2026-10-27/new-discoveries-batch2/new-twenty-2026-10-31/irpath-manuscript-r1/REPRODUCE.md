# Reproduction (DRAFT dossier, MathDB 350452)

Everything here uses standard-library Python 3. The only exceptions are Pillow, which `scripts/zoom.py` uses for one QA close-up, and poppler's `pdftoppm`, which is called as a child of the capped Python process to render pages. No network is used. No Lean, lake, leanchecker, SAT or ILP solver is run. No script from another lane is executed; discovery-lane scripts are kept only as `.txt` copies.

## How to run

Run from the dossier root, **one command per invocation, sequentially**, each wrapped as:

```
PYTHONDONTWRITEBYTECODE=1 bash -c 'ulimit -v 2000000; timeout 100 python3 -I SCRIPT ARGS'
```

`-I` ignores the `PYTHON*` environment variables, so every script also sets `sys.dont_write_bytecode = True`. The scripts import no local modules. Outputs are opened with mode `x`, so to rerun you must use a fresh directory or delete the old output first.

## 1. Frozen inputs

These steps run only inside the campaign tree, because they need the sibling input lanes.

1. `scripts/hashbind.py snapshot receipts/inputs-before.json`
2. `scripts/copy_inputs.py receipts/copy-receipt.json` copies 77 files byte for byte, including `lean/source.zip` and `mathdb-350452.jsonl`.
3. `scripts/hashbind.py snapshot receipts/inputs-after.json`
4. `scripts/hashbind.py compare receipts/inputs-before.json receipts/inputs-after.json receipts/inputs-compare.json`

## 2. Finite facts about G

`scripts/recompute.py outputs/graph-facts.json`

This step takes about 3 s and computes:
- the graph and its degrees;
- the automorphism group, over 9! permutations;
- the private neighbourhoods of all subsets, and the identity PN(v,D) = U(D−v) − U(D);
- the irredundant counts;
- the 36 pair sets U(P);
- the triple classes (a)/(b)/(c), which have 54/21/9 members;
- the 126 four-set witnesses (121 + 5);
- the 9 IR-sets, the 36 IR-set pairs and the 8 swaps;
- the K2 control.

## 3. Exhaustive search

Run these steps in order. Each finished in under 25 s.

```
scripts/search.py small outputs/search/small.json
scripts/search.py gen8 outputs/search/small.json 0 1044 outputs/search/gen8-0000-1044.json
scripts/search.py merge8 outputs/search/merge8.json outputs/search/small.json outputs/search/gen8-0000-1044.json
scripts/search.py ext9 outputs/search/merge8.json 0 2000 outputs/search/ext9-00000-02000.json
scripts/search.py ext9 outputs/search/merge8.json 2000 4500 outputs/search/ext9-02000-04500.json
scripts/search.py ext9 outputs/search/merge8.json 4500 7500 outputs/search/ext9-04500-07500.json
scripts/search.py ext9 outputs/search/merge8.json 7500 10500 outputs/search/ext9-07500-10500.json
scripts/search.py ext9 outputs/search/merge8.json 10500 12346 outputs/search/ext9-10500-12346.json
scripts/search.py agg outputs/search/agg9.json outputs/search/merge8.json outputs/search/ext9-*.json   (list the five files explicitly)
```

Expected results:
- Class counts are 1, 2, 4, 11, 34, 156, 1044 and 12346.
- No hits at orders 1–8.
- At order 9, 3,160,576 labelled graphs are evaluated, with 21 hits in 3 classes:
  - P7: 6 hits, 22 edges;
  - P8: 10 hits, 21 edges;
  - P9: 5 hits, 20 edges, the class of G.
- There are no cycles C_m with m ≥ 5.

## 4. Lean packet (no Lean run)

`scripts/safe_extract.py lean/source.zip lean/safe-extracted receipts/safe-extract-receipt.json`

This script:
- checks the SHA-256 `953331d0a5ed9984657fdfb8f35822e8383c19c7adf10a31c6390e0e961439ee`;
- checks member names, symlinks, duplicates, sizes and CRCs;
- extracts the regular files;
- checks that `module-order.txt` lists General, GData, Four, Three, Finite, Endpoint, Control and Audit;
- checks that each module equals the formal lane's `final-extraction` copy;
- scans for forbidden tokens (only the Audit module's own `extern`/`unsafe` strings occur);
- locates the endpoint declarations.

Compiling the packet is a separate, authorised Lean step. See `inputs/formal/REPRODUCE.md` and the root replay in `inputs/root/replay-result.json` (PASS, 8 modules built and leanchecked, axioms propext, Classical.choice and Quot.sound).

## 5. Paper

1. `scripts/build_pdf.py paper/manuscript.src outputs/graph-facts.json outputs/search paper` writes `paper/manuscript.pdf` and `paper/manuscript-resolved.txt`. Tables are generated from the outputs, not typed by hand. The fonts are Liberation Serif/Mono and Noto Sans Math from `/usr/share/fonts`, embedded whole.
2. `scripts/check_numbers.py paper/manuscript-resolved.txt receipts/numbers-receipt.json` checks 68 claims; all pass.
3. `scripts/render.py paper/manuscript.pdf qa 110` renders every page. Then inspect each `qa/page-N.png`; see `qa/visual-qa-receipt.json`.
4. `scripts/zoom.py paper/manuscript.pdf 5 300 0.1 0.7 0.9 0.8 qa/zoom/p5-lean-table.png` produces a glyph close-up.

The PDF has no timestamp and is deterministic given the same fonts.

## 6. Packaging

`scripts/package.py` writes the following:
- `MANIFEST.sha256`, covering every file except itself, the ZIPs, `archives.sha256` and `receipts/package-receipt.json`;
- `paper-source.zip`, containing the source, scripts, outputs and this guide;
- `full-dossier.zip`, containing every manifest file plus the manifest;
- `archives.sha256`;
- `receipts/package-receipt.json`.

It reopens both ZIPs and CRC-tests them.
