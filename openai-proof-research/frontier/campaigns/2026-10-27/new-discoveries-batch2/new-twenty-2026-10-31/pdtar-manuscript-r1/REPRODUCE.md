# Reproduce the draft and inspect the proof packet

No Lean, lake or leanchecker was run in this lane. Root’s completed fresh replay is copied verbatim in evidence/replay-result.json (76/76 PASS). Acceptance remains root’s decision.

## Check the delivered bytes

Use inputs-before.json and inputs-after.json to compare frozen upstream files, and frozen-integrity.json for the equality result. The raw MathDB line is mathdb-353203.raw.jsonl, including its newline, SHA256 fb3b4a73e92d8196e75e36cb9ee60ad6ad119a70c59be6cb44744734c24f3935. The chunk path and one-based line 2515 are recorded in evidence/r119-353203.json.

pdtar-source.zip must have SHA256 3a599c52f33e8fcbed9294de07b9b6a549606b7d6bd693fdfd834304a67173b4. It is byte-identical to formal-r4. safe-extraction.json records safe paths, no links or build objects, and every extracted member hash. proof-packet-safe/ is a source-only extraction; no proof script has been executed from it.

## Future authorized formal replay

These commands are documentation only. Run them in a new directory INSIDE this lane, with the pinned read-only toolchain/cache available at the absolute paths in proof-packet-safe/manifest.json. Never reuse completed replay state or run replay processes concurrently.

```bash
mkdir -p reproduction/scripts
cp pdtar-source.zip reproduction/pdtar-source.zip
cp proof-packet-safe/scripts/replay.py reproduction/scripts/replay.py
cd reproduction
python3 -I scripts/replay.py --init
python3 -I scripts/replay.py --resume --steps 10
```

Repeat the last invocation until REPLAY COMPLETE. The driver verifies source and toolchain hashes, log hashes and build-object inventory at each resume. It runs 34 strict serial builds, 34 leanchecker checks, one complete declaration audit, and seven expected-failure controls. The extracted limited.py sets two-CPU affinity, CPU 120 s, wall 140 s, sampled process RSS 6 GiB, AS 16 GiB for mappings, MALLOC_ARENA_MAX=2 and local temporary/cache paths. Only one heavy process runs at a time. Lean elaboration uses -j1 -M3500, warnings as errors and asynchronous elaboration disabled. Sampling cannot rule out transient unsampled RSS peaks.

## Render the manuscript

paper.md is the editable manuscript source; scripts/render.py is its renderer. ReportLab and Pillow are required. This lane reused existing local PDF dependencies by copying them to tmp/pdf-deps; that cache is omitted from the delivery ZIP. Standard installed ReportLab also works, since the optional cache path is inserted before normal package search. No installation or network request was made. The four font files and their hashes are included in fonts/.

From this lane, with ReportLab available, use the following sequentially (fresh log tags):

```bash
MALLOC_ARENA_MAX=2 taskset -c 0,1 timeout 140s python3 -I scripts/limited.py new-render /usr/bin/python3 -I scripts/render.py
MALLOC_ARENA_MAX=2 taskset -c 0,1 timeout 140s python3 -I scripts/limited.py new-raster /usr/bin/pdftoppm -r 110 -png paper.pdf qa/page
```

The runner itself caps its heavy child. If invoking it beneath an outer AS limit, allow 16 GiB of address space: RSS is separately sampled and limited to 6 GiB. Inspect every PNG anew after edits; the current inspection receipt is qa/receipt.json. The initial renderer launch failed in preexec because an outer AS limit was lower than the child’s requested limit. Subsequent launches exposed a missing ReportLab package and absent default font path; retained logs document both. Copying local dependencies and supplied font files resolved those environment issues. No mathematical code changed.

DOSSIER-MANIFEST.json inventories included files except itself. DELIVERY-SHA256.json, outside the ZIP, hashes both ZIPs, the PDF, and the manifest to avoid circular self-hashing. The package process tests every ZIP member against the manifest. No job remains running at handback.
