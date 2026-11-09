# REPRODUCE — manuscript draft PDF (ordinary proof)

Lane: `crown-vnumber-manuscript-pi-r1`. Date: 2026-11-06 (UTC).

## Artifact

`output/pdf/paper.pdf` — 9 pages, A4. Research **draft**, ordinary (pen-and-paper)
proof only. Lean formalization: **PENDING** (no kernel-checked endpoint claimed).
Acceptance/credit: none claimed here; recorded campaign count 52/60, credit 0.

## Environment

- Python 3.12 + ReportLab 4.4.9 (cached runtime:
  `~/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3.12`)
- poppler-utils `pdfinfo` / `pdftoppm` (system)
- Fonts: Liberation Serif (regular/bold/italic/bolditalic), Symbola fallback for
  math glyphs; registered by absolute path in the generator.
- No network access needed.

## Build

```sh
./capped_run.sh build \
  ~/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3.12 \
  manuscript/generate_paper.py
# writes output/pdf/paper.pdf
```

`capped_run.sh` caps jobs at 2 CPUs (taskset), 120 s CPU / 140 s wall, 12 GiB
address space, 6 GiB RSS guard, `MALLOC_ARENA_MAX=2`, and logs each run to
`logs/jobs.jsonl`.

## Page render + inspection

```sh
./capped_run.sh render pdftoppm -png -r 100 output/pdf/paper.pdf qa/page
```
then inspect every `qa/page-N.png`. Record: `qa/INSPECTION.md`.

## Frozen-input verification (before and after)

```sh
python3 verify_frozen.py before   # -> evidence/frozen-before.json
# ... build ...
python3 verify_frozen.py after    # -> evidence/frozen-after.json
```
Both runs must report `all_ok: true` over all 129 files of `frozen-inputs.json`
(SHA-256). Last runs: before 2026-11-06 (129/129), after 2026-11-06 (129/129).

## Companion files

- `PROOF-COVERAGE.json` — obligation-by-section coverage map (23 obligations,
  11 mandatory-element checks).
- `artifact-hashes.json` — SHA-256 of the released artifacts.
- `logs/jobs.jsonl` — capped-run journal. `logs/marker-receipt.txt` — the single
  PDF-skill marker invocation (`mark_artifact_operation_started.mjs
  --operation-kind create --expected-output-count 1 --output-format pdf`, exit 0,
  run once immediately before the first PDF-authoring command).
- `manuscript/generate_paper.py` — the entire source of the PDF (single file).

## Source zip

`manuscript-source.zip` contains `manuscript/generate_paper.py`,
`PROOF-COVERAGE.json`, `REPRODUCE.md`, `qa/INSPECTION.md`, `verify_frozen.py`,
`capped_run.sh` — everything needed to regenerate and re-check the draft
(excluding the frozen evidence lanes, which are verified in place).
