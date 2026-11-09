# Validation, reproducibility and limits (expanded-corpus-r96)

## Provenance

- `bootstrap.py` (copied from r95) extracts the 20 exact raw corpus lines from `lanes/pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-*.jsonl` into `raw/<id>.jsonl`. Each line keeps its newline, and `extracted.json` records its chunk path, one-based line number, chunk sha256 and raw sha256.
- `results.json` adds the statement sha256 and re-verifies every raw hash.
- Prior-campaign search: a ripgrep over `frontier/campaigns` for ID-shaped references (`mathdb_id: ID`, `/p/ID`, `"id": ID`, `MathDB ID`) found only the r301 inventory tag shards and the r309 coverage queue, where all 20 IDs are listed as `statement_screen` / `not_reconciled`. An earlier plain-numeric grep returned only false positives (numbers inside unrelated computations) and was stopped. These checks show that no lane notes exist for these IDs; they do not show that the IDs have never been reviewed.

## Sources and registries (2026-11-02 UTC)

- **arXiv HTML** came from `scripts/fetch.py`, with receipts in `sources/*-receipt.json`. Pages that returned 404 (341896, 363770, 368807) were replaced by PDF or abstract pages (`scripts/additional_sources.py`). Prior-art documents are in `sources/prior/` (`scripts/prior_sources.py`), each with a receipt. No denied route was retried, and none was hit apart from those 404s.
- **Registries** were queried through `/commits/HEAD` only.
  - OpenAI/math `4eaee87548250b2682affda7d05d947c05554bae` (unchanged), screened with the cached preprint listing `fresh-corpus-r10/sources/registry-preprints.json` (sha256 `6ac178a0…`).
  - Omega `9e88f6fbe4681a1f5617c2673e72e9d814178a53` (committed 2026-11-02T02:32Z). This is newer than root's `0ef26ad5…`. Its complete, untruncated D5 and Problems trees were fetched (`outputs/registry-screen.json`, `sources/omega-*.json`).
  - Result: no reserved-ID paths. The keyword screens (ASEP, subtour, TSP, rowmotion, nut, resurgence, chordal) found nothing related.
  - These are path and keyword screens only; no proof bodies were read from the registries.

## Resource discipline

- Python jobs set `RLIMIT_CPU` to 118–120 s and run under `timeout 135–140`. Node jobs use `ulimit -t 120`.
- Lean jobs use `scripts/rsscap.py`. It runs each process in its own session with a 64 GiB address-space limit and polls the RSS of the whole process tree every 0.2 s, killing it above 6144 MB. It also enforces CPU 120 s and wall 140 s, and Lean runs with `-j2`.
- At most two compute processes ran concurrently, except for the incident below.
- Incidents (`logs/resource-incident-ghv.txt`):
  1. A GHV batch was launched as four concurrent single-threaded processes, each capped at 118 s CPU, for about 2 minutes. Its wait loop matched itself and was stopped.
  2. An early Lean compile ran with no memory cap. It used a single kernel `decide` over all 5040 certificates plus the coverage equality, reached 26.4 GB RSS, and was killed at 131 s. After that, all checks were split into 105-certificate theorems (≤ 2.8 GB each; the coverage module peaks at 4.9 GB).
- Lean RSS is dominated by the mmapped mathlib oleans, about 1.5–2.2 GB for the targeted imports. A full `import Mathlib` test reached 7.0 GB and was then avoided.
- `gcc` is absent, so `scripts/linreal.c` was never compiled (`logs/linreal-c-not-compiled.txt`). The executed implementation is `scripts/linreal.js`.
- Python scripts that need numpy, scipy or sympy (user site-packages) were run without `-I`. They read only files generated in this lane, never downloaded data. Scripts that parse downloaded HTML (`texts.py`, `html2txt.py`, `fetch.py`, `prior_sources.py`) were run with `-I`.

## Reproduction commands (from the lane directory)

- 368807:
  - Sampling and walks: `python3 scripts/asep.py n samples seed [int]` and `python3 scripts/asep_walk.py n steps seed [maxzeros]`.
  - Exact checks: `python3 scripts/asep_exact_all.py 8 outputs/asep/candidate/n8-den4.json lo hi` and `node scripts/asep_independent.js 8 outputs/asep/candidate/n8-den4.json`.
  - Certificates: `python3 scripts/asep_cert.py`, then `python3 scripts/asep_lean_data.py` (regenerates `lean/ASEPData.lean`, re-checking every certificate) and `python3 scripts/asep_lean_vertex.py` (regenerates `lean/ASEPVertex.lean`).
  - Lean replay: `python3 scripts/asep_replay.py NEWDIR`.
- 368627: `python3 scripts/designs.py t1,t2,... p`.
- 382492: `python3 scripts/rowdiv.py k nmax`.
- 341896: `node scripts/rowmotion.js {example|gr|grdao|quad|quaddual} …` and `scripts/rowmotion_batch.sh`.
- 368042: `python3 -I scripts/chordal_gen.py 9`, then `python3 scripts/sqfree_reg.py 9 32003 1 lo:hi`. The slices for n = 9 are merged into `outputs/chordal/reg-n9-p32003.json`.
- 366914: `node scripts/linreal.js sweep ymin ymax B cap`, plus the `rand` and `one` modes.
- 376197: `python3 scripts/ghv.py {uniform|random q kmax nmax trials seed}`.

## Numerical-versus-exact status

- **368807:** the vertex and non-adjacency claims are exact. They are checked by integer-rank Python, by independent BigInt JavaScript and by the Lean kernel. The LP sampling and walks (floating point) were used only to find candidates.
- **368627, 382492, 366914, 368042, 341896:** exact integer or rational arithmetic, except that ranks for 368042 are taken mod 32003. These results are finite checks, not proofs.
- **376197:** floating-point HiGHS LPs; this is a diagnostic screen only.
- **368627 design sweep, capped groups:** runs that hit the CPU cap left empty JSON files, with their timing in `outputs/designs/*.time`. The capped groups are Z_169, Z_2×Z_64, Z_4×Z_32, Z_2^5×Z_4, Z_3^3×Z_9, Z_243 and Z_5×Z_25. Completed runs: every non-elementary abelian p-group of order at most 81, plus Z_121, Z_125, Z_128 and Z_8×Z_16.

## Not claimed

- No acceptance or novelty clearance.
- No full mathlib rebuild. `leanchecker` was run without `--fresh`.
- No exhaustive search at n = 7 for 368807.
- No proof of any parked conjecture.
