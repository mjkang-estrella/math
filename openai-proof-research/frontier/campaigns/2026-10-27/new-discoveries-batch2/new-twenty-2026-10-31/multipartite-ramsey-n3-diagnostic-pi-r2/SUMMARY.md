# SUMMARY — multipartite-ramsey-n3-diagnostic-pi-r2 (MathDB 359209, n=3 s=4 only)

UTC: 2026-11-05T22:08Z window. Pi GLM-5.3-Flash high, bounded planning diagnostic. Credit: 0. No Lean, no formalization, no n=5, no novelty/significance clearance.

## What was done

1. **Pre-flight**: `scripts/dpll.py` sha256 `5d91d053…10841d6` matches ROOT-FIXES patched hash; `ast.parse` OK; cwd verified. All **399/399** `frozen-inputs.json` entries (protected inputs + r1 partial artifacts incl. full r1 tree) byte-verified before the run → `frozen-before.json`. r1 directory bytes preserved untouched.
2. **Single bounded execution** of the existing `scripts/dpll.py` (no rewrite): `taskset -c 0,1`, `MALLOC_ARENA_MAX=2`, `ulimit -v` 12 GiB AS, external wall cap 140 s with process-group kill, script-internal 110 s deadline. Full receipt in `logs/` (launch-receipt, stdout, stderr, sampled RSS).
   - Result: **SAT**, 2535 nodes, wall 1.529 s, CPU 1.537 s, peak RSS 12.5 MiB, exit 0. Far under every cap; one run only; no budget resets, no loops.
3. **Independent verification** (`scripts/verify_model.py` → `verification.json`), trusting no counts:
   - Fresh CNF parse: 48 vars, 2400 clauses; the 48-bit witness satisfies **all 2400** clauses.
   - Edge numbering **regenerated in lex order** (complete tripartite host, parts of 4); matches `mapping.json` entry-for-entry.
   - **All 66 vertex pairs**: common neighbors outside both endpoint parts (8 for same-part pairs, 4 for cross-part pairs); both-red ≤ 2 **and** both-blue ≤ 2 for every pair ⇒ no monochromatic K_{2,3} in either 2-side/3-side orientation. Max both-red = 2, max both-blue = 2. **CHECKER PASS.**

## Status (exactly what this is and is not)

- This is an **uncredited m3 ≥ 5 feasibility witness (lower-bound planning input) only**.
- It is **not** a conjecture solution, not a proof of any endpoint, and no UNSAT certificate exists (the script implements no proof logging; `UNVERIFIED_UNSAT` path unused since SAT was found on the first run).
- Source review (2019 body / 2025 thesis), prior, and significance gates **HOLD, stay open**. No n=5 work started.

## Deliverables (all real files, hashes in `hash-manifest.json`)

- `results.json` — ID-keyed (mathdb_id 359209) run + verification summary
- `solver-result.json` — actual solver output (48-bit witness, SAT, internal receipt metrics)
- `verification.json` — independent checker: bits, all 66 pair counts, PASS flags
- `scripts/dpll.py` (unedited, root-patched), `scripts/verify_model.py`, `scripts/run_once.sh`
- `logs/launch-receipt.txt`, `logs/solver-stdout.txt`, `logs/solver-stderr.txt`, `logs/rss-samples.tsv`
- `frozen-before.json` / `frozen-after.json` (399/399 verified before and after; r1 preserved)
- `hash-manifest.json` — sha256 over all deliverables

## Process hygiene

Runner + solver exited normally (exit 0); group-kill path never triggered (wall 2.0 s ≪ 140 s); no stray `dpll.py` processes remain. No network, no installs, no dependency/cache repair, no git, no shared edits, no credit counted.
