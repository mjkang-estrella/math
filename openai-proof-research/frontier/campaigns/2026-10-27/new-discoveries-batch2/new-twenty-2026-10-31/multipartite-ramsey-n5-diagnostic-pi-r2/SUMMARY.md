# multipartite-ramsey-n5-diagnostic-pi-r2 — SUMMARY

**MathDB 359209 planning diagnostic (bounded, zero credit). Executed once, 2026-11-05, Pi GLM5.3Flash lane r2.**

## What ran

1. **Frozen verification (before)**: `scripts/verify_frozen.py` — 418/418 entries OK (`frozen-before.json`, `logs/frozen-before.txt`). Patched `scripts/search.py` sha256 `f6894588cd58602e5c0e495793790b3372fbea96c98db91ff0a71fc7168728f0` confirmed (matches ROOT-FIXES.json); AST-parses.
2. **Capped selftest**: `./run_selftest.sh` — `{"incremental_mismatches": 0, same_part_pairs 50, cross_part_pairs 250, eligible_counts_ok true}`, mask-vs-bits assertion (`colors_to_masks(bits) == (rnb2,bnb2)`) and static-count assert passed; exit 0 (`logs/selftest.txt`).
3. **The ONE full search**: `./run_search.sh` → `python3 scripts/search.py --seed 20261105 --cpu-budget 112 --wall-deadline 128`. Guards: affinity `taskset -c 0,1`, hard CPU 120 s (`ulimit -t`), wall 140 s process-group kill, AS 12 GiB (`ulimit -v`), sampled RSS 6 GiB guard, `MALLOC_ARENA_MAX=2`. **Exit 0.** Neither guard tripped; the run ended on its internal CPU budget.

## Result

| quantity | value |
|---|---|
| best score (exact, 300 pairs) | **52** |
| CPU used / budget | 112.0 s / 112 s (wall 112.2 s) |
| inits (phase 1 ranking) | see `search-result.json` `inits` |
| best bits (lex, 250) | `search-result.json` `best_bits_lex`, sha256 in `bits_sha256` |

**Interpretation.** Score 52 > 0: this single bounded seeded heuristic run found **no** coloring with both red/blue common-neighbor counts ≤ 4 on all 300 pairs. This is **not** UNSAT, not a lower bound, not a proof — a heuristic failure to find 0. All original source/prior/significance holds stand untouched; zero credit; no Lean/no formalization; no other sizes, seeds, or repeats.

## Independent verification (step 3, ran unconditionally despite score > 0)

`scripts/verify_independent.py` (imports nothing from search.py): rebuilds all 250 edges and 300 pairs with plain loops, enumerates eligible common neighbors as explicit lists, recounts every red/blue count, exact score, degrees, part-neighbor rows.

- recomputed score **52 == saved 52** (`score_match: true`)
- bits sha256 matches `search-result.json` (`bits_sha_match: true`)
- 39 pairs carry excess; max red/blue common = 6; all 25 vertices red-degree exactly 10
- full per-pair table: `pair-count-table.json` / `verification.json` (`pair_count_table`, `degrees`, `part_neighbor_rows`)

## Deliverables

`results.json` (id 359209, credit 0) · `search-result.json` · `best-bits.json` · `verification.json` · `pair-count-table.json` · `scripts/{search,verify_frozen,verify_independent}.py` · `run_selftest.sh`, `run_search.sh` · `logs/` (selftest, search stdout/stderr, launch, frozen before/after, verify) · `frozen-before.json`, `frozen-after.json` (418/418 both) · `hash-manifest.txt` · `resource-receipt.json`.

## Handback state

No background processes; process group reaped (`pgrep` clean). No shared/old-lane edits; r1 preserved untouched. Stopped after the single run as instructed.
