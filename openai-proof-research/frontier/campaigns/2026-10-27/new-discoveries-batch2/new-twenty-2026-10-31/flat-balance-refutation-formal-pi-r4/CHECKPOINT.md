# CHECKPOINT — flat-balance-refutation-formal-pi-r4 (2026-11-07)

Terminal state: COMPLETE. Nothing pending inside this lane. No "next step"
interrupted work; every pipeline stage below has a true-exit receipt.

## Completed stages (receipt in receipt/, hash in SHA-MANIFEST.json)

1. `bootstrap.py` — done (bootstrap-receipt.json; frozen 791, editable src excluded, pristine copy frozen).
2. `verify_frozen.py before` — 791 ok, 0 mismatches.
3. Read of `src/FlatBalance.lean` (draft `ad57bf76…`), `input/r2-latest-production-failure.log`, `input/literal352972.json`.
4. Targeted repair of the 4 production clusters (250 / 258–260 / 318–320 / 390); NO baseline failed rerun, no probe modules.
   - strict build EXIT 0: receipt 1794077849162370651
   - kernel checker EXIT 0: receipt 1794077858358628717
5. Endpoint completed (parity sums 6/10/9; discrepancies 4 and 3 via `Int.natAbs`; `1 < D` both conventions; `K33_not_balanced`; `FlatBalancedConjecture` def; existential counterexample; literal universal negation).
   - one diagnostic failed rerun (if_pos/if_neg deprecation+mismatch) receipt 1794081112852911426, then fixed
   - FINAL strict build EXIT 0, zero diagnostics: receipt 1794081309058037712
   - FINAL kernel checker EXIT 0: receipt 1794081313646459863
6. Audit `audit/Audit352972.lean` EXIT 0: transitive `#print axioms` = exactly
   `{propext, Classical.choice, Quot.sound}` on the full endpoint chain; body prints of all core defs. Receipt 1794081428908960004.
7. Negative controls `audit/Controls352972.lean` EXIT 0 (9 controls). Receipts 1794081454508334320 (v1 diagnostic), 1794081468044737814 (final).
8. Source safety grep via runner: no sorry/admit/axiom/unsafe/partial/native_decide/extern/implementedBy. Receipt 1794081476585429321.
9. Clean extracted source-only replay: `extracted/src` == `src` (SHA
   `4a4ca90e…`); empty-build strict rebuild EXIT 0 (1794081493174672770); kernel check EXIT 0 (1794081511812753048; earlier PATH-less attempt 1794081500242996651 diagnostic). Extracted olean `385a976e…`; lane olean `aeb27a12…`.
10. `verify_frozen.py after` — 791 ok, 0 mismatches (t=1794081516.5).
11. Bookkeeping: `results/352972.json`, `SHA-MANIFEST.json` (all 13 receipt hashes + named self-exclusions), `SUMMARY.md`, this file.

## Hashes (authoritative)

- src/FlatBalance.lean: `4a4ca90e72d35f516ca4f84f9ab3fcb1e49527f5625278ed67ba2cabbeed889d`
- build/FlatBalance.olean: `aeb27a12596525015e0d88f64113eb578b3e20d02ad8b3b541481c28f5a574e0`
- extracted olean: `385a976e032ce8ee387317de77e3f952d09e6afede8707bd4b9d310cd8620552`
- results/352972.json: `7cd5d4bd546ad6a8fd4bc0a02e8e4503e873e3463708cee027b9d2abba6d273c`
- audit/Audit352972.lean: `7861f94d1441e05bc3f8a1facea709c8db2a7103a26ad286aa852b9f1841a39a`
- audit/Controls352972.lean: `d176c4d2c13fb5f45515b40b86bd89ee7fbe7dd52f39af296b6a58667887e08a`

## Remaining (outside this lane, per task)

Independent formal/source review; root acceptance and credit (count stays 52/60
until then; this lane claims 0). No paper/PDF was requested or produced.
