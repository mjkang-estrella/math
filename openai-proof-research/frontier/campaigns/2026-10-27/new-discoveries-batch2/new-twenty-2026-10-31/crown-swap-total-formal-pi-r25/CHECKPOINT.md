# CHECKPOINT — crown-swap-total-formal-pi-r25 (2026-11-06)

Milestone: **swap finite-prefix TOTAL-SUM seal of CrownVSwapTotal** — single strict
exit-0 compile on the first mandated attempt; no repair cycle; no proof logic authored.

## Mandated sequence (executed in order)

1. `bootstrap.py` — lane bootstrap, AGENTS/TASK read, first receipt preserved.
2. `verify_frozen.py before` — **1297/1297 frozen inputs intact**, 0 mismatches
   (`frozen-before.json`).
3. `bash check.sh CrownVSwapTotal` (first mathematical operation) — **EXIT=0**, strict
   `-DwarningAsError=true`, receipt `1794019967458390610_lean_CrownVSwapTotal.json`,
   olean produced (`build/CrownVSwapTotal.olean`, sha `1537f62e…f0d380`).

## Sealing steps

- Module-name checker through pinned PATH (lean 4.34.1): `bash checker.sh
  CrownVSwapTotal` → EXIT=0, receipt
  `1794020057139747422_leanchecker_CrownVSwapTotal.json`. Resolves `CrownVSwapTotal`
  by module name through LEAN_PATH — not a stale-olean pass.
- Scoped `#print axioms` on **BOTH new declarations** via
  `audit/CrownVSwapTotalAxioms.lean`, capped runner, receipt
  `1794020062813053667_axioms_CrownVSwapTotal.json`, EXIT=0:
  - `CrownV.swapAlloc_shift`: `propext`, `Quot.sound`
  - `CrownV.swapAlloc_total`: `propext`, `Classical.choice`, `Quot.sound`
  All within {propext, Classical.choice, Quot.sound}. No sorry/admit/new axiom/unsafe/
  partial/native_decide/extern/implementedBy anywhere in the module.
- `verify_frozen.py after` — **1297/1297 intact**, 0 mismatches (`frozen-after.json`).
- Postchecker rehash (`postcheck.json`): every receipt-recorded source/olean/log hash
  re-verified against actual disk bytes plus all three receipt-file hashes;
  `all_pinned_hashes_match: true`.
- Manifest with actual hashes including all three receipt JSON hashes: `manifest.json`.
- ID-keyed result with exact paid/unpaid boundary: `results/369163.json`.
- All runner groups reaped (`GROUP_MEMBERS_LEFT []` on every receipt).

## Paid (this milestone only)

`CrownVSwapTotal`: pointwise unit-balance `swapAlloc_shift` (swapped allocation +
indicator of `j` = original + indicator of `i`, via `i < j`, `0 < a j`) and
`swapAlloc_total`: for ALL `m i j : Nat`, `a : Nat → Nat` with `i < j < m`, `0 < a j`,
`∑ k < m, swapAlloc a i j k = ∑ k < m, a k`. Exact copied r23 statements about the
actual unchanged `Function.update` swap from sealed `CrownVSwapCapacity` (imported, not
redefined); no proxy, no capacity premise, no conclusion-encoding hypothesis. Zero
proof-logic changes: only compiler-prescribed `ite_eq_right`/`ite_eq_left` renames and
one omega diagnosed `No goals to be solved` removed.

## Unpaid (boundaries in results/369163.json)

Strict natural weight descent; normalization existence; finite-block bridge; monomial
ideal certificates; arbitrary coefficients; reverse kernel; component/Pc; J/colons;
degrees 0..3 incl char 2; quartic VIs4; full audit / negative controls / extracted
replay / independent review / paper / acceptance. Capacity paid only within its r24
scoped evidence. Credit 0; campaign 52/60 unchanged.

## Handback

Lane sealed on disk: `src/CrownVSwapTotal.lean`, `build/CrownVSwapTotal.olean`,
`logs/` (3), `receipt/` (3), `audit/`, `results/`, `postcheck.json`, `manifest.json`,
`frozen-before/after.json`. r23/r24 artifacts and all 1297 frozen inputs untouched.
No delegate/network/git/browser use; tournament and expanded-corpus r374 paths
unread and unpolled.
