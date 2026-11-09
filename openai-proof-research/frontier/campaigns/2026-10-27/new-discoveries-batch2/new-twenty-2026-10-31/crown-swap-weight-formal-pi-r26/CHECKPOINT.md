# CHECKPOINT — crown-swap-weight-formal-pi-r26 (2026-11-07)

Milestone: **strict natural prefix-weight descent seal of CrownVSwapWeight** — single
strict exit-0 compile on the first mandated attempt; no repair cycle; no proof logic
authored.

## Mandated sequence (executed in order)

1. `bootstrap.py` — lane bootstrap, AGENTS/TASK read, first receipt preserved
   (`bootstrap-receipt.json`).
2. `verify_frozen.py before` — **1350/1350 frozen inputs intact**, 0 mismatches
   (`frozen-before.json`).
3. `bash check.sh CrownVSwapWeight` (first mathematical operation) — **EXIT=0**, strict
   `-DwarningAsError=true`, receipt `1794020574315053687_lean_CrownVSwapWeight.json`,
   olean produced (`build/CrownVSwapWeight.olean`, sha `c5bc8634…972b1d`), wall 4.5 s,
   peak group RSS sampled 1.69 GiB.

## Sealing steps

- Module-name checker through pinned PATH (lean 4.34.1): `bash checker.sh
  CrownVSwapWeight` → EXIT=0, receipt
  `1794020641311966811_leanchecker_CrownVSwapWeight.json`. Resolves `CrownVSwapWeight`
  by module name through LEAN_PATH — not a stale-olean pass.
- Scoped `#print axioms` on the ONE new declaration via
  `audit/CrownVSwapWeightAxioms.lean`, capped runner, receipt
  `1794020661311636767_axioms_CrownVSwapWeight.json`, EXIT=0:
  - `CrownV.swapAlloc_weight_strict`: `propext`, `Classical.choice`, `Quot.sound`
  Exactly the allowed three; no sorry/admit/new axiom/unsafe/partial/native_decide/
  extern/implementedBy anywhere in the module.
- `verify_frozen.py after` — **1350/1350 intact**, 0 mismatches (`frozen-after.json`).
- Postchecker rehash (`postcheck.json`): every receipt-recorded source/olean/log hash
  re-verified against actual disk bytes plus all three receipt-file hashes;
  `all_pinned_hashes_match: true`.
- Manifest with actual hashes including all three receipt JSON hashes: `manifest.json`.
- ID-keyed result with exact paid/unpaid boundary: `results/369163.json`.
- All runner groups reaped (`GROUP_MEMBERS_LEFT []` on every receipt).

## Paid (this milestone only)

`CrownVSwapWeight`: the ACTUAL strict natural finite-prefix weight descent
`swapAlloc_weight_strict` — for ALL `m i j : Nat`, `a : Nat → Nat` with `i < j < m`,
`0 < a j`: `∑ k < m, k * swapAlloc a i j k < ∑ k < m, k * a k`. About the real unchanged
double `Function.update` swap from sealed `CrownVSwapCapacity` (imported via
`CrownVSwapTotal`, not redefined); no proxy, no capacity/desired-weight premise, no
conclusion-encoding hypothesis. Proof: single-column indicator weight sums equal `i`
and `j`, termwise weighted unit balance from paid r25 `swapAlloc_shift`,
`Finset.sum_add_distrib` regrouping, strict descent by `omega` from `i < j`. Zero
proof-logic changes by this lane: only the root's mechanical conditional-name/Nat
namespace/sum-binder repairs to the copied r23 draft, accepted by the first strict
compile.

## Unpaid (boundaries in results/369163.json)

Normalization existence; finite-block allocation bridge; monomial ideal certificates;
arbitrary coefficients; reverse rank-one kernel; component/Pc; J/colons; degrees 0..3
incl char 2; quartic VIs4; full module-origin/body/type/safety/dependency/negative-
control audit and extracted replay; independent reviews/paper/acceptance. r22
uniqueness / r21 prefix / r24 capacity / r25 total remain scoped preserved milestones,
not endpoints. Credit 0; campaign 52/60 unchanged.

## Handback

Lane sealed on disk: `src/CrownVSwapWeight.lean`, `build/CrownVSwapWeight.olean`,
`logs/` (3), `receipt/` (3), `audit/`, `results/`, `postcheck.json`, `manifest.json`,
`frozen-before/after.json`. r23/r24/r25 artifacts and all 1350 frozen inputs untouched.
No delegate/network/git/browser use; tournament, transitive-bunkbed and
double-interval-piercing paths unread and unpolled.
