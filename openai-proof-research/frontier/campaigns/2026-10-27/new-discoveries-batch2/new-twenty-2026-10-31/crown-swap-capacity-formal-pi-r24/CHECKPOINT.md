# CHECKPOINT — crown-swap-capacity-formal-pi-r24 (2026-11-06)

Milestone: **capacity-only seal of CrownVSwapCapacity** — single strict exit-0 compile on the
first mandated attempt; no repair cycle needed; r23 failure history not repeated.

## Mandated sequence (executed in order)

1. `bootstrap.py` — lane bootstrap, AGENTS/TASK read, first receipt preserved.
2. `verify_frozen.py before` — **1245/1245 frozen inputs intact**, 0 mismatches
   (`frozen-before.json`).
3. `bash check.sh CrownVSwapCapacity` (first mathematical operation) —
   **EXIT=0**, strict `-DwarningAsError=true`, receipt
   `1794019498816700509_lean_CrownVSwapCapacity.json`, olean produced
   (`build/CrownVSwapCapacity.olean`, sha `7c80ab9d…efabb23`).

## Sealing steps

- Module-name checker through pinned PATH (lean 4.34.1):
  `bash checker.sh CrownVSwapCapacity` → EXIT=0, receipt
  `1794019538688071155_leanchecker_CrownVSwapCapacity.json`. Not a stale-olean pass: the
  checker resolves `CrownVSwapCapacity` by module name through LEAN_PATH.
- Scoped `#print axioms` on **all six declarations** via
  `audit/CrownVSwapCapacityAxioms.lean`, run under the capped runner, receipt
  `1794019565397621244_axioms_CrownVSwapCapacity.json`, EXIT=0:
  - `CrownV.swapAlloc`: no axioms
  - `swapAlloc_eval`, `_at_i`, `_at_j`, `_at_else`: `propext`
  - `swapAlloc_capacity`: `propext`, `Quot.sound`
  All within {propext, Classical.choice, Quot.sound}. No sorry/admit/new axiom/unsafe/
  partial/native_decide anywhere in the module.
- `verify_frozen.py after` — **1245/1245 intact**, 0 mismatches (`frozen-after.json`).
- Postchecker rehash (`postcheck.json`): every pinned source/olean/log/receipt hash
  re-verified against actual disk bytes; `all_pinned_hashes_match: true`.
- Manifest with actual hashes including all three receipt JSON hashes: `manifest.json`.
- ID-keyed result with exact paid/unpaid boundary: `results/369163.json`.
- All runner groups reaped (`GROUP_MEMBERS_LEFT []` on every receipt); no zombies on the
  host scan.

## Paid (this milestone only)

Actual double `Function.update` swap allocation (`swapAlloc`: +1 at `i`, −1 at `j`, one
unit moved j→i), pointwise helpers `swapAlloc_eval/_at_i/_at_j/_at_else` on the exact
copied statements, and `swapAlloc_capacity`: for arbitrary `m i j d a` with `i < j`,
`j < m`, `a i < d i`, and every `k < m` with `a k ≤ d k`, every value of the swapped
allocation is `≤ d k`. Six declarations: one def, five theorems. Zero proof-logic changes
by this lane; only the root's compiler-prescribed `ite_eq_right`/`ite_eq_left` renames
stood between r23 diagnostics and this compile.

## Unpaid (boundaries recorded in results/369163.json)

Prefix total-sum; strict natural weight descent; normalization existence; finite-block
allocation bridge; monomial ideal certificates; arbitrary coefficients; reverse rank-one
kernel; component/Pc fidelity; J/colons; degrees 0..3 incl. characteristic 2; quartic
VIs4; full audit / negative controls / extracted replay / independent reviews / paper /
acceptance. Credit 0; campaign 52/60 unchanged.

## Handback

Lane sealed on disk: `src/`, `build/CrownVSwapCapacity.olean`, `logs/`, `receipt/` (3),
`audit/`, `results/`, `postcheck.json`, `manifest.json`, `frozen-before/after.json`.
Frozen inputs and the r23 `src/CrownVGreedySwap.lean` untouched.
