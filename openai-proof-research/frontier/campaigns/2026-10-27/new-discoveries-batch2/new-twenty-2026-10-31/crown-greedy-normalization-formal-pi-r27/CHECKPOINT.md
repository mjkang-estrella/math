# CHECKPOINT — crown-greedy-normalization-formal-pi-r27 (2026-11-07)

Milestone: **finite legal-swap normalization to the greedy allocation, sealed in
`CrownVGreedyNormalize`** — genuine implementation, three diagnostic-driven repairs
retained, final strict exit 0, module checker and scoped axiom audit pass.

## Mandated sequence (executed in order)

1. `bootstrap.py` — lane bootstrap, AGENTS/TASK read, first receipt preserved
   (`bootstrap-receipt.json`).
2. `verify_frozen.py before` — **1404/1404 frozen inputs intact**, 0 mismatches
   (`frozen-before.json`).
3. `src/CrownVGreedyNormalize.lean` written as the FIRST mathematical operation
   (genuine attempt: legal-swap relation + weight-bound induction + paid
   uniqueness), then `bash check.sh CrownVGreedyNormalize` BEFORE any
   API/style/signature search or planning — per TASK.
4. Diagnostic-driven repairs, all retained as true receipts (no stale olean pass):
   - attempt 1 (exit 1): `ReflTransGen` unresolved (namespace `Relation`);
     auto-implicit `n` binder → cascade.
   - attempt 2 (exit 1): added `open Relation`; `∀ n a : Nat → Nat` still
     elaborated `n` as auto-implicit → annotated `(n : Nat)`.
   - attempt 3 (exit 1): `le_trans` needs `≤`, had `=` → `le_of_eq`.
   - attempt 4: **EXIT=0**, strict `-DwarningAsError=true`, receipt
     `1794021633820455370_lean_CrownVGreedyNormalize.json`, olean
     `build/CrownVGreedyNormalize.olean` sha `3c6f0dac…2fe093a`.

## Sealing steps

- Module-name checker through pinned PATH (lean 4.34.1): `bash checker.sh
  CrownVGreedyNormalize` → EXIT=0, receipt
  `1794021664919650528_leanchecker_CrownVGreedyNormalize.json`. Resolves
  `CrownVGreedyNormalize` by module name through LEAN_PATH — not a stale-olean pass.
- Scoped `#print axioms` on ALL FOUR new declarations via
  `audit/CrownVGreedyNormalizeAxioms.lean`, capped runner, receipt
  `1794021674245942135_axioms_CrownVGreedyNormalize.json`, EXIT=0:
  - `CrownV.LegalSwap`, `CrownV.Terminal`: no axioms
  - `CrownV.normalizeAux`, `CrownV.greedyNormalize`: `propext`,
    `Classical.choice`, `Quot.sound`
  Exactly the allowed three; no sorry/admit/new axiom/unsafe/partial/
  native_decide/extern/implementedBy.
- `verify_frozen.py after` — **1404/1404 intact**, 0 mismatches (`frozen-after.json`).
- Postchecker rehash (`postcheck.json` via `seal_postcheck.py`): sealed
  strict/checker/axioms receipts re-verified against actual disk bytes (source,
  olean, log, audit) plus all six receipt-file hashes;
  `all_pinned_hashes_match: true`; the three failed-attempt receipts retained as
  diagnostic history with their true exits.
- Manifest with actual hashes including all receipt JSON hashes: `manifest.json`.
- ID-keyed result with exact paid/unpaid boundary: `results/369163.json`.
- All runner groups reaped (`GROUP_MEMBERS_LEFT []` on every receipt).

## Paid (this milestone only)

`CrownVGreedyNormalize`: finite legal-swap normalization.
`LegalSwap m d a b` := `∃ i j, i < j ∧ j < m ∧ a i < d i ∧ 0 < a j ∧ b = swapAlloc a i j`
— legality and the actual update only; no preservation/descent/terminality/canonical
clause in the relation. Endpoint `greedyNormalize`: for ALL `m r : Nat`,
`d a : Nat → Nat` with prefix capacity and `∑_{k<m} a k = r` (no `m > 0`, no
positivity, no proxy, no conclusion-bearing premise) there EXISTS `b` with
`Relation.ReflTransGen (LegalSwap m d) a b` — a genuine finite swap chain — such that
`b` keeps prefix capacity, keeps total `r`, is terminal (underfull earlier ⇒ later
zero), and `b k = greedyStep d r k` on the whole prefix via paid r22
`greedy_terminal_unique`. Mechanism: paid r26 strict weight descent
`swapAlloc_weight_strict` + plain induction on a weight bound; base case (weight 0)
is terminal by the positive-weight columns argument; successor performs the one
legal swap witnessed by non-terminality and descends below the bound. Capacity and
total carried by paid r24/r25 lemmas. Empty prefixes and zero budgets: same
universal statement, no special-cased premises. Outside-prefix values untouched.

## Unpaid (boundaries in results/369163.json)

Finite-block allocation bridge; monomial difference certificates/arbitrary
coefficients; reverse rank-one kernel; component/Pc; J/colons; degrees 0..3 incl
char 2; quartic VIs4; full module-origin/body/unabridged-type/safety/negative-
control audit and extracted replay; independent reviews/paper/acceptance. r22
uniqueness / r21 prefix / r24 capacity / r25 total / r26 weight descent remain
scoped preserved milestones, not re-proved here. Credit 0; campaign 52/60 unchanged.

## Handback

Lane sealed on disk: `src/CrownVGreedyNormalize.lean`,
`build/CrownVGreedyNormalize.olean`, `logs/` (6), `receipt/` (6), `audit/`,
`results/369163.json`, `postcheck.json`, `seal_postcheck.py`, `manifest.json`,
`frozen-before/after.json`. Frozen inputs (1404) and all prior crown lanes
untouched; no r23-style stall; no delegate/network/git/browser use.
