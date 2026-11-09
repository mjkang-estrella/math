# r21 CHECKPOINT — crown greedy prefix identity (sealed)

Status: SEALED, expansion stopped at the single assigned milestone. Credit 0;
campaign 52/60 beyond 39 prior, unchanged.

## Executed sequence (actual)
1. `bootstrap.py` — done first; receipt `bootstrap-receipt.json` preserved untouched.
2. `verify_frozen.py before` — 1106/1106 frozen inputs match, zero mismatches
   (`frozen-before.json`).
3. FIRST mathematical operation: wrote `src/CrownVGreedyPrefix.lean` (literal
   finite sums over `Finset.range`, Nat truncated subtraction) and ran
   `check.sh CrownVGreedyPrefix`.
   - Attempt 1 nonpass, preserved: import `Mathlib.Algebra.BigOperators.Basic`
     absent in this pinned mathlib (reorganized layout) — receipt
     `1794011272299428065_lean_CrownVGreedyPrefix.json`, EXIT 1.
   - Attempt 2 sealed, EXIT 0, strict `warningAsError=true`, receipt
     `1794011356728191378_lean_CrownVGreedyPrefix.json`; correct import is
     `Mathlib.Algebra.BigOperators.Group.Finset.Basic` (home of the
     `@[to_additive]` `sum_range_succ`). No lane-convention/API probing occurred
     before the first write+compile; the only pre-compile read was the compiler
     diagnostic itself plus the import header check it motivated.
4. Scoped axiom audit `src/CrownVGreedyPrefixAudit.lean` via
   `check.sh CrownVGreedyPrefixAudit`, EXIT 0, receipt
   `1794011399476241157_lean_CrownVGreedyPrefixAudit.json`: all five new decls
   exactly `[propext, Classical.choice, Quot.sound]` (`greedyStepAux`
   `[propext, Quot.sound]`).
5. Module kernel check `checker.sh CrownVGreedyPrefix` (module-name leanchecker,
   pinned toolchain), EXIT 0, receipt
   `1794011408069941367_leanchecker_CrownVGreedyPrefix.json`.
6. `verify_frozen.py after` — 1106/1106, zero mismatches (`frozen-after.json`).
7. `ARTIFACT-MANIFEST.json` — actual on-disk 64-hex sha256 for both new sources,
   both oleans and all four run logs; receipts recorded by id with exit notes
   (receipt JSONs carry their own hashes; not self-hashed, lane convention).

## Sealed mathematical content
- `CrownV.greedyPre d k = ∑ i ∈ Finset.range k, d i` — literal finite prefix sum.
- `CrownV.greedyStep d r i = min (d i) (r - greedyPre d i)` — Nat truncation.
- `CrownV.greedyPrefix_sum d r k : ∑ i ∈ range k, greedyStep d r i
  = min r (greedyPre d k)` for ALL `d : Nat → Nat, r k : Nat`. One induction;
  the step is `greedyStepAux : min a b + min c (a - b) = min a (b + c)` (omega).
  Boundary cases k=0, r=0, zero capacities and saturation are instances of the
  single quantified theorem; no `r ≤ prefix` hypothesis anywhere in it.
- `CrownV.greedyPrefix_sum_of_le : r ≤ greedyPre d k → ∑ ... = r` (corollary).
- Not claimed here (unpaid): finite-block/Fin bridge, terminal uniqueness, and
  all downstream normal-form items; see results.json unpaid_followups.
