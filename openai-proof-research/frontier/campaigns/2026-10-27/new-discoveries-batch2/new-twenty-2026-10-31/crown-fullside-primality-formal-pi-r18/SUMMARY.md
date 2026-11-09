# r18 SUMMARY — crown fullside/coordinate primality (MathDB 369163 auxiliary milestone)

Executed by Pi GLM5.3Flash, no children. Credit 0; campaign 52/60 beyond 39 prior, unchanged.

## Delivered (actual, on disk)
- `src/CrownVCoordPrime.lean` (sealed first): `CrownV.coordKer_isPrime` — the kernel of the
  actual endomorphism `CrownV.coordKill T` is prime, by `1 ↦ 1 ≠ 0` properness and
  domain cancellation `mul_eq_zero` on the codomain; and `CrownV.coordSpan_isPrime` —
  `Ideal.span (coordGens T)` is prime, via the frozen `CrownV.coordKill_ker_eq` only.
  All `n : Nat`, arbitrary `K` with `[Field K]`, all `T : Finset (V n)`; n=0, empty/full T,
  all characteristics included by generality. No Pc redefinition, no quotient construction,
  no containment proxy: genuine `Ideal.IsPrime` (properness + factor splitting).
- `src/CrownVFullSidePrime.lean`: `CrownV.pcXside_isPrime`, `CrownV.pcYside_isPrime` — the
  original `CrownVAlg.Pc` fullside ideals are prime, rewritten by the frozen
  `pcXside_eq_span` / `pcYside_eq_span` and closed by `coordSpan_isPrime`.
- `src/CrownVFullSidePrimeAudit.lean`: scoped `#print axioms` under the same runner for all
  four new theorems — exactly `propext, Classical.choice, Quot.sound` each — and for the
  completed r17 `CrownV.coordKill_sub_mem_span` from its sealed readonly olean (its
  previously missing checker receipt is now an actual receipt+log).
- Strict builds (`warningAsError=true`, pinned Lean 4.34.1, runner caps): all three modules
  EXIT=0. Latest true exits/receipts in `results.json`; `ARTIFACT-MANIFEST.json` carries
  actual sha256 for 9 artifacts, disk-rechecked, with honest exclusions.
- Frozen inputs: 924/924 before and 924/924 after, zero mismatches.

## Attempts preserved
First attempt nonpass (`Ideal.mem_top` unknown in this renamed mathlib → `Submodule.mem_top`)
and the intermediate single-file pass are retained with receipts; sealed two-module split
supersedes them.

## Unpaid (exact)
noncoordinate families; J-structure/direct-colon; all-field homogeneous degree 0..3 incl
char2; quartic EXACT colons/VIs4; full origin/body/safety/type audits beyond this scoped
axiom audit; negative controls; fresh extracted all-source replay (this lane is development
reuse of pinned cached oleans, not a replay claim); independent reviews; paper; full
endpoint; acceptance; deeper independent r17-Diff recheck.
