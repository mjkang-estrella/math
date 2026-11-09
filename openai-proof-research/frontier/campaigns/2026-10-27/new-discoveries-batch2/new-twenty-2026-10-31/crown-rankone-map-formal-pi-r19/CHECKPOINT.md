# r19 CHECKPOINT — crown rank-one map (sealed)

Status: SEALED, expansion stopped. Credit 0; campaign 52/60 beyond 39 prior, unchanged.

## Executed sequence (actual)
1. `bootstrap.py` — done first; receipt `bootstrap-receipt.json` preserved untouched.
2. `verify_frozen.py before` — 975/975 frozen inputs match, zero mismatches
   (`frozen-before.json`).
3. Mandatory missing kernel checks, sequential, supplied `checker.sh`, runner caps,
   no API inspection, all EXIT 0:
   - `CrownVCoordPrime`  receipt `1794007143667727499_leanchecker_CrownVCoordPrime.json`
   - `CrownVFullSidePrime` receipt `1794007147442855478_leanchecker_CrownVFullSidePrime.json`
   - `CrownVCoordDiff`   receipt `1794007153403768634_leanchecker_CrownVCoordDiff.json`
   Frozen 975 reverified intact after the checker sequence by direct sha256 comparison
   (zero mismatches); per-checker intermediate snapshots not separately emitted —
   verify_frozen labels are before/after only. Old modules untouched, READ-ONLY.
4. FIRST new-proof operation: wrote `src/CrownVRankOneMap.lean`, ran
   `check.sh CrownVRankOneMap`. Two preserved nonpass attempts
   (unpinned `n` in base-lemma headers → stuck metavars; then one unsolved
   `rankOneFun (v, b) = factVar b * vertVar v` goal), fixed by explicit type
   ascriptions + `rfl`; sealed run EXIT 0, receipt
   `1794007682218805194_lean_CrownVRankOneMap.json`, strict `warningAsError=true`.
5. Scoped axiom audit `src/CrownVRankOneMapAudit.lean` under the same runner, EXIT 0,
   receipt `1794007745184149534_lean_CrownVRankOneMapAudit.json`: all nine new
   decls exactly `[propext, Classical.choice, Quot.sound]`.
6. `ARTIFACT-MANIFEST.json`: actual 64-hex sha256, disk-rechecked, for both new
   sources, both oleans and all five new-module/checker logs; receipts recorded by
   id, not self-hashed (lane convention).
7. `verify_frozen.py after` — see `frozen-after.json`.

## Sealed mathematical content (no kernel-equality claim)
- `CrownV.RankOneCodomain n K = MvPolynomial (Bool ⊕ V n) K` — two independent
  factor variables (indexed by `Bool`), one independent factor variable per `v : V n`.
- `CrownV.rankOneHom : PolyRing n K →+* RankOneCodomain n K` via
  `MvPolynomial.eval₂Hom (MvPolynomial.C) rankOneFun`, `rankOneFun (v, b) =
  factVar b * vertVar v`; constants fixed (`rankOneHom_C`), variable action
  `rankOneHom_X/_xx/_yy/_xy`.
- `rankOneHom_minor u v : rankOneHom (minor u v) = 0` for ALL `u v : V n`.
- `allPairMinorIdeal n K = Ideal.span (allPairMinorSet n)` and
  `allPairMinorIdeal_le_ker : allPairMinorIdeal ≤ RingHom.ker rankOneHom` — inclusion ONLY;
  no reverse equality, no primality, no Pc(T) identification; `Pc`/`minor`/`PolyRing`
  used, never redefined.

## Protected (no read/hash/glob/poll performed)
Tournament update-lower r12; Sol crown-component-quotient-ordinary-ideation-r1.
No network/git/shared/author/parent/tmp writes; all writes via `write_lane.py`/lane scripts.

## Unpaid (exact)
reverse rank-one kernel; component ideals; J decomposition/direct colon; arbitrary
homogeneous degree 0..3 incl char2; quartic EXACT colons/VIs4; deep origin/body/type/
safety audits; negative controls; fresh all-source extracted replay; independent
reviews; paper; full endpoint; acceptance.
