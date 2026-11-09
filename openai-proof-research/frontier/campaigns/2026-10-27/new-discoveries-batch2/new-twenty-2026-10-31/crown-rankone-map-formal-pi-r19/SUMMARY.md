# r19 SUMMARY — crown rank-one parametrization map (MathDB 369163 auxiliary milestone)

Executed by Pi GLM5.3Flash, no children. Credit 0; campaign 52/60 beyond 39 prior, unchanged.

## Delivered (actual, on disk)
- Mandatory kernel checks closed with genuine `leanchecker` receipts (EXIT 0, supplied
  `checker.sh`, sequential, runner caps): `CrownVCoordPrime`, `CrownVFullSidePrime`,
  `CrownVCoordDiff`. R18's axiom-audit-only state is superseded by actual checker
  receipts; its incorrect "Diff checker existed" note is corrected here.
- `src/CrownVRankOneMap.lean` (sealed, strict build EXIT 0): the actual rank-one
  parametrizing ring homomorphism `CrownV.rankOneHom` from the existing
  `PolyRing n K = MvPolynomial (V n × Bool) K` to the free codomain
  `RankOneCodomain n K = MvPolynomial (Bool ⊕ V n) K` (two independent Bool factor
  variables, one independent factor variable per vertex). Coefficients fixed via
  `MvPolynomial.eval₂Hom` + `MvPolynomial.C`; `X (v, b) ↦ factVar b * vertVar v`.
  Proved: constant action, full variable action (`_X/_xx/_yy/_xy`), and
  `rankOneHom_minor : rankOneHom (minor u v) = 0` for every pair `u v : V n`.
  Plus `allPairMinorIdeal` (span over ALL pairs, precisely defined) and
  `allPairMinorIdeal_le_ker` — an inclusion only.
- `src/CrownVRankOneMapAudit.lean`: scoped `#print axioms` for all nine new decls under
  the same runner — exactly `propext, Classical.choice, Quot.sound` each. Not counted
  as production.
- No kernel-equality, reverse-kernel, primality or Pc(T) claim is made; `Pc`, `minor`,
  `PolyRing` consumed, never redefined. No sorry/admit/new axioms/unsafe/
  native_decide. Only supplied wrappers used; all writes in-lane via `write_lane.py`.
- `ARTIFACT-MANIFEST.json`: actual disk-rechecked 64-hex sha256 for sealed sources,
  oleans and logs; `results.json` carries latest true exits and the exact unpaid list.
- Frozen inputs 975/975 before (`frozen-before.json`) and after (`frozen-after.json`),
  zero mismatches; bootstrap receipt preserved.

## Attempts preserved
Two nonpass `CrownVRankOneMap` runs (receipts `1794007470589692903`, `1794007660579673873`
era) retained with logs: unpinned `n` metavariables in the two base-lemma headers, then
one unsolved defeq goal; fixed by explicit ascriptions, no proof restructure.

## Unpaid (exact)
reverse rank-one kernel equality; kernel/image primality; identification with actual
Pc(T) evaluation; component ideals; J decomposition/direct colon; homogeneous degree
0..3 incl char2; quartic EXACT colons/VIs4; deep origin/body/type/safety audits;
negative controls; fresh all-source extracted replay (this lane reuses pinned cached
oleans read-only); independent reviews; paper; full endpoint; acceptance.
