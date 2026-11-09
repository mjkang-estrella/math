# CHECKPOINT — crown-coordinate-map-formal-pi-r15 (2026-11-06, sealed)

Done (all lane-local, true exits, unique receipts):
- [x] bootstrap.py first command; receipt preserved; verify_frozen before 768/768.
- [x] src/CrownVCoordMap.lean written as FIRST mathematical op; check.sh CrownVCoordMap
      strict success on 3rd run: receipt 1794000388003300228, EXIT=0,
      warningAsError=true clean, wall 1051 ms, CPU 1.033 s, peak sampled RSS ~2.3 GiB.
- [x] Sealed hashes: source a7b8f67a…7206, olean cc94d845…e8fa, log 52c90ce1…3553,
      receipt f665e648…24b4. No source edits after seal (re-verified a7b8f67a…7206).
- [x] Scoped #print axioms (audit/CrownVCoordMapAxioms.lean, runner receipt
      1794000447501533205, EXIT=0): all 8 decls exactly
      [propext, Classical.choice, Quot.sound]; no sorryAx/new axioms.
- [x] leanchecker on sealed olean: receipt 1794000491243562284, EXIT=0
      (3 earlier probe failures preserved: …462155720940, …470828968787, …481003321279).
- [x] verify_frozen after 768/768 (frozen-after.json c27cef02…7308).
- [x] results.json (ID 369163, credit 0, status AUXILIARY_COMPILED_MODULE_SEALED_NOT_ACCEPTED),
      ARTIFACTS-MANIFEST.json, SUMMARY.md — honest exclusions recorded.

Not done (unpaid, exact list also in results.json):
- [ ] kernel inclusion ⊆ and ⊇ (coordinate-kernel equality, both directions)
- [ ] fullside primality of Pc T
- [ ] noncoordinate families / J structure / direct colon
- [ ] homogeneous degrees 0..3 incl char-2 exclusion
- [ ] quartic EXACT colons / V(I,4)
- [ ] independent audits, negative controls, fresh all-source extracted replay, reviews, paper

Handback state: sealed module on disk with verifiable receipts; nothing future-tense.
Protected lanes r8 / Sol r356 untouched. No git, no shared writes, no delegates used.
