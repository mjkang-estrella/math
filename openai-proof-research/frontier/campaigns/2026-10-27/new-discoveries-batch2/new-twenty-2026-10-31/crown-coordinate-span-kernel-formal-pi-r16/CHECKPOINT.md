# CHECKPOINT — crown-coordinate-span-kernel-formal-pi-r16 (2026-11-06, sealed)

Done (all lane-local, true exits, unique receipts):
- [x] bootstrap.py first command; receipt preserved (bootstrap-receipt.json untouched).
- [x] verify_frozen before: 820/820, no mismatches (frozen-before.json).
- [x] src/CrownVCoordSpanKernel.lean written as FIRST mathematical op; strict success
      on 3rd run: receipt 1794001212035007769, EXIT=0, warningAsError=true clean,
      wall 1052 ms, CPU 0.979 s, peak sampled RSS ~2.3 GiB.
      Failed probes preserved: 1794000917300525130 (exit 1), 1794001188616124216 (exit 1).
- [x] ONE theorem sealed: CrownV.coordSpan_le_ker :
      Ideal.span (coordGens T : Set (PolyRing n K)) <= RingHom.ker (coordKill (n:=n) (K:=K) T).
      K pinned explicitly; existing coordGens / sealed coordKill / sealed
      coordKill_xx_eq_zero & coordKill_yy_eq_zero used unchanged; no Pc(T); no
      reverse inclusion / primality / induction / fullside.
- [x] Sealed hashes: source 754af6ea…5ab32, olean 2898ba03…3d5f, log 5391d0c7…f46cf.
      No source edits after seal (re-verified post-checker).
- [x] Scoped #print axioms (audit/CrownVCoordSpanKernelAxioms.lean, runner receipt
      1794001385019952002, EXIT=0): coordSpan_le_ker exactly
      [propext, Classical.choice, Quot.sound]; no sorryAx/new axioms.
- [x] leanchecker kernel recheck of sealed olean by module name: receipt
      1794001400801494419, EXIT=0, PATH pinned to lean-4.34.1 toolchain bin;
      source/olean hashes re-verified MATCH after checker.
- [x] verify_frozen after (frozen-after.json) — see results.json.
- [x] results.json, ARTIFACTS-MANIFEST.json, SUMMARY.md — honest exclusions recorded.

Not done (unpaid, exact list in results.json):
- [ ] reverse kernel inclusion / coordinate-kernel equality
- [ ] fullside primality of Pc T; noncoordinate families / J structure / direct colon
- [ ] homogeneous degrees 0..3 incl char-2 exclusion; quartic EXACT colons / V(I,4)
- [ ] deeper audits, negative controls, fresh all-source extracted replay, reviews, paper

Handback state: sealed module + audit + checker receipts on disk; nothing future-tense.
Protected lanes: tournament upper-support r9, expanded-corpus Sol r358 untouched.
No git, no shared writes, no delegates; all runner jobs reaped.
