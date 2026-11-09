# CHECKPOINT — crown-fullside-ideal-formal-pi-r13

DONE (facts, this lane r13):
- verify_frozen before AND after: 698/698, zero mismatches (frozen-before.json / frozen-after via verify_frozen.py after).
- NEW src/CrownVFullSide.lean compiled strict (lean 4.34.1, -DwarningAsError=true, runner caps; exit 0, no diagnostics):
  receipt receipt/1793994393954306964_lean_CrownVFullSide.json
  source sha256 ed5c1f25283f58dc7f48fdc4dd22a018c2e83a4e3413754a9c42a39ed8930376
  olean  sha256 1cbeef27a1d719ca3735d422f55012fcd1f736667f0b8cf70070677e310ecfa9
  Theorems (namespace CrownV, original Pc/CrownVAlg untouched):
    pcXside_eq_span (n) (K) [CommRing K] : Pc (Xside n) = Ideal.span (coordGens (Xside n))
    pcYside_eq_span (n) (K) [CommRing K] : Pc (Yside n) = Ideal.span (coordGens (Yside n))
  Mechanism: complement of a full side is the opposite side; no crown edge inside one
  side (cadj needs opposite isX tags) => not_sEdge_univDiffX/Y; existing
  sameC_eq_of_forall_not_sEdge (CrownVClass) => every compMinor has equal endpoints;
  minor v v = 0 by the defining subtraction (sub_self); both ideal inclusions proved
  (span_mono one way; Ideal.span_le + per-generator the other). No sorry/axiom/unsafe/
  native_decide; no new Pc definition; both ideal inclusions, not FamPrime rewrites.
- Scoped axiom audit src/CrownVFullSideAudit.lean compiled exit 0:
  receipt receipt/1793994413785910460_lean_CrownVFullSideAudit.json
  source sha256 fc848163b238f227021dbf41bdc28dab119e36d5dea79b47a5950d55749a85e7
  olean  sha256 ace4615ef5857366c23c8604737a446d79b5044b9a2e5d608983c03cc133c1ab
  #print axioms pcXside_eq_span / pcYside_eq_span:
  [propext, Classical.choice, Quot.sound] only. Scope: lane audit on cached baseline
  oleans (r7/r9/r10/r11 readonly imports per check.sh); full extracted-rebuild audit
  NOT done here.
- All runner jobs reaped (leader_reaped note: reaped via Popen.poll; group_members_left []).

UNPAID (next):
- noncoordinate family ideals/kernel/primality/J-structure; all-field degree0..3 with
  char2 exclusion; quartic exact colons; fullVIs4; actual Pc/J algebra endpoints.
- full-proof extraction: EMPTY strict rebuild without old LEAN_PATH, module-origin/body
  audits, negative controls, independent reviews, paper.

Protected (untouched): transitive-bunkbed-prefix-helpers-formal-pi-r5, expanded-corpus-r350.
Frozen-after verified. No network/git/shared/parent/tmp-outside-lane writes.
