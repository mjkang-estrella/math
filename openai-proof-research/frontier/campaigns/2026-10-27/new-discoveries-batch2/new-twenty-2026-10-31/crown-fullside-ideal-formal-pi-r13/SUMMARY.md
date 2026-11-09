# SUMMARY — crown-fullside-ideal-formal-pi-r13 (handback)

Task: the two full-side ideal equalities for MathDB 369163 (full local v=4 chain),
lane r13, Pi/GLM-5.3-Flash execution, no children. 0 credit; 52/60 campaign.

Result: BOTH equalities are now literally proved and kernel-compiled strict
(lean 4.34.1, pinned toolchain, runner caps, -DwarningAsError, exit 0, zero
diagnostics), in new module CrownVFullSide over the UNCHANGED CrownVAlg Pc:

- CrownV.pcXside_eq_span : Pc (Xside n) = Ideal.span (coordGens (Xside n))
- CrownV.pcYside_eq_span : Pc (Yside n) = Ideal.span (coordGens (Yside n))

for every n : ℕ and every CommRing K, as ideal equalities in
MvPolynomial (V n × Bool) K. Both inclusions proved: span_mono for the trivial
direction; for the other, each completed-component minor (u,w ∉ side,
SameC (univ ∖ side) u w) is shown to have u = w — the complement is the
opposite side, the crown has no same-side edge (actual cadj, not mere
nonadjacency), so by the existing sameC_eq_of_forall_not_sEdge every path is
trivial — and minor v v = 0 by the defining subtraction. No sorry/admit/axiom/
unsafe/native_decide; scoped #print axioms audit (CrownVFullSideAudit, exit 0):
propext, Classical.choice, Quot.sound only.

Receipts (true exits, sha256 of source/olean/log in each JSON):
- receipt/1793994393954306964_lean_CrownVFullSide.json      exit 0
  src ed5c1f25283f58dc7f48fdc4dd22a018c2e83a4e3413754a9c42a39ed8930376
  olean 1cbeef27a1d719ca3735d422f55012fcd1f736667f0b8cf70070677e310ecfa9
- receipt/1793994413785910460_lean_CrownVFullSideAudit.json exit 0
  src fc848163b238f227021dbf41bdc28dab119e36d5dea79b47a5950d55749a85e7
  olean ace4615ef5857366c23c8604737a446d79b5044b9a2e5d608983c03cc133c1ab

Frozen inputs 698/698 verified before and after (verify_frozen.py before/after,
zero mismatches). Baselines r7/r9/r10/r11 used readonly via check.sh LEAN_PATH
only; no olean copying, no rebuilds, no environment changes. Protected lanes
transitive-bunkbed-prefix-helpers-formal-pi-r5 and expanded-corpus-r350
untouched. All runner jobs reaped; no background work left.

Unpaid next (exact): noncoordinate family ideals / kernel / primality /
J-structure; all-field degree 0..3 with char2 exclusion; quartic exact colons;
fullVIs4; then full extracted strict rebuild, audits, reviews, paper.
