# Proof and formal-support boundary

Theorem1.1 is exactly frozen T027O: ∀g≥2 ∀r≥2 ∃number field L⊂C ∃ρ:π1(Σ_g)→SL_r(O_L), the orientation-preserving Mod(Σ_g) orbit of [ρ] is Zariski dense in the entire complex SL_r character variety. The r≥3 construction allows L depending only on r; the original theorem permits g-dependence.

| Obligation | Full mathematical proof | Scoped Lean support |
|---|---|---|
| Rank2 actual integral representative and one dense orbit | §1.1, cited CL3.1.10/5.0.1/5.0.2 | None |
| SL relation/character irreducibility | §1.3, exact stipulated source intermediate assertion | None |
| Arithmetic torus and dense integral parameter family | §2 | None |
| Actual simple based curves and twists | §3 | None |
| Principal-minor rigidity | Lemma4.2, independent elementary proof with classical credit | Author package proves polynomial core; independent reviewer adds derivative bridge after lower-order identities |
| Generic Cartans and residual injectivity | §4 | None |
| Two-band and extra-handle cotangent certificate | §5 | None |
| Finite-open arithmetic selection then complex Baire | §6 | None |
| Component spectral cover, torus saturation, singular ideal/flow invariance | §7 | None |
| Open subset implies full density | §7, irreducibility input | None |

[Author scoped formal coverage](../t027o-formal-v1/README.md), [author support source](../t027o-formal-v1/T027O.lean), [independent scoped formal review](../t027o-formal-review-r1/review.md), [independent reviewer additions](../t027o-formal-review-r1/src/T027OReview.lean).

Formal author manifest anchor: b35948fddec735c7d9f0ed742d8158f4787f571cd69175a01f4db7ce2add46a4. Independent formal review anchor, supplied by parent: 2d71cfd5193c76f59c8b3bc5aa3e2fa9a5dea3191badfc6a868aa859d5789f2a. Reviewer terminal verdict is PASS_SCOPED_FORMAL_SUPPORT; parent adopted it after independent identity controls and a fresh54-declaration rebuild (copied adoption receipt in provenance/). This manuscript does not claim that the support or review proves the full theorem.

The formal reviewer compiled39 added declarations separately from the author's15 support/control declarations. Its derivative bridge uses polynomial first-order minors. Neither package covers Vandermonde/dense torus reduction, P2 existence, NB/BN rescaling, geometry, topology, arithmetic, or the orbit argument. Shared library object caches are trusted and not rebuilt. Formal rebuild command, if needed, begins `GIT_OPTIONAL_LOCKS=0 python3 -B ...`; this manuscript performs no formal-cache mutation or recompile.
