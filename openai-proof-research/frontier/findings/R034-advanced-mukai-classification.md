# R034 — Advanced Mukai classification from independent quantum correspondences

**Accepted as the twelfth substantial result of the 2026-10-14 campaign: 12/20.** Internal acceptance uses the stipulated pinned source and bounded primary comparison; it is not external peer review or worldwide-priority certification.

Assume source S1 (generalized Mukai bound and equality classification) and essential stronger internal S2 (a nonzero word of r numerically independent genus-zero two-point correspondences with total degree budget) at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. For every smooth connected positive-dimensional complex projective Fano manifold X of dimension n, actual Picard number r and pseudoindex i with r(i−1)≥n−1, X is one of:

1. (P^(i−1))^r.
2. Q^i × (P^(i−1))^(r−1), with i≥3.
3. P over P^i of O^(i−1)⊕O(1), times (P^(i−1))^(r−2), with r≥2 and i≥2.
4. P over P^i of T(P^i), times the same product, with r≥2 and i≥2.
5. P^i × (P^(i−1))^(r−1), with r≥2 and i≥2.

Projectivizations parametrize one-dimensional quotients. The converse and actual invariants are proved: type1 has n=r(i−1), and types2–5 have n=r(i−1)+1. No dimension, rank, contraction, symmetry or covering hypothesis is added. Small dimensions, the actual-rank Q² exception, and equivalence to Fujita's lower-Picard-parameter formulation are explicit. See the [frozen full scope](../campaigns/2026-10-14/fresh-arithmetic-discovery-r18/fixed-scope.md). S2 is not inferred from S1; both are stipulated also on induction bases.

The integrated new deduction retains the supported composed virtual cycle's dimension n+s≥2n−1. A saturated full rational-chain quotient puts endpoint pairs in the same fiber or in the complement square. The dimension bound leaves a base of dimension at most one; a compact fiber divisor avoiding finitely many numerical spanning representatives excludes the curve base. Full chain connectivity then supplies bounded-degree competitors at every minimal horizontal step. The strict degree cutoff makes all selected families unsplit, allowing Fujita's existing extremal-ray criterion, induction and bundle classifications to finish.

Source equality, low-degree arithmetic, Kollár/Fujita quotient theory, Fujita's construction and final classification, and Dedieu–Höring's rank-one characterization are credited antecedents. Both complete Watanabe versioned papers were compared independently: the first includes rank-two defect-one cases; the revised second requires a birational extremal contraction. No already classified special case is counted separately. The contribution review rates the integrated bridge substantial, moderately so.

All independent gates passed at the unchanged full classification:

- [Full proof](../campaigns/2026-10-14/agm063-proof-r1/review.md): PASS_FULL_AGM063.
- [Contribution](../campaigns/2026-10-14/agm063-contribution-r1/review.md): SUBSTANTIAL (moderate).
- [Scoped Lean support](../campaigns/2026-10-14/agm063-formal-review-r1/review.md): PASS_SCOPED_SUPPORT.
- [Full manuscript](../campaigns/2026-10-14/agm063-manuscript-review-r1/review.md): PASS_FULL_MANUSCRIPT_AGM063; no required repairs remain.

**The full geometric theorem is not formalized.** Lean proves 29 support theorems among35 declarations across finite degree budgets, integer dimension arithmetic, saturated relation endpoint decomposition, actual reflexive-transitive chain preservation, spanning linear-functional contradiction, and actual Picard/pseudoindex induction arithmetic. Saturation, dimension bounds, spanning, positive witnesses and generator preservation are supplied abstract hypotheses. Fano geometry, stable-map moduli, virtual cycles, quotient existence, horizontal families, contractions, bundle classifications and converses remain human proof. S1/S2 are not Lean axioms. Root and independent reviewer freshly built the support with pinned Lean4.34.1/mathlib. The reviewer added nine boundary theorems and five false goals; installed kernel/runtime and prebuilt dependency objects remain trusted.

The mathematical author drafted the exposition; a successor Astra worker finalized it with separately disclosed reading provenance. A nonauthor audited both formal support and manuscript and independently read both complete Watanabe bodies. That reviewer authored none of the candidate, code or manuscript. Its requested genus-zero qualifier was incorporated in the low-degree lemma before sealing. Original Kollár is used through Fujita's exact statement; Fulton's chapter bodies were not newly read, and the standard contracts and explicit supported construction are disclosed. These limits remain part of acceptance.

The [nine-page manuscript](../campaigns/2026-10-14/agm063-manuscript-r1/output/pdf/advanced-mukai-classification.pdf) has SHA256 `bb9d911bf972f91d57f6e00b037ecd012e2cd892927d22ebbb5fa8ca0682b4b5`. Root and independent reviewer directly inspected every page. The [385-file local release](../campaigns/2026-10-14/agm063-release/README.md) passed20 integrity/reproduction controls, deterministic byte-identical reassembly, fresh PDF reproduction and all nine identical page rasters. Archive SHA256 `dae896492c72fd0fdf1b3b8916edd3438182fac71196976b2083b4d2c02499ae`; bundle manifest `7360b1959d10a8bbe333cf7f2feab20c0e6f8f0f13af3a13113a116ce09eb3e8`; final gate `800a31666ae1712b503fca19a9e6f0807adaae9a52282b524716bf342ff1e6b5`; outer seal `cd86e96ff8a76c61bdad80fd048ef2f8412a212ad195bf1dc0be0c92c4ad7c71`. Third-party bodies, private contract-page images and dependency objects are excluded; original private-packet verifiers retain disclosed workspace requirements. Integrity checks do not prove geometry.

Author: Myeongjin Kang, no affiliation. Original prose CC BY4.0; original code MIT. Uploads/publication remain stopped. The [acceptance receipt](../campaigns/2026-10-14/agm063-parent/acceptance.json) records the subsequent parent decision; immutable preparation records retain historical nonacceptance states. Eight further accepted results remain.
