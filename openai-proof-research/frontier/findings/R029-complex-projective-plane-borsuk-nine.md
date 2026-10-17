# R029 — The Borsuk number of the complex projective plane is nine

**Accepted as the seventh substantial result of the 2026-10-14 campaign: 7/10.**
Acceptance is internal, with the stated source contracts and bounded literature comparison; it is not external peer review or certification of worldwide priority.

Let X = {uu*: u in C³, ||u|| = 1}, with the Frobenius metric in the eight-dimensional affine space of trace-one Hermitian matrices. Then diam(X) = sqrt(2) and b(X) = 9. Nine compact subsets cover X and each has diameter strictly below sqrt(2). Every cover by at most eight arbitrary subsets has a member of full diameter. No regularity of the latter subsets is assumed. This attains d+1 in dimension eight; it does not give a Borsuk counterexample there.

The added operation is a covariant perturbation of the Hesse rays, controlled by uniform two-trio estimates in complex neighborhoods of the twelve equality holes. The topological extension method, SIC/MUB geometry and compactness arguments are credited antecedents. The primary comparison includes exact exclusions for the checked non-SIC examples; it does not claim an exhaustive optimization of all nine-center constructions.

The [eleven-page manuscript](../campaigns/2026-10-14/complex-projector-borsuk-manuscript-r1/output/pdf/complex-projective-plane-borsuk-nine.pdf) has SHA256 `870941e2499b3005f13063694ce183d3c77fdbea6ead1263a3c3e49dd58a517b`. The original scope and candidate are unchanged. Independent gates:

- [Proof](../campaigns/2026-10-14/complex-projector-borsuk-review-r1/review.md): PASS_FULL_B8C.
- [Contribution](../campaigns/2026-10-14/complex-projector-borsuk-contribution-r3/review.md): SUBSTANTIAL.
- [Formal support](../campaigns/2026-10-14/complex-projector-borsuk-formal-review-r1/review.md): PASS_SCOPED_SUPPORT.
- [Manuscript](../campaigns/2026-10-14/complex-projector-borsuk-manuscript-review-r1/review.md): PASS_MANUSCRIPT, no required repairs.

**The full theorem is not formalized.** Sixteen supporting Lean theorems and three definitions cover exact scalar three-branch positivity, conditional score consequences and complex norm-square identities. Actual geometric score estimates, the projective/PSD construction, Borsuk–Ulam, compactness and strict-diameter attainment remain in prose. Fresh author, parent and independent source builds passed with Lean 4.34.1 and pinned mathlib, standard axioms only; five false mutations were rejected. The manuscript reviewer authored the separate formal implementation; a different reviewer independently audited that implementation. This relationship is disclosed rather than treated as independent formal validation.

The [public release](../campaigns/2026-10-14/complex-projector-borsuk-release/README.md) contains 284 files including its manifest. Archive `output/release/r029-complex-projective-plane-borsuk-nine-v1.zip` is 5,240,152 bytes, SHA256 `e2bf6164efaac7890a9adac3ed1b895ccd48dde397d42abbc1ff1318a8c88c51`. Bundle manifest SHA256: `a62e2b14d39aca9ec8712973dc421a8dd36d03fea003bdf37c1beea26ba0aa68`. Final gate SHA256: `30039b8c75485c014536c52a019e1a9cf82c4233c0fa474ac8f263d7d63e4867`.

Parent verification passed archive and clean-extraction integrity, byte-identical reassembly, the portable exact Appendix A certificate, byte-identical PDF rebuilding, and wrong-anchor, changed-file, missing-file, extra-file, symlink and pending-gate rejection. The independent manuscript reviewer inspected all eleven rendered pages. See the [final receipt](../campaigns/2026-10-14/complex-projector-borsuk-parent/final-package-verification.json). Hashes and finite diagnostics do not replace universal proof. Historical private-input verifiers are preserved with explicit portability limits; the top-level archive verifier is portable.

Author: Myeongjin Kang, no affiliation. Original prose CC BY 4.0; original code MIT. Public submission is authorized and underway; no upload, DOI or external acceptance is asserted by this acceptance record. Research continues toward 10/10.

## Public publication

Published 2026-10-17 UTC: [Zenodo PDF and complete supporting package](https://zenodo.org/records/23432031), DOI `10.5281/zenodo.23432031`; [MathDB paper](https://mathdb.com/abs/2610.00029). Public title, author, description and both Zenodo checksums were verified. All eleven MathDB PDF page rasters match outside its narrow platform stamp. See [submission receipts](../campaigns/2026-10-14/submissions/README.md). Earlier pending statements record the acceptance-time state; publication is not external peer review.
