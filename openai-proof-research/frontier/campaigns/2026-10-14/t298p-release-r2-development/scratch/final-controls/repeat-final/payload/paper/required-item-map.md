# Reviewer completion and attribution map

Locations refer to numbered sections of main.pdf and stable LaTeX labels in main.tex. This is an author response map, not an independent gate verdict.

## Four required contribution items

| Item | Manuscript location | Resolution |
|---|---|---|
| R1: NSS orbit credits and narrow contribution | Sections 1, 3.1, 8.1; eq:unitary-volume, eq:orbit-asymptotic | Names NSS Lemmas 2.6/2.8/2.9/2.10, unitary volume formula and Marinov; normal geometry and constants credited; claim confined to U1/U2/U3. |
| R2: supplied matrix units, corner and packing; entropy conventions; printed issues | Sections 8.1–8.2 | Credits corner p<=e11, compression map T and measure-preserving packing; states ultrafilter equality, one-sided ordinary limsup, left-to-reader proof and second-claim direction typo. Relative degeneracy is qualified correctly: ultrafilter microstates=-infinity, nonmicrostates relative=-infinity, ordinary-limsup relative value not computed by cited one-sided theorem. No infinity subtraction. |
| R3: smoothing, covariance, comparison, projection, heat and source template | Section 2 (i)–(iv), Sections 6.3 and 7 | Prop. 4.2 embeddability and n/2 proof constant versus printed n; covariance derivation; BCG/JP chi<=chi*; Prop. 2.8 plus projection; source eq:chistar/eq:freeflow and two-noise-scale credit. |
| R4: pinned generator paper | Section 8.3 | thm:main and cor:entropy-generators; classical Douglas–Pearcy/Wogen/DSSW 2x2 encoding; generation only, entropy depends on generators; coordinatewise companion transport does not shorten tuple. |

## All nine proof-review optional repairs

1. Historical uncertainty text: removed from theorem/proof narrative; Appendix A identifies superseded exploratory notes as provenance only.
2. Rank perturbation: Lemma 4.2 (lem:rank), explicit 2 L R^L m/N bound, telescoping proof and compression normalization.
3. Uniform source moment conditions: Lemma 4.3 (lem:recovery), fully quantified and proved from sequential recovery by contradiction.
4. Tube Jacobian: Lemma 3.1 final paragraph, determinant ratio of L+E to L at bundle coordinates, no triangular-shear assertion.
5. Theorem 4.1 hypotheses: Section 6.2, B=alg(T), grouped T coefficients, absolute majorants, both inverse identities, strict common norm margins, self-adjointness of F/G.
6. Relative-to-unconditional inequality: Section 2(i), Section 6.3, using Prop. 2.8 and projected microstate inclusion; explicitly avoids Prop. 2.12's reader-left equality.
7. Prop. 4.2 constant: Section 2(iv), n/2 proof constant and printed typo expressly noted.
8. Fixed multiplicity of rank losses: Lemma 4.3 second truncation, at most 2k² Hermitian parts per coordinate and 4k² total, fixed before N grows.
9. Ineffective epsilon/no small witness: Theorem 1.2 and Appendix A; fixed k=2^32, no useful quantitative epsilon or low-dimensional numerical witness.

## Additional normalization correction

The proof review's Section 6 prose accidentally omits the epsilon² k⁴ denominator in one energy equality. The score formula, reviewed candidate inequality and formal support all have the correct normalization. The equation labelled eq:leading-score, expressly includes Phi*(U)/(epsilon² k⁴). Section 6.1 changes time by dt=epsilon² k² du, yielding k^-2.

## Other contribution suggestions

Relative degeneracy and orbital logarithmic coefficient are included (8.2). Classical coefficient rotation/1/k normalization are credited (6.1). Theorem 4.1's omitted proof in arXiv v1 is disclosed (2 and 6.2). The frozen source-specialized transfer target is retained rather than adding a general theorem. The optional orbital/dimension/free-mutual-information leads remain explicitly unread at operative-body level (8.3 and reading-limits.md); no literature-priority clearance is claimed.

## Required manuscript r3 repairs

See revision-response.md. R1 is resolved in the explicit bilinear score definition, eq:entry-adjoint, eq:adjoint-product, eq:bilinear-pairing and the finite-Neumann-sum limit paragraph in Section5.3. R2 is resolved in AppendixA and README. Earlier numerical equation locations refer to the original r1 layout; stable LaTeX labels identify retained formulas in this revision. Fresh independent verification remains pending.
