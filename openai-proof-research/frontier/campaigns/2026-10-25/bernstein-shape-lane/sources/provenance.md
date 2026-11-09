# Source provenance and prior results

Retrieved 2026-10-25. This artifact makes no mathematical novelty or formalization-priority claim.

## Frozen task statements

`327180.json`, `327181.json`, and `327182.json` are byte-identical copies of the supplied files in `../twenty-proof-campaign/queued-sources/`. Their original identifiers, statuses, text, and provenance fields are preserved. The task concerns the common family

    phi_n(x) = sum_{k=0}^n choose(n,k)^2 x^(2k) (1-x)^(2(n-k)).

This related trio is ONE campaign outcome.

## Actual original source

- H. Gonska, I. Raşa, M.-D. Rusu, *Chebyshev-Grüss-type inequalities via discrete oscillations*, arXiv:1401.7908v1.
- Abstract record: https://arxiv.org/abs/1401.7908
- Download: https://arxiv.org/pdf/1401.7908v1
- Local full PDF: `1401.7908v1.pdf`; full text extraction: `1401.7908v1.txt`; complete original TeX: `1401.7908v1-source.tex`, retrieved from https://arxiv.org/src/1401.7908v1 (original gzip retained).
- Printed page 10: exact definition and Conjectures 3.2 (convexity), 3.3 (monotonicity), 3.4 (midpoint minimum).
- Printed pages 11-12: Lemma 3.5 proves the midpoint lower bound, with an explicit attribution to Thorsten Neuschel. The source then uses that result in Theorem 3.6.
- **Snapshot correction:** The assertion in the MathDB 327182 snapshot that no resolution is supplied by this source is contradicted by Lemma 3.5 in the retrieved version explicitly requested as v1. The PDF header itself identifies it as arXiv:1401.7908v1. We do not silently rewrite the task snapshot.

## Existing convexity proof

- Geno Nikolov, *Inequalities for ultraspherical polynomials. Proof of a conjecture of I. Raşa*, arXiv:1402.6539v1, submitted 26 February 2014.
- Abstract record: https://arxiv.org/abs/1402.6539
- Download: https://arxiv.org/pdf/1402.6539v1
- Local full PDF: `1402.6539v1.pdf`; full text extraction: `1402.6539v1.txt`; complete original TeX: `1402.6539v1-source.tex`, retrieved from https://arxiv.org/src/1402.6539v1 (original gzip retained).
- Printed page 2: Conjecture 1 is the exact Bernstein square-sum convexity claim; Theorem 2 states an equivalent Legendre ratio inequality.
- Printed page 3: Corollary 4 affirms Conjecture 1, using Theorem 3.
- Journal publication: Journal of Mathematical Analysis and Applications 418 (2014), 852-860; https://doi.org/10.1016/j.jmaa.2014.04.022.
- The present Lean proof does not assume Nikolov's inequalities. It independently proves the finite Fourier bridge and then uses convexity of a norm composed with an affine map.

## Existing Parseval-based proof

- Ioan Gavrea and Mircea Ivan, *On a conjecture concerning the sum of the squared Bernstein polynomials*, Applied Mathematics and Computation 241 (2014), 70-74.
- DOI: https://doi.org/10.1016/j.amc.2014.05.003
- Publisher page: https://www.sciencedirect.com/science/article/pii/S0096300314006596
- The publisher's accessible abstract asserts a new representation and a proof of the convexity conjecture; the accessible section descriptions state that Parseval's identity is used.
- Full text was not obtained. No precise theorem number, formula, or priority claim is inferred from that inaccessible full text. The finite Fourier approach is credited as belonging to this established representation/Parseval method.

## Mathematical dependency limits

The Lean theorem depends only on the pinned mathlib and its listed packages, not on any conjecture status, informal derivation, paper result, or result elsewhere in the campaign. The positive central-binomial coefficient identity suggested in the task is proved in the paper using continuous Fourier orthogonality and an elementary beta-moment recurrence. That identity is not formalized and is not used by Lean; the exact finite-average bridge that Lean does use is fully proved. An additional exact polynomial coefficient regression for n=0,...,32 is evidence only, not a universal proof.
