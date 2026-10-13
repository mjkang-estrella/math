# I245 — reading and attempted failures

## Scope

Work stayed in `/home/mj-kang/Documents/Dev/math/openai-proof-research`. Only the assigned I245 review, experiment files, literature index and fully read primary-excerpt copies were written. No subordinate agents, live I243 or other gate outputs, shared edits, staging, commits, publication, research code, tests, numerical experiments, scans, snapshots, seals, or giant history replay were used. Python was used only for retrieval, extraction/string provenance comparison, JSON metadata, and hashes. Shell text writes produced the review artifacts.

Read AGENTS.md and sources/upstream.json in full; sources/CONTENTS.md lines 7920–7955; only the two exact manuscript metadata entries from sources/preprints-tree.json. Read the requested I242 analytic file in full and verified its supplied SHA-256 before review. Read I242 input-authentication.json in full for provenance; the final I242 report, reading record and literature index were also supplied in the prompt. No unrelated historical reports were opened.

## Primary reading

- Direct pinned manuscript excerpts: complete thm:main and tensor convention; all retained Sections 2–3, including lem:faber, prop:coefficients, lem:resolvent, thm:domain, their proofs, both ordered tests, constant terms, reciprocal diagonal weights and positive-block trace; lem:approx statement. Entire retained excerpt read. Independently fetched the pinned raw manuscript, computed SHA-256 and Git blob, matched the tree metadata, and matched all three retained excerpt blocks verbatim. The unretained whole manuscript was not claimed as newly read.
- Structural companion excerpts: conformal-coordinate lemma, thm:structural, thm:representation, complete prop:density proof, equality fibers and both density systems, complete lem:comparison proof. Entire retained excerpt read. Independently fetched and authenticated the pinned raw manuscript; all four retained excerpt blocks matched verbatim. No truth audit of the pin was performed.
- Shanmu Jin, Rigidity at the Extremal Crouzeix Constant, v2: entire retained primary lines 93–738, Sections 1–8 and Corollary 1, read across bounded chunks with no skipped proof. This includes the scalar constant's definition, Theorem 1, finite confluent Schur interpolation and uniqueness, strict domain monotonicity, boundary-spectrum induction, equality vectors, rational collapse, full-level set, and algebraic contact proof. A live primary-page request confirmed version 2 and the scalar theorem; the page redirects the versioned URL to its current base URL while identifying itself as version 2. The retained primary excerpt, rather than the live result's abbreviated display, supplies full proof reading.
- Åhag–Czyż–Virtanen, arXiv:2608.27346v3: entire retained Section 11 through Corollary 11.5 read, including proofs and the explicit complete-dimension-three boundary. Used for attribution/prior-art comparison only. No new dependence on its Proposition 10.1 or its unretained proof was introduced.

All four primary excerpt files copied to the I245 source directory had been fully read first. Their original source labels and line extents are preserved. Copying a retained primary passage is not a snapshot or seal of project state.

## Active objections tested analytically

1. Wrong exterior logarithm sign: differentiating gives zL'=2∫ξ/(z−ξ), confirming the plus sign in front of log(1−ξ/z).
2. Exterior derivative blowup on convex corners: the Herglotz upper bound 4c and uniform logarithmic Fourier tails handle the nonsmooth limit; no lower derivative bound is used.
3. Incorrect inverse-map limit or boundary parametrization: expanded the two-sided inverse argument and supplied the Jordan-boundary/reflection step. It identifies both h and its derivative and gives a positive-measure circle interval.
4. Divergent Faber normalization: resolved for the fixed active irreducible block by its strict interior spectrum, bounded resolvents and the derivative upper bound. No estimate uniform over all matrices is claimed.
5. Lost constant term or reversed product: compared against the actual source. The residual contains 3||Y*X||² and both coefficient orders, and the factor two is correct.
6. Passing a nonlinear expression through weak convergence: not used. The proof passes tr(HDHD) in L¹ using strong L², then uses nonnegativity to recover the square-root identity.
7. Trace zero mistaken for total isotropy: the squared Hilbert–Schmidt norm of H^(1/2)DH^(1/2) is exactly the trace, so zero gives the whole matrix identity. The resulting inertia count is valid.
8. Simple support assumed generically: independently checked the dimension-four two-generator reduction and the positive-curvature derivative formula. Neither simple ordinary spectrum nor genericity is needed.
9. An a.e. equality missed the regular arc: the exterior boundary homeomorphism and local reflection make its preimage an open circle interval.
10. Conjugated coefficient vector: explicitly used X=ξu^T so that x=ξ⊗u under the source convention. Scalar p=v*Pu follows with no transpose error.
11. Losing full-range normalization during block selection: the complete bound forces the active block's normalization to remain one. The scalar polynomial is bounded on the original full range.
12. Unjustified H∞ interpolation or outer-block step: gave radial dilations and Taylor approximation to derive the needed H∞ estimate from the stipulated polynomial bound. Minimal spectral-jet interpolation norm is one, so Jin's precise uniqueness assertion applies; the polynomial monomial then controls the full range.
13. I238 weighted-chain obstruction: recomputed conceptually from the exact weights. It still refutes output nilpotent amplification, but agrees with coefficient scalarization p=z. No test code or numerical values were generated.
14. Matrix Schur saturation mistaken for scalarity: not used before rank reduction. A constant unitary channel remains an obstruction to that alternative argument.

No substantive gap survived these checks. The report is PASS, with explanatory expansions in analytic-check.md. Positive-deficit quantitative stability, a nonattained complete supremum, and exhaustive literature novelty remain outside the approved statement.

## Tool/output limitations

One batched read returned an overall truncated output containing part of Jin's long excerpt. The complete 653-line retained excerpt was then reread in three bounded, nontruncated chunks, so no missing portion was counted as read. No mathematical inference rests on a truncated or search-only passage. The pinned provenance retrievals completed successfully. No missing source or approval blocked the review.
