# Independent review: two matrix counterexamples

Decision: **PASS for both complete source-scoped counterexamples.** No mathematical, formal-coverage, source-fidelity, or attribution blocker found. Reviewed on 2026-10-26 by the independent Fibonacci-minima lane; this reviewer did not author either matrix artifact.

The reviewed authoritative artifacts are `thirty-proof-campaign/outcomes/weak-majorization/` and `thirty-proof-campaign/outcomes/coefficient-minor/`. The Lean files are byte-identical to the author's corresponding files in `extension-matrix-lane/`. Final parent TeX formatting changes were read and included in the hashes below. No artifact, shared index, or git state was edited by this reviewer.

## Reviewed content hashes

| Outcome | File | SHA256 |
|---|---|---|
| MathDB 372496 | `formal/WeakMajorization.lean` | `5e7b178594e22448192286bd8d0dee222392a2243a0f9b9e287f6c4c59ab9fc2` |
| MathDB 372496 | final `main.tex` | `c1374ae42074ac99a1867cd5aac78ed8d8d8afc11257583a43a56d711f63816a` |
| MathDB 380287 | `formal/CoefficientMinor.lean` | `751348723b7729f8c6933b972af494a1f0e73b228bc98ec777d3e659df6c4cd7` |
| MathDB 380287 | final `main.tex` | `e4d0b5efa0b1926f32f7e129ed3e9e1b9371191104e1fcbd52becb2afb074b66` |

This approval binds the formal and mathematical text above. PDF rendering/visual QA remains the parent's separate validation step; this review did not generate PDFs.

## Fresh pinned validation

The reviewer copied only each integrated manifest and Lean file into unique scratch outcomes at `extension-fibonacci-minima/review-matrix/{weak-majorization,coefficient-minor}/`, then independently ran the campaign's `twenty-proof-campaign/verify_outcome.py` on those copies. These were fresh isolated compilations, not acceptance of the author's preexisting objects.

Both audits passed with warnings treated as errors, using Lean 4.34.1 and the pinned dependency revisions checked by that verifier:

- Weak majorization: **18 declarations**, main theorem `WeakMajorizationCounterexample.source_counterexample`.
- Coefficient minor: **30 declarations**, main theorem `CoefficientMinorCounterexample.source_counterexample`.
- Both audit reports observed exactly `propext`, `Classical.choice`, and `Quot.sound`; no additional proof postulates or prohibited evaluation mechanism was used.

Fresh receipts and compiler logs are in the corresponding scratch `build/` directories. Additional isolated `ScopeChecks.lean` checks cover the actual antitone ordered eigenvalue enumerations and the semantic substitution of the three nested polynomial variables into the literal matrix pencil. These scope checks also compile with warning-as-error.

## MathDB 372496: weak majorization

**Primary-source match.** Read the actual archived Zhang text in `extension-matrix-lane/sources/372496.txt`, including Section 1's definition of ordered eigenvalues, weak majorization, `Q_k`, and Section 5's Conjecture 5.5. The source allows arbitrary Hermitian matrices and every integer `k ≥ 5`; it does not impose positive definiteness. Its operator order is exactly `A^j B^(k-j)`, and `R_k` is its Hermitian part. The formal `Q` and `R` match these definitions. The distinct singular-value question in Problem 1.1 is explicitly outside both theorem and paper.

**Spectral bridge.** Read mathlib `Mathlib/Analysis/Matrix/Spectrum.lean`: `eigenvalues₀` is the actual Hermitian spectral enumeration, with `eigenvalues₀_antitone` giving nonincreasing order. It is not an arbitrary vector fitted to the computation. The review's additional scope checks instantiate this ordering lemma for both matrices. The formal `WeakMajorized` takes initial partial sums on these `Fin` indices; its harmless `k=0` case adds only the empty-sum inequality. At full rank its sum is the entire spectrum. `trace_real_eigenvalues` derives the correct full sum from mathlib's trace identity and reindexes from the matrix index type to the ordered enumeration.

**Witness and full coverage.** The theorem proves both input matrices Hermitian, computes `H^5`, all six terms of `Q_5`, and `R_5`, and obtains traces `-82` and `-122`. Weak majorization would require `-82 ≤ -122` at full rank. Exponent 5 is admissible, so a single two-dimensional witness fully refutes the universal assertion. No eigenvalues, trace identities for the witness, or coefficient/source bridges are assumed as hypotheses. The final paper gives this full argument and correctly limits its scope to the eigenvalue conjecture and the `k=5` witness, rather than claiming the posted stronger all-odd-exponent statement.

**Credit.** Checked the archived MathDB post, solution UUID `d0710bc2-d7fb-47e4-ad1c-e207b1bc7f82`, attributed to Shivam Patel. Its exact body hash agrees with `source.json`. The paper and proof record explicitly call this verification of Patel's existing counterexample and deny discovery/priority claims. Primary HTML/text and full post snapshot hashes all agree with the manifest inventory.

## MathDB 380287: coefficient-minor stability

**Primary-source match.** Read Fisk's actual archived text at printed p619 (Chapter 21's stability definition) and printed p650 (Conjecture 21.90). Also visually inspected `380287-conjecture.png`, which reproduces printed p650. The conjecture really concerns coefficients in `y,z` of `det(I+xD1+yD2+zD3)` and every finite square minor as a polynomial in `x`. The source's one-variable stability means roots in the closed left half-plane, equivalently nonvanishing on the open right half-plane. The local `Stable` uses exactly the latter complex-evaluation condition.

**Coefficient variable and minor bridge.** Decoded the nested rings directly: `PX=ℝ[x]`, `PXZ=PX[z]`, `PXYZ=PXZ[y]`. In `pencil`, the inner `X` multiplies `D1`, the outer `X` multiplies `D2`, and the middle `X` multiplies `D3`. Thus `(determinant.coeff i).coeff j` really is `[z^j][y^i]` and leaves a polynomial in `x`. An independent Lean scratch check substitutes scalar `x,y,z` and confirms each pencil entry is `δij+x D1ij+y D2ij+z D3ij`. The complete determinant expansion is proved before extracting coefficients; `coefficient_bridge` identifies the displayed matrix with the actual submatrix rather than defining a substitute matrix. The `Fin 3` value maps select the distinct increasing indices 0,1,2. They lie in the source's genuine finite coefficient matrix (whose degree bound is 3); the ambient natural-number indexing introduces no extraneous selected rows or columns.

**Strict positivity and stability obstruction.** The formal witness proves all three real symmetric matrices strictly positive definite. It uses `Matrix.PosDef` and positivity for every nonzero vector, not semidefiniteness. The exact LDL/sum-of-squares formulas have strictly positive pivots; the proof successively forces all three coordinates to vanish if the quadratic form is zero. The actual selected minor is proved equal to `-4(3076x³+3012x²-99x-440)`. Its certified values at 0 and 1 have opposite signs, so the real intermediate value theorem supplies a root in `(0,1)`. The root is transported through the real-to-complex homomorphism to contradict the exact open-right-half-plane nonvanishing predicate. Thus this is a full counterexample to the source assertion, not merely a polynomial unrelated to its coefficient matrix. The minor is nonzero (its value at zero is 1760), so any convention about accepting the zero polynomial as stable is immaterial.

**Source caveat and credit.** The source example immediately following the conjecture has the same `D2,D3` but a semidefinite `D1`. Its nearby stability assertion is not used; the final paper correctly says so. The proof verifies the posted strictly positive definite replacement `diag(1,2,1)`. Checked Patel's existing MathDB solution UUID `5e36d5b0-235a-4456-8644-eabbd5f90132` and its exact body hash. All four archived source snapshot hashes agree with `source.json`. Both final prose and proof record preserve Patel's prior mathematical credit and make no novelty claim.

## Packaging observation resolved

The initially copied `PROOF.md` files referred to `../sources`, a path valid for neither integrated outcome. The reviewer notified the parent. The parent changed those statements to identify the separate local campaign source audit `extension-matrix-lane/sources` and explicitly says it is outside the standalone package; exact snapshot hashes remain in `source.json`. The final repaired wording was checked. This was a documentation-path correction, with no change to mathematics or formal source.

## Final assessment

**PASS: MathDB 372496 and MathDB 380287 are each fully covered by their explicit formal counterexample.** The source definitions, admissible hypotheses, construction/eigenvalue bridges, and failure conclusions were checked independently. Both final papers accurately report the formal scope and existing Patel credit. No unresolved rejection-level objection remains.
