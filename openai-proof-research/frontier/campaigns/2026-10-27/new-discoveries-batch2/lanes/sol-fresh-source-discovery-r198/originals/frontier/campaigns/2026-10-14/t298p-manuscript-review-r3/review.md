# Independent full T298P manuscript review, round 3

Verdict: **NEEDS_REVISION**. Two REQUIRED manuscript repairs are specified below: one coefficient-pairing inconsistency in the written Fisher proof, and the assignment-requested formal trust disclosure. Neither requires weakening the frozen target. I found no obstruction to the mathematical transfer after the explicit local convention repair below. This is a manuscript gate, not an acceptance, contribution reclassification, or result-count decision.

This is a fresh independent review after two provider failures that produced no manuscript verdict. I did not inherit the earlier proof PASS as a manuscript proof. I read the full 1293-line single-file source, inspected all 18 rendered pages, read the complete proof and contribution reviews and both attribution responses, and checked the relevant actual primary bodies. Only this new review directory and its scratch were written. No author/shared file was edited, no agent was spawned, and no browser, download, upload, publication, staging, or commit was used.

## Object, authentication, and exact retained scope

Reviewed package: `t298p-manuscript-r1`.

- External manuscript MANIFEST SHA256: `24a3e405e1bceda384a8b6a4e28f610809a4c9ec5b32b0a66e0277b24b2124fe`.
- Single-file source: `f08aec0f30e535dad576c9ca01c35575416c911ad9aebfaeca871c8eaaab22a6`.
- Delivered and independently rebuilt PDF: `6242cd7172404b4dfff15de10e06d00fe4484fddda7964983801bc971540bcb2`.
- Upstream pin: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

The author verifier/build/arithmetic/control code was read before execution or deciding not to execute it. The author verifier passes with the supplied external anchor, checks exact sealed membership and all 51 entries in its inputs.json, and makes no mathematical claim. The original r104 verifier also passes: 20 public payloads, 19 canonical Git blobs, and three primary PDF/text pairs. My separate authentication script checks all listed payload hashes under the eight supplied manifest anchors, all author-bound inputs, and three generator-preprint blobs against both their Git blob IDs and the complete pinned tree. The resulting binding has 171 files; authentication is distinct from actual reading. See `checks/input-authentication.json` and `reading-extents.md`.

The target remains exactly two bounded self-adjoint elements of a von Neumann algebra with faithful normal tracial state, with

`-infinity < chi(Z1,Z2) < chi*(Z1,Z2) < infinity`.

Chi is precisely the original operator-norm-cutoff, ordinary limsup over **all** output matrix sizes, with unnormalized Hilbert-Schmidt Lebesgue volume. The source-specialized stronger liminf transfer remains `gap(X)/k^2` at the fixed `k=2^32`, `n=k^2+1=2^64+1`. No matrix-unit conditioning, ultrafilter, restricted-size replacement, generation assertion, effective numerical epsilon, or general-transfer replacement has entered this review.

## REQUIRED R1: make the score pairing and coefficient product rule consistent

Location: page 11, Section 5.2, equation (31), source lines 773–787; also clarify the relation to equation (29), lines 752–757, and the adjoints in lines 820–829.

Equation (31) is the familiar **Hilbert-adjoint** formula. It is valid with that meaning. However, equation (29) expressly uses the bilinear conjugate pairing, giving `E_cb` rather than the Hilbert-adjoint `E_bc`; equation (31)'s following sentence says that its displayed convention is the conjugate pairing and that modifications would instead be needed for the sesquilinear convention. These conventions are reversed at this point. With the inner-leg insertion actually displayed in equation (30), the unconverted right side of (31) is not the bilinear score.

Here is an exact witness, entirely within the hypotheses used for coefficient insertion. Let `s,t` be centered free standard semicirculars, differentiate in `s`, and take `xi_s=s` relative to `t`. Put `u=t`, `v=1`, `P=ts`. The inserted derivative is

`delta(P) = t^2 tensor 1`, so `(tau tensor tau)(delta(P))=1`.

The right side printed in (31), paired as the score convention used in the paper, is `t s`; but

`tau((t s)P)=tau(t s t s)=0`.

The correct bilinear score here is `s t`, giving `tau(s t t s)=1`. This does not refute the conventional Hilbert-adjoint formula: the Hilbert-adjoint vector `t s` is paired using its adjoint. It demonstrates precisely why the conversion must be written.

An implementable repair that preserves (29), the target, and the leading constant is to define the bilinear coefficient score explicitly. If

`delta_uv(P) = sum_{P=P1 U_a P2} P1 u tensor v P2`,

define

`C_a(u,v) = v xi_a u - v (tau tensor id)(partial_a u) - (id tensor tau)(partial_a v) u`.

Then state and derive

`(tau tensor tau)(delta_uv(P)) = tau(C_a(u,v) P)`.

Apply the conjugate relation to `v P u` and the Leibniz rule to obtain this identity directly. For the matrix insertion in (30), its corresponding bilinear score is

`k^(-1) E_cb tensor C_a(u,v)`.

If retaining the conventional Hilbert formula as well, label it separately and write the flip/adjoint conversion; do not use the same star notation to mean both identities without explanation. Equivalently, define the bilinear score at `1 tensor 1` as the adjoint of the Hilbert-adjoint vector and state that convention throughout. Check the finite Neumann sums under the chosen convention, then pass to the series using the already supplied absolute coefficient and differentiated-coefficient bounds.

Why this is a local repair: the corrected score is bounded by `||u|| ||v|| ||xi_a||_2` plus the same two differentiated-coefficient bounds, in the appropriate reversed order. Summing gives exactly the existing projective-norm estimate. Constant leading coefficients give the same equation (33), including `Phi*(U)/(epsilon^2 k^4)`. Partial-trace bounds for inner derivatives, projection contraction, and the heat estimate are unchanged. The earlier proof-review diagnostic `checks/exact_adjoint.py`, which I read, actually uses this flipped bilinear formula, so its successful test did not verify the manuscript's unconverted convention. My independent `check_pairing.py` is written from the semicircular moment recursion, checks the witness, and verifies the corrected identity on 1519 monomial triples; 116 of those distinguish it from the unconverted printed expression. These finite checks support the identified convention error; the product-rule derivation supplies the repair for general polynomial coefficients.

This is a required correction to the precision of a central written identity, not a finding that the full unconditional estimate or the frozen target is false.

## REQUIRED R2: complete the stated formal coverage/trust boundary

Location: page 16, Appendix A, source lines 1197–1209; accompanying README's formal-scope paragraph.

The scope is already substantially accurate: four support declarations plus four controls, a column-Gram premise, assumed analytic increments and endpoint comparison, strict error absorption, and an explicit exclusion of the analytic theorem. However, the requested standard-axiom and cached-dependency trust boundary is absent from the manuscript/README summary. Also make explicit that the scalar entropy variables in Lean are finite real numbers. This is a disclosure completion under this review brief, not an analytic proof objection.

Add, for example, the following factual content in the Appendix, optionally linking to the companion coverage/provenance records:

“The scalar support statements quantify over finite real numbers, not extended-real entropy functions. The reported axiom dependencies are propext, Classical.choice, and Quot.sound. Reproduction builds fresh support/control oleans while trusting the installed Lean toolchain and pre-existing pinned dependency oleans; it does not rebuild the compiler or mathlib, and Git source cleanliness does not authenticate those cached binaries.”

The separate formal-review-r2 report is now authenticated and read: it reports 18 declarations and five expected rejected mutations, with no required scoped-support finding. I did not rerun Lean here. Its trusted-cache limitation is explicit and must not be erased when reporting formal support. The manuscript predates that review and says later outcomes do not enlarge coverage; that historical wording is accurate and is **not** a required repair, nor is the earlier OOM a mathematical objection. Updating the historical status after parent integration is optional.

## Independent mathematical audit of the rest of the complete proof

### Source and finite geometry

I checked source298's actual introduction/main theorem, conventions, full signal construction, and terminal proof conclusion. Its exact choice `p=2^64`, positive smoothing `h`, bounded models and finite gap agree with (1)–(2). The finite initial Fisher bound is the classical projected score of the added semicircular family. These stipulated inputs are used as supplied; I did not audit upstream truth.

For the chosen path adjacency and separated diagonal, the commutant is scalar. Thus the real orbit rank is `k^2-1`, the normal dimension is `k^2+1`, and the tensor-amplified linear chart fills the Hermitian pair space. Block extraction gives matrix-size-independent operator-norm inverse bounds as well as Hilbert-Schmidt bounds. The contraction construction can be performed in the absolute noncommutative majorant norm, and strict radius margins justify differentiated series.

The global tube proof reduces an almost-commuting transition unitary to the scalar stabilizer using off-diagonal block control, the path edges, and the polar part of the average diagonal block. The local injectivity argument then applies. Its coefficient-algebra version supplies the law identification required later. The manuscript correctly replaces the old triangular-shear phrase with the determinant ratio `|det(L+E)|/|det L|` in local bundle coordinates; the singular-value bounds give `exp(+-C epsilon d^2)`.

The orbit volume (15), stabilizer metric factor `k^(d^2/2)`, fiber Jacobian `(epsilon sqrt(k))^(n d^2)`, asymptotic (18), and shared constant (20) are consistent. Recombining them cancels the `log d` terms using `n+k^2-1=2k^2`, and leaves the single `log k` from output entropy normalization. The exact arithmetic runner was independently executed as finite support only.

### Matched volumes and all output sizes

The lower bound is an injective associated bundle over a conjugation-invariant source microstate set. Every subsequence realizing a source limsup remains as the output subsequence `kd`; this use is appropriate for a lower bound on the full output limsup.

For the upper bound, Lemma 4.3 is genuinely quantified over all sufficiently accurate output microstates with a fixed output cutoff. I checked its sequential proof and the final contradiction argument. The actual band projections have trace exactly `1/k` by norm-continuous unitary equivalence along the perturbation path, including nonfactor coefficient algebras. Bounded moment convergence transfers band ranks and truncated-polar moments. Pulling good domains to one root along finitely many tree paths gives exact matrix units with vanishing rank loss; no near-zero inverse or cycle-consistency assumption is used.

The explicit rank lemma handles the common-root intersections, which need not themselves be functional calculi. The second truncation uses positive `O(epsilon)` thresholds even for a zero limiting entry. There are at most `4k^2` Hermitian parts, fixed before dimension grows. Compression to the common good subspace bounds each compressed part without requiring its invariance. Hence the resulting pair is within the normal solver's norm radius, the recovered coefficients have a fixed cutoff independent of the output cutoff, and absolute series approximation transfers the source law. The coefficient-algebra uniqueness argument identifies that law up to common conjugation.

Projection nets cover arbitrary recovered corners without a measurable recovery map or uncontrolled source-set thickening. A nearby net projection is intertwined by a near-identity unitary; choose its mesh after fixing source slack. Orthogonal block measure decomposition has remaining real dimension `2(N^2-r^2)` with induced cross-block metric. The ball estimate (24), net cardinality (22), and rank sum produce the printed vanishing error (25). The leading size terms are exactly

`-r^2 log r -(N^2-r^2) log N + N^2 log N = r^2 log(N/r)`.

The missing `(r/N)^2` multiplier on the finite main bracket is harmless in the limit: it tends to one as theta tends to zero; bounded-source volume supplies a finite upper bound. The text keeps that multiplier implicitly until the limit. The all-large-`d` upper consequence of the source limsup applies to every retained `d >= (1-theta)N/k`. No residue class of output sizes is lost. The written order in lines 667–674 fixes epsilon/source accuracy/output cutoff, chooses mesh and output accuracy, takes `N` limsup, sends theta to zero, then source slack/accuracy to zero, and finally takes the output-cutoff supremum. The surviving error is independent of output cutoff. This establishes the required original-limsup upper bound, rather than just a multiples-of-k assertion.

### Fisher construction and exact noise path

Apart from R1's convention inconsistency, the coarse decomposition is substantive and correct. The central intertwiners `w_bc` have the stated matrix-unit orientation, the Gram matrix in (28) is `delta/k`, and the dimensions of `ran J` and the normal span add to `2k^4`. This is not inferred from the ordinary tangent dimension. Freeness promotes U-conjugates to relative conjugates; the ordinary adjoint-domain argument gives represented difference quotients. Inner-leg coefficient insertion preserves the outer bimodule Leibniz rule.

The unknowns `(epsilon c,eta)` make the generator-value map a fixed finite isomorphism plus `epsilon` times a bounded commutator perturbation. A projective-norm Neumann inverse and its differentiated series converge uniformly on the specified coefficient bounds. Undoing the scaling gives bounded remainder scores; R1's corrected product rule supplies the required same L2 estimate. The target derivations agree with the free difference quotients on Z-polynomials. With the pairing conversion made explicit, projection gives unconditional conjugates. Equation (33) includes the correct `epsilon^2 k^4` denominator and does not assume orthogonality of the source conjugates. The parent normalization clarification and the formal finite identity agree here; the proof-review prose omission was not copied.

The coefficient completeness identity in Section 6.1 gives a standard free semicircular pair using `2k^2` standard coefficients divided by k. Orthogonal normal/orbit rotation preserves their free law. At `t=epsilon^2 k^2 u` this yields exactly (34), with U free from T. The noise path needs neither upper Fisher semicontinuity nor a separate hidden X. Changing time turns the leading `k^-4` energy into `k^-2`; finite initial Fisher information bounds the error integral for each fixed upper source-noise time.

### Literal analytic theorem interface and final limit

I checked Shlyakhtenko's actual Theorem 4.1 statement and its preceding definitions. The paper explicitly uses its stated theorem, whose proof is omitted in the read v1. Section 6.2 supplies coefficients in the orbital algebra by grouping T-runs termwise, an absolute majorant with radius margins, both inverse-series identities by contraction, preservation of self-adjointness, and the logarithmic Jacobian estimate. The series representation may have many summands with the same U-word; its summable coefficient majorant controls them. No merely formal inverse substitutes for convergence. The conditioning algebra is embeddable and free from U. The direct semicircular conditioning-model argument explains preservation of source limsup subsequences. Proposition 2.8 plus projection, rather than the reader-left equality in Proposition 2.12, supplies the relative-to-unconditional inequality.

The lower volume bound at H and upper bound at X have the identical `C_D` and logarithmic epsilon term. Thus finite increment subtraction produces (41) with the correct source-gap sign. All entropies being subtracted are finite by the lower bounds, comparison, and covariance maximum. Proposition 4.2 is used with its embeddability hypothesis and its proof's `n/2` constant, not the displayed v1 typo. The covariance squeeze makes the noisy-source gap tend to zero. Matrix-size limits precede the epsilon limit; for each fixed upper source-noise time first send epsilon to zero, then send that noise time to infinity. The resulting source-specialized liminf and strictness quantifiers agree with the frozen r104 argument. The ambient tensor trace is faithful and normal, and the encoded tuple has exactly two bounded self-adjoint coordinates.

## Prior findings, attribution, scope, and rights

I tested `required-item-map.md` against the actual paper rather than treating the map as a resolution certificate.

1. Contribution R1: Sections 1, 3.1, 8.1 and equations (17)–(18) credit NSS Lemmas 2.6/2.8/2.9/2.10, the classical unitary volumes and Marinov. The claim is confined to unconditional Fisher U1, all-output-size matched upper volume U2, and their coupling U3. Uniform tube geometry is supporting analysis.
2. Contribution R2: Section 8.1 credits supplied-unit corner/compression/packing, states the dilated-ultrafilter equality, the one-sided ordinary-limsup statement and reader-left proof, and the intermediate direction typo. Section 8.2 correctly qualifies the relative degeneracy: ultrafilter microstates and relative nonmicrostates quantities are negative infinite, while the cited one-sided theorem does not determine the ordinary-limsup relative value. There is no proof by infinity subtraction.
3. Contribution R3: Section 2 and Sections 6–7 credit the Gaussian lower bound and its actual hypotheses/constant, covariance, chi<=chi*, relative projection, heat identity, and source298's two-scale template. The final scalar comparison is not claimed as a new operation.
4. Contribution R4: Section 8.3 accurately describes the pinned generator theorem, its classical 2-by-2 encoding credits, its entropy-dimension dependence corollary, and the companion's length-preserving coordinatewise transport. It draws no entropy invariance from generation or isomorphism.

All nine optional proof-review completions are actually present: historical exploratory status excluded from the theorem narrative; explicit rank perturbation and uniform recovery proofs; direct tube Jacobian; literal inverse-series hypotheses; correct projection inequality; Gaussian proof constant; fixed truncation multiplicity; and ineffective epsilon/no small witness. R1 above is a newly noticed inconsistency in the manuscript's expanded formula, not an attempt to reinterpret the old normalization typo.

The bounded literature screen is accurately disclosed. The optional Jung/orbital/dimension/mutual-information bodies remain unread in this review as well. The manuscript makes no negative claim about them and no worldwide-priority claim, so their unread status creates no new mandatory literature gate. I did not reclassify contribution or assert exhaustive duplicate clearance.

The author is Myeongjin Kang with no affiliation. Original paper/LaTeX/prose are CC BY 4.0 and original reproducibility Python code MIT. Third-party papers, software, fonts and earlier packets retain their rights. The source/PDF is standalone for reading and typesetting; private inputs are needed only to replay provenance authentication. These boundaries are candid and consistent across the Appendix and license files.

## Optional polish and visual/build evidence

- O1: page 6, equation (21), line 424: `\Gamma_{mathrm{out},kd}` renders a stray mathematical “mathrmout” subscript. Replace it with `\Gamma_{\mathrm{out},kd}` and define the shorthand as the prescribed output microstate neighborhood. Its intended meaning is clear from the surrounding paragraph, so this is not an analytic blocker.
- O2: the last reference page has only two entries and ample whitespace. This is legible and not a gate issue; a later layout pass could consolidate references if desired.
- O3: the historical “subsequently available” formal-review wording may be updated after parent integration, preserving the scoped coverage and cache caveat in R2. No analytic conclusion should depend on that workflow update.

I independently ran the inspected build.py with a fresh output wholly inside this review's scratch. Tectonic 0.17.0, executable hash `a98aa59ad5c1df39a6c9e56cbfc5088f2b11d6c179c0130b97998e4bd46a46da`, and SOURCE_DATE_EPOCH=1792281600 reproduced the delivered PDF byte for byte. The fresh log has no LaTeX warning, overfull/underfull hbox, or unresolved-reference warning. The complete source has no external section/bibliography include. This tests reproducibility, not mathematics; the TeX bundle remains an external dependency.

Poppler rendered all 18 frozen PDF pages at 115 dpi. I opened every page individually, in six groups of three, and inspected titles, abstract, statements, all displays, dense proof paragraphs, references, links, and page numbers. I observed no clipping, overlap, missing glyph box, or broken page transition. Equations (29), (31), and (33) were read in their rendered context. The notation typo O1 is visible on page 6; R1 is a mathematical convention problem visible on page 11. `checks/visual-review.json` records per-page PNG hashes and observations; the reproducible PNGs and fresh PDF are under excluded scratch.

The sealed verifier is read-only and requires an externally supplied manifest SHA256. It checks exact payload membership, safe paths, regular single-link files, lengths and hashes, and optionally rechecks all bound external inputs. Copied positive/negative controls test its integrity failure modes, not the mathematics. See README for replay commands. No analytic theorem, formal theorem, acceptance, or count is certified merely by the seal.
