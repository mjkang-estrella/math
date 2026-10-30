# Independent full T298P manuscript review, round 4

Verdict: **PASS_FULL_MANUSCRIPT_T298P**. Required findings: **none** (`required: []`). Both required round-3 manuscript repairs are resolved in the active r2 bytes. One new optional prose correction is recorded below. This is a full manuscript verdict under the stipulated source and named classical interfaces, with the entire frozen target retained. It is not acceptance, result-count credit, an enlarged formal verification claim, or exhaustive literature clearance.

## Reviewed object and independence

The active object is `t298p-manuscript-r2`, not historical r1:

- External manifest SHA256: `afc2c2ad6ecd45ef9958092c343e99b9d2804cb8f771a3d54cccae3e426393dc`.
- Complete main.tex SHA256: `499c2a2e6d14d70f47f39acde47c6404ce2101a91985998e363f9e1fe229b397`.
- Delivered and freshly reproduced PDF SHA256: `d460d6c916fd83b2f5a3a1554664ac335d6777d97a4787dec360cfd57171b740` (18 pages).
- Stipulated upstream revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

I read AGENTS, the full assignment and prior required findings, the full revised 1342-line source, its diff from r1, the complete r3 review/verdict/reading-extents/pairing checker, and the full proof/contribution reviews and attribution responses. I independently checked the actual proof, rather than treating either an author response or the prior proof PASS as a manuscript certificate. The r3 NEEDS_REVISION remains a correct historical verdict on its old object; this verdict binds only the revised object above. Provider failures supplied no mathematical verdict.

All writes were confined to this new review directory and its scratch. No author, prior review, shared or index file was edited; no agent was spawned, no browser or network was used, and nothing was staged, committed, uploaded or published.

## Exact retained target

Theorems 1.1 and 1.2 retain exactly two bounded self-adjoint elements in a von Neumann algebra with faithful normal tracial state, with

`-infinity < chi(Z1,Z2) < chi*(Z1,Z2) < infinity`.

Chi is the original operator-norm-cutoff microstates entropy, ordinary limsup over **all output sizes**, with unnormalized Hilbert-Schmidt Lebesgue volume. There is no replacement by conditioning on matrix units, an ultrafilter, a multiples-of-k limit, a different entropy, or extra output coordinates. The source-specialized stronger assertion is still

`liminf_(epsilon down to 0) gap(E_epsilon(X)) >= gap(X)/k^2`,

at fixed `k=2^32`, `n=k^2+1=2^64+1`. No generation claim, effective numerical epsilon, small witness, or uniformity in k was introduced.

## Resolution of round-3 required R1

**Resolved.** The revised Section 5.2, pages 10-11, explicitly distinguishes the bilinear score from the Hilbert-adjoint vector. Equations (29)-(32), with labels `eq:entry-adjoint`, `eq:insertion`, `eq:adjoint-product`, and `eq:bilinear-pairing`, now use a consistent convention.

For the declared Hilbert inner product `<x,y>=tau(x* y)`,

`<delta_H*(1 tensor 1),P> = tau((delta_H*(1 tensor 1))* P)`.

Thus the bilinear score is exactly `b(delta)=(delta_H*(1 tensor 1))*`. No unconverted conventional product rule is identified with that score.

Here is the general polynomial check, independent of the finite diagnostics. Write `partial_a u=sum l tensor r` and `partial_a v=sum f tensor g`. Applying the conjugate relation to **u P v** gives three Leibniz terms. Their trace contractions are respectively

1. `sum tau(l) tau(r P v) = tau(v (tau tensor id)(partial_a u) P)`;
2. `sum_(P=P1 U_a P2) tau(u P1) tau(P2 v) = sum tau(P1 u) tau(v P2)`;
3. `sum tau(u P f) tau(g) = tau((id tensor tau)(partial_a v) u P)`.

The left side is `tau(xi_a u P v)=tau(v xi_a u P)`. Subtracting the first and third terms yields, for every polynomial P and polynomial u,v,

`C_a(u,v)=v xi_a u-v(tau tensor id)(partial_a u)-(id tensor tau)(partial_a v)u`,

`tau(C_a(u,v)P)=(tau tensor tau)(delta_uv(P))`.

This proves the displayed identity for the actual inner-leg insertion. The author's choice of **uPv** is correct. The r3 review's explanatory **vPu** sentence (also repeated in its repair field) is an order typo; copying it would not derive the displayed corrected C. The r2 manuscript does not copy that typo.

For `E_ij tensor P`, direct matrix-unit multiplication in (30) gives `delta_ib delta_jc/k^2` times the scalar inserted contraction. Pairing `k^-1 E_cb tensor C_a(u,v)` against that matrix polynomial gives exactly the same factor. The Hilbert vector is its adjoint, `k^-1 E_bc tensor C_a(u,v)*`. This verifies both orientation and normalization, including off-diagonal tests. The old witness u=t, v=1, P=ts gives actual contraction 1 and revised score 1; the old unconverted bilinear expression gives 0.

The L2 estimate in Section 5.2 is valid: bounded left/right multiplication controls `v xi_a u`; the two partial traces are contractions from the projective norm to the operator norm. Reversing the factors has not changed the coefficient or differentiated-coefficient majorants. The inner derivation has score equal to the difference of its partial traces and norm at most `2||eta||_pi`.

### Neumann limit, domain and unconditional projection

Section 5.3, page 12, now gives the needed passage explicitly. Each finite Neumann sum has polynomial coefficients, so the preceding polynomial pairing applies to it. The inverse is formed in the sum projective norm of the finitely many coefficient arrays. Its nonconstant coefficient and differentiated-coefficient series are absolutely convergent, with derivative majorant `sum_(ell>=1) ell epsilon (epsilon K H_R)^(ell-1)=O(epsilon)`. Undoing the normal scaling leaves an O(1) score remainder, not an extra epsilon inverse.

The base difference quotients are well defined on the represented algebra by relative conjugates and the elementary-tensor adjoint test. Inner-leg insertion is a bounded operation on the evaluated projective tensors and preserves the outer bimodule Leibniz rule. For any fixed polynomial, its finite-sum derivatives therefore converge, while the finite-sum scores are Cauchy in L2. Trace passage is legitimate: `|tau((b_m-b)P)| <= ||b_m-b||_2 ||P||_2`, and trace contraction is continuous on the converging derivative tensors. The limit has the stated bilinear score, hence the corresponding Hilbert adjoint at 1 tensor 1. A bare operator-norm inverse without differentiated control would not establish this; the manuscript supplies the stronger control.

The limiting derivation has `delta_j(Z_s)=delta_js 1 tensor 1`, so its polynomial restriction is the free difference quotient in Z. Conditional expectation onto W*(Z), extended to L2, preserves `tau(bP)` for every Z-polynomial P and contracts the norm. It is the bilinear score, with the specified conversion, that is projected. This yields unconditional conjugates; no scalar-matrix conditioning has been discarded.

The normal projection coefficient is `(V_aj)_cb/k`; together with (29) this gives current equation (34), `Xi_j^0=(epsilon k^2)^-1 sum_a V_aj tensor xi_a`. Summing its squared norms uses `sum_j tr_k(V_aj V_ej)=delta_ae`, with no orthogonality premise on the conjugates. The leading energy is precisely `Phi*(U)/(epsilon^2 k^4)`. The bounded remainder and its cross term give Proposition 5.1 as printed. This also avoids the prefactor omission in one historical proof-review prose equality.

My new `check_revised_score.py` independently checks 14,175 exact scalar/Hilbert pairings and 71,295 matrix pairings, including four negative controls. The original r3 diagnostic was also replayed separately and is credited as copied code. These are finite diagnostics only. The general proof and analytic limit justification above, not the counts, resolve R1.

## Resolution of round-3 required R2

**Resolved.** Appendix A, page 17, and the README explicitly state all requested boundaries: finite real scalar variables rather than extended-real entropy functions; reported `propext`, `Classical.choice`, and `Quot.sound` dependencies; fresh support/control oleans; trust in the installed Lean toolchain and pre-existing pinned dependency oleans; no compiler or mathlib bootstrap; and no authentication of cached binaries from Git source cleanliness.

I read the actual T298P.lean/Controls.lean, coverage, and complete independent formal-review-r2 report. The four support statements assume the full column Gram premise or the analytic increments and endpoint comparison; four controls test scalar failure modes. Ten reviewer examples and five expected rejected mutations are reported by that independent formal review. I authenticated that packet but did **not** execute Lean anew in this manuscript review. No declaration formalizes conjugate-variable domains, microstate recovery, inverse series, entropy limits, the source theorem, or the analytic theorem here. The revised disclosure is accurate and does not enlarge the formal coverage.

## Full proof audit beyond the repairs

### Source, tube and matched volumes

I checked the actual source298 main theorem and construction interfaces: p=2^64, n=p+1, positive h smoothing, bounded models, finite gap, the entropy convention, and heat equation. Initial Fisher information is bounded by n/h using the projected semicircular score. These are stipulated inputs, not an upstream truth audit.

The diagonal/path pair has scalar commutant, ordinary orbit rank k^2-1 and normal dimension k^2+1. The scalar coefficient inverse tensors to every matrix size; block extraction gives operator-norm bounds independent of that size. The contraction and its absolute majorant supply a radius margin and differentiated series. Almost commutation with D1 controls off-diagonal unitary blocks; path edges compare diagonal blocks; the polar part of their average reduces a global transition to the local chart. The same argument over the actual coefficient algebra identifies recovered source laws.

The bundle Jacobian is the written determinant ratio of L+E to L, with Hilbert-Schmidt relative error O(epsilon) in real dimension 2k^2 d^2. This is valid pointwise in bundle coordinates. Orbit volume, stabilizer metric factor k^(d^2/2), normal Jacobian `(epsilon sqrt(k))^(n d^2)`, and Stirling normalization give the shared C_D. The log d terms cancel because n+k^2-1=2k^2. The single remaining log k is the output entropy normalization. The lower bundle over a conjugation-invariant source microstate set retains every source limsup subsequence as sizes kd; this is sufficient for the lower bound on the full output limsup.

The upper bound genuinely addresses every N. The actual spectral bands have trace exactly 1/k by norm-continuous equivalence along the perturbation path, without a factor assumption. Moment convergence controls matrix band ranks and bounded truncated-polar operations. Pulling good domains to one root along the finite tree loses o(N) rank and yields exact matrix units. The rank lemma applies to common-root intersections even though they are not themselves functional calculi. The second truncation uses positive O(epsilon) thresholds, including zero limiting entries, for at most 4k^2 Hermitian parts fixed before N grows. Compression bounds each part without an invariance requirement. The inverse then has a recovered cutoff independent of output cutoff, and uniform series approximation recovers the source law. The final contradiction argument supplies the quantified uniform lemma over all sufficiently accurate microstates.

Projection nets cover the possible corners; nearby projections are carried by a near-identity unitary. Thus no measurable recovery map or uncontrolled volume of a thickened source set is needed. Orthogonal block decomposition gives remaining real dimension 2(N^2-r^2), including the induced cross-block metric. The main logarithms are exactly `-r^2 log r-(N^2-r^2)log N+N^2 log N=r^2 log(N/r)`; the net and remaining-ball costs vanish with theta. The finite main bracket has the multiplier `(r/N)^2` until the limit; it tends to one. Finite upper bounds on source volumes justify this passage, including arbitrarily negative finite bounds if a source limsup is -infinity.

For fixed epsilon, source accuracy and output cutoff, choose net mesh for source slack, then output accuracy for theta; take the N limsup, theta down to zero, source slack/tolerance down to zero and moment order up to infinity, then the output-cutoff supremum. Each retained d is at least `(1-theta)N/k`, so the source-limsup upper bound applies at every such large d. No output residue class is dropped. The final error is independent of the output cutoff. This establishes the original all-size upper bound with the same C_D.

### Noise, analytic theorem interface and final limits

The coarse decomposition has the stated Gram delta/k and dimensions summing to 2k^4; it is not deduced from the ordinary tangent dimension. The corrected score argument above completes the unconditional Fisher estimate on the exact noisy path. The Hermitian-basis completeness identity makes the coefficient semicircular construction with 1/k scaling a standard pair free from the ambient algebra. Orthogonal normal/orbit rotation gives the exact law at `t=epsilon^2 k^2 u`, with U free from T. The leading k^-4 energy therefore integrates to k^-2; finite initial source Fisher information makes the remainder integrable for each fixed upper source-noise time. No upper Fisher semicontinuity is used.

I checked Shlyakhtenko's actual series definitions and Theorem 4.1 statement. The manuscript provides the B=alg(T) coefficient representation by grouping T-runs, summable coefficient majorants, both inverse identities from contraction, strict common radius margins beyond the evaluated norms, self-adjointness of F and G, and Jacobian I+O(epsilon). These meet the printed hypotheses. The v1 proof is omitted; the published theorem is an explicit dependency, and no absent proof is claimed as read.

Theorem 2.19 applies to U free from the embeddable orbital semicircular algebra. Its all-large-size models and the averaging argument preserve source limsup subsequences. Proposition 2.8 and projection of joint microstate sets give the required relative-to-unconditional inequality, without relying on Proposition 2.12's reader-left equality. Proposition 4.2 is applied with embeddability and its proof's n/2 Gaussian constant, with the printed n typo disclosed.

The lower bound at H and upper bound at X have identical C_D and log-epsilon term. Their cancellation and the unconditional Fisher increment give current equation (42) with the correct source-gap sign. All subtracted entropies are finite by the lower bounds, chi<=chi*, and covariance upper bound. Gaussian smoothing and covariance squeeze the large-noise source gap to zero. First fix the upper noise time and send epsilon to zero; only then send that noise time to infinity. Matrix-size limits occur earlier. Strictness follows for every sufficiently small positive epsilon. The tensor trace is faithful normal and the two coordinates bounded self-adjoint. No weakened theorem was needed.

## Earlier contribution and proof items in the actual manuscript

All four contribution corrections remain implemented: (1) NSS Lemmas 2.6/2.8/2.9/2.10, unitary volumes and Marinov are credited and claims confined to U1/U2/U3; (2) Shlyakhtenko's supplied-unit corner/compression/packing, dilated-ultrafilter equality, one-sided ordinary-limsup result, reader-left proof and intermediate direction typo are stated accurately; ordinary-limsup relative degeneracy is not inferred from a lower bound of -infinity; (3) embeddability, the Gaussian proof constant, covariance, comparison, relative projection, heat identity and source two-scale template are credited; (4) the pinned generator preprint's generation-only 2-by-2 encoding and entropy-generator dependence, and the companion's length-preserving transport, are accurately described. I checked these against the actual operative bodies.

All nine earlier optional proof completions are present: historical exploratory status confined to provenance; explicit rank estimate; quantified recovery; direct Jacobian calculation; literal inverse-series hypotheses; correct projection inequality; Gaussian proof constant; fixed truncation multiplicity; and ineffective epsilon/no small witness. No mandatory contribution issue remains under the supplied bounded-screen contract. Optional unread literature leads do not alone create a new mandatory gate.

## Optional finding and disposition of earlier optional items

**O4, optional prose only:** page 6, Section 4.1, main.tex lines 422-425: the inserted shorthand definition splices into the sentence as “Lemma ... and ... give Here ...”. Move the “Here Gamma_out ...” definition before that sentence, or place it after equation (21), so “give” leads directly to the display. This does not change the definition, estimate, or proof.

Old O1's malformed subscript is fixed and the shorthand is defined. Old O2's sparse reference ending has naturally reflowed: all twelve entries fit legibly on page 18. Old O3's formal status wording is updated in the manuscript. None remains required. New required findings: **none**.

## Reproduction, presentation, rights and limits

The inspected author verifier passes: exact 26 sealed payloads and all 57 bound input entries. The inspected r104 verifier passes: 20 public payloads, 19 canonical blobs and three primary PDF/text pairs. The adapted audit authenticates ten externally supplied packet anchors, all their listed payloads, and 217 bound files, including generator Git-blob/tree membership. These are byte checks, not proof. Ten copied author integrity controls pass, run wholly inside this review's scratch.

A fresh inspected build reproduced the PDF byte for byte with Tectonic 0.17.0, executable SHA256 `a98aa59ad5c1df39a6c9e56cbfc5088f2b11d6c179c0130b97998e4bd46a46da`, SOURCE_DATE_EPOCH=1792281600, and no LaTeX warnings, overfull/underfull hboxes or unresolved references. The complete source needs no external manuscript section or bibliography include. The TeX bundle remains an external build dependency.

I rendered all 18 pages at 115 dpi and opened every page individually, including revised pages 11, 12 and 17. No clipping, overlap, missing glyphs or broken page transition was observed. The score equations and trust disclosure are legible in their rendered context. Per-page PNG hashes and observations are in checks/visual-review.json; reproducible renders and build products are excluded scratch.

The author is Myeongjin Kang, with no affiliation. Original manuscript material is CC BY 4.0 and original reproducibility code MIT; third-party papers, software, fonts and prior packet materials retain their own rights. The standalone source/PDF can be read and built without private provenance copies; those copies are needed to replay local input authentication. The manuscript makes no worldwide-priority or exhaustive-rights-clearance assertion.

The bounded literature screen remains explicit. Jung math/0410594, Shlyakhtenko 2201.09503, HMU math/0702745, Ueda 1210.6421/1610.04118, Izumi-Ueda 1306.5372 and the Connes-Shlyakhtenko orbital/dimension/mutual-information bodies were not newly screened here. No negative theorem assertion about them supports this verdict. No exhaustive novelty certification, new contribution classification, acceptance or count decision is made. Reading-extents.md distinguishes actual reads, authenticated files, classical assumptions, and reported formal evidence.

The review's external manifest seal and read-only verifier authenticate this review packet and, optionally, its bound input hashes. Copied verifier controls test integrity failure modes only. They do not certify the infinite-dimensional analytic theorem merely by passing.
