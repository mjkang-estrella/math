# Consolidation of the p-gradient manuscript

2026-10-14 local date. Implementation and presentation consolidation only.
**The repaired four-text research argument has proof-gate PASS. This
consolidated manuscript awaits an independent manuscript verification gate.**
No acceptance, publication, priority certification or count credit is claimed.
The theorem retains every finite p>=3 and every original n>=2, with no sign,
critical-set, level-set or boundary restriction.

## Inputs and boundaries

I read `AGENTS.md`, the complete round-2 `review.md` and `source-map.md`,
and compared the manuscript with the four bound research texts: I345
`analysis.md`, the repair addendum, the compact-p `lemma.md`, and the
frozen appendix. The original I345 sections were compared to their
manuscript counterparts; the appendix retains its entire reviewed proof.
The seven-theorem vector Lean source and the parent formal README/receipt
were read. I did not perform another independent proof gate or literature
search. Primary-source reading boundaries are inherited explicitly from
`../p-gradient-proof-r2/source-map.md`, rather than expanded by this edit.

`inputs.json` records SHA-256 and byte lengths for those inputs and the
pre-edit manuscript hashes. `frozen-inputs-check.json` verifies that all
eight recorded review/proof/Lean inputs retain their original bytes.
In particular, `viscous-appendix.tex` remains
`1685cc94d4a0956debc413a063718b60be68074d4f2152ea167b9852f92c4e65`.
There were no edits outside the manuscript and this consolidation directory,
and no git, publishing, submission, or child-agent operations.

## P1–P8 dispositions

| Item | Manuscript disposition |
|---|---|
| P1 | Implemented. `compact-p.tex` replaces the former compressed interface with all structural, preliminary, perturbation, decay, critical-gradient and normalization steps from the bound lemma. The appendix plus the explicit I236 dependency paragraph replaces the old independent-revalidation description. Lemma 6.1 states the common Savin interface. Its application gives rho=min(1/8,b0²/30), lambda=b0²/6 and the **operator-norm** Lambda=3N. Lemma 4.1 states R4; Lemma 6.2 states R5 with its quantified scale and conclusion. |
| P2 | Parent-owned archive/commit task, outside this writer's permission. The four proof inputs remain SHA-bound; this report does not certify their archive or git status. |
| P3 | Implemented as an explicitly reviewable delta. The frozen appendix is preserved and compilation uses the typeset copy. `appendix-final.diff` records every difference. This delta is no longer described as typesetting only. It requires the pending manuscript gate. |
| P4 | Implemented in Appendix A.5: normalized locally uniform limits retain both G_tau=0 and FIT at every center/radius with the same C0; extract bounded fit coefficients separately for each center/radius, pass through strict margins, then use continuity. |
| P5 | Implemented in Appendix A.4: for m=1, constant extension of the weak linear solution and diag(B,1), verified by Fubini, permits three-dimensional Harnack followed by restriction. |
| P6 | Implemented in Appendix A.6: D²_xx W<=I/t gives the common 1/t_min spatial semiconcavity constant on each compact positive-time cylinder before invoking time regularity and contact. |
| P7 | Implemented in the manuscript only. The next reference is w_i+omega_tilde_i(0), projected onto the closed unit ball. The text states why the center estimate gives the t² gain and projection preserves the errors and drift. The reviewed uniformity lemma is unchanged. |
| P8 | Implemented in the manuscript only. It lists K*, (S+1)², 2^(2S+2), fixed cutoff factors, fixed-exponent Moser c(beta), c'(1), Sobolev and Poincare. The weighted Caccioppoli constant 4(P-1)² and normalization factors are explicit. No assertion that an arbitrary fixed-p constant is compactly bounded replaces the threshold argument. |

R4 was already a quantified lemma in the incoming manuscript; it was
checked against the addendum and retained. Its displayed selection now
says s_i tends to zero, rather than asserting monotonicity not supplied
by the approximate-supremum construction. A harmless clarification writes
the ordinary fit coefficient q as a-|p|²/2 to match the appendix convention.
The derivative-limit consequence now spells out the converging-slope and
unique-derivative steps from the reviewed original. It remains a consequence,
not an additional result.

## Claim and source map

| Manuscript passage | Reviewed mathematical source and operation retained |
|---|---|
| Theorem 1.1; Section 1 | I345 Section 1, overridden by addendum R3/R6/R7. Exact homogeneous n>=2, finite p>=3 claim; stipulated upstream revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Full inhomogeneous conjecture excluded. |
| Section 2, logarithmic bound and expanding domains | I345 Sections 2.1 and 2.3; Kotschwar–Ni Theorem 1.1 constants; weak/viscosity equivalence; fixed-p entire rigidity; pinned infinity lift and interior estimate. Critical gradients and original dimension two retained. |
| Lemma 2.1, `compact-p.tex` | Bound uniformity lemma Sections 1–5 plus its fixed-p Bernstein interface; Uhlenbeck Sections 1–5, especially (1.3)–(1.4), (4.1)–(4.15), (5.1), (5.4)–(5.5), and (6.1). Explicit common s interval, Taylor/inverse-power comparison, reference iteration, contraction/drift choices, decrease branch including zeros, Caccioppoli/Moser and constant dimension lift. P7/P8 are manuscript additions requested by review. |
| Section 3 | I345 Section 3: Schur-complement test construction with sigma perturbation, semidefinite comparison and sigma->0, both test signs and critical original gradients. |
| Section 4, Lemma 4.1 | I345 Section 4 plus addendum R4: goodness/beta definitions, approximate suprema, all scale separations, bounded-p exclusion, equal-parameter comparisons, equicontinuity, same-C0 inherited fits and nonaffinity. Pinned source-03 geometric interfaces only. |
| Section 5 | I345 Sections 5–6: exact on-test constraint, nonnegative continuous elliptic extension, one bounded contact for negative viscosity, transport identity, stability, projected PDE and fits with unchanged C0. Positive viscosity uses Appendix A; zero viscosity uses pinned source-04 Liouville. |
| Section 6, Lemmas 6.1–6.2 | I345 Section 7 plus addendum R2/R5 and r2 Section 3.1/3.3: Savin Proposition 4.1 varying-operator proof, quantified common jet radius/ellipticity/C2 data, amplitude rescaling for a proportional bound, inner ellipsoid, nonzero actual slope and Taylor estimate on reoriented fine cylinders. |
| Section 6 vector certificate | New `VectorEllipticity.lean` supplies the Gram inequality, square identity and lower certificate for arbitrary real inner product spaces. `physical_uniform_bounds` includes sqrt(e). This replaces the scalar coordinate split, preserving the same zero-jet constants. It is not part of the prior r2 formal audit; the parent separately compiled/audited the new source. |
| Section 7 | I345 Section 8: growing eta_i-good scales, unequal-parameter axial comparison, quadratic angular correction, equal-eta dyadic chain, A'_i/A_i->1 **before** coarse-parameter substitution, eta_i/e'_i->0, available ellipsoid scale and final contradiction. No stronger I344 norm comparison is used. |
| Section 8 | I345 Section 10: dyadic slope convergence, residual exponent gamma/(2+gamma), two-center derivative comparison, value-limit derivative identification and finite-difference consequence. |
| Section 9 and package scope | Addendum R6/R7; round-2 gate scope; contribution review boundaries; parent Lean build/axiom receipt. Exact support only, no PDE formalization or accepted-result claim. |
| Appendix A.1–A.4 | Frozen reviewed appendix and I236 Sections 2–5: locally uniform spatial slope/time regularity, cone infimum and contact recovery, full-gradient exponential flux, Alexandrov/sup-convolution/mollification/Fatou passage, gradient convergence, weak linear Dirichlet comparison, Harnack/trace/open-closed propagation. P5 makes the m=1 case explicit. |
| Appendix A.5–A.6 | Frozen reviewed appendix and I236 Section 6: invariant fitted frames and growth, affine-slice/reflection alternative, extremal Jensen configurations, moment/tail passage, equality in the envelope bound, synchronized-time theorem of sums and changed-PDE calculation, contact and global maximizer contradiction. P4/P6 make inherited class and semiconcavity explicit. |
| References and comparison paragraphs | Incoming manuscript references/contribution work retained. This consolidation makes no new literature-priority assessment. |

The source of record for positive viscosity is I236 `analytic-attempt.md`
Sections 1–6 (SHA a30077ca36f40e6613e340d3f8ae0ac692000f7b39d6eb4113897f40b7c68931),
with prior I239 review. The appendix includes the proof, rather than using
a review verdict as a mathematical theorem citation. Source-04 fit and
source-05 envelope operations remain stipulated geometric inputs; the
changed PDE operations are written in the manuscript.

## Exact appendix delta

`appendix-before.diff` preserves the pre-consolidation eight-line delta.
`appendix-final.diff` now has five groups of changes against frozen bytes:
(1) I236/I239 provenance and proof-of-record clarification; (2) `split` to
`aligned` in the ellipticity display; (3) the two-dimensional Harnack lift;
(4) PDE-plus-FIT closure with per-center/radius coefficient subsequences;
(5) the uniform positive-time-cylinder semiconcavity constant. No frozen
paragraph, analytic operation or theorem hypothesis was deleted. This
expanded copy remains subject to its own manuscript review.

## Reproduction and visual QA

The exact final command was run from the manuscript directory:

    /tmp/frontier-typeset/tectonic -X compile main.tex --outdir output/pdf --keep-logs

It exited 0 and produced a 21-page PDF. The final log has no TeX warning,
undefined reference/citation, missing-character, overfull or underfull-box
warning. All final pages were rendered at 110 dpi with Poppler; the six
contact sheets were inspected. The dense new/changed mathematics and
appendix additions were also inspected at full-page resolution on pages
3, 4, 5, 10, 11, 13, 14, 18, 19 and 20. No clipping, equation overlap, missing
symbols or unresolved references was observed. A formal-version hash
orphan at the page break was corrected and the final pages 13–14 rechecked.
This visual check is not an independent mathematical verification.

`main.txt` is the final extracted text; `pages/` contains the final renders.
`validation.json` in the manuscript binds the final sources, README/scope,
PDF, log and formal support receipt. `outputs.json` binds this report and
its supporting evidence. The frozen input check covers all eight inputs.
No separate new numeric test claims or new formal proof claims are made.

## Remaining review and publication work

The parent should commission the independent adversarial manuscript gate
on these frozen output hashes. Particular review targets are the P7
center-reference update and normalized excess conventions, the complete
compact-p translation and P8 factor inventory, the operator-norm Savin
constants and amplitude rescaling, the fresh vector source/receipt, and
all five appendix delta groups. Check all manuscript sections against the
four proof inputs using the map above; this report is an implementer's
comparison, not an independent gate verdict. I found no new mathematical
obstruction while consolidating, but do not upgrade the reviewed proof
PASS to manuscript PASS. Parent-owned P2 archival, final authorship/license,
matching MathDB scope and release assembly remain outside this task.
