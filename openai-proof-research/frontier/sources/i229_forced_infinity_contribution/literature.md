# I229 — primary-source comparison and reading record

This record supports the independent contribution gate, not a worldwide-priority claim. All OpenAI theorems and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. Source files were read to identify their actual hypotheses and reusable contracts, not to audit them. No I228 or other active review was read.

## Pinned primary source, reused in place

Base path: `frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/`.

Completely read: README.md; build/manuscript/main.tex; build/references/bibliography.tex; build/manuscript/sections/01-introduction.tex, 02-flatness.tex and 03-reduction.tex. The original proof's later sections 04–08 were not read for this gate. Their results remain stipulated.

[Main theorem](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/01-introduction.tex): `thm:main`, exact infinity-harmonic functions, every d≥3, uniform C^{1,alpha_d}, alpha_d∈(0,1/3], no boundary or endpoint claim.

[Flatness operations](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/02-flatness.tex): `lem:linear-lift`, `lem:cone-slopes`, `prop:affine-blowups`, `lem:sum-rule`, `prop:three-point`. The last proposition assumes exact infinity harmonicity; its proof supplies the bounded contact gradients and divergent negative penalty Hessian used by I224.

[Reduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/03-reduction.tex): `thm:liouville`, `lem:family-flatness`, `lem:bad-scales`, `lem:cylinder-comparison`, `prop:nonaffine-limit`, `prop:power-decay`. The Liouville statement requires exact homogeneous limiting PDE and all-center/all-radius shear fits. Cylinder comparison is explicitly geometric. The reduction already provides the compactness, nonaffinity and slope extraction mechanisms.

The family-377 portion of sources/CONTENTS.md and matching entries of the complete sources/preprints-tree.json were inspected. Only one manuscript appears for this family. No claim was made from the truncated sources/tree.json, which was not used.

## Lindgren: manuscript content accessible; original PDF not authenticated

Erik Lindgren, *On the regularity of solutions of the inhomogeneous infinity Laplace equation*, Proc. AMS 142 (2014), 277–288, [DOI](https://doi.org/10.1090/S0002-9939-2013-12180-5).

The [author's publication page](https://sites.google.com/view/eriklindgren) was consulted; its entry links `https://staff.math.su.se/erik.lindgren/diff.pdf`. That file returned 404. AMS's journal and shorter proc PDF paths returned 403. Attempts at an archived author URL, plausible author-host migrations, and the PDF linked from the accessible mirror did not yield an authenticated PDF. No failed PDF was retained, and no arXiv identifier is invented.

An accessible [transcription of the primary manuscript](https://doczz.net/doc/7566335/on-the-regularity-of-solutions-of-the) was read. Retained [web lines 8–329](lindgren-manuscript-web-lines-8-329.txt) are fully read and correspond to manuscript pages 1–5: abstract, introduction, exact Theorems 1–2, preliminaries/fundamental assumptions, and Section 3 through the proof of Theorem 1. Web lines 330–508 were additionally displayed/read for the C¹-forcing regularization discussion and opening of Lemma 3's proof; not retained or used to claim a full-paper reading.

Theorems 1–2 concern the **unnormalized** equation Δ∞u=f, with bounded continuous f for affine subsequential blow-ups and C¹∩L∞ forcing for differentiability. There is no planar restriction or sign assumption in those theorem statements; Section 2.1 explains its dimensional lift to obtain nonzero slopes and signed forcing. Section 3 contains the almost-monotonicity and homogeneous blow-up mechanism. It does not give R's arbitrary normalized-forcing uniform gradient Hölder estimate.

The transcription has malformed formulas (notably Definition 1 appears to omit the forcing). This is not an authenticated author or publisher copy, and no convention or delicate proof claim rests on that damaged formula. The cited theorem statements and equation are legible and agree with the discussion in Crasta–Fragalà. This is an explicit retrieval/provenance limitation.

## Crasta–Fragalà

G. Crasta and I. Fragalà, *A C¹ regularity result for the inhomogeneous normalized infinity Laplacian*, [arXiv:1506.05305v1](https://arxiv.org/abs/1506.05305v1), Proc. AMS 144 (2016), 2547–2558.

Reused and fully read `frontier/sources/i224_infinity_gradient_stability/crasta-fragala-1506.05305v1-pages-1-3.txt`. Newly retained and fully read [PDF pages 9–10](crasta-fragala-1506.05305v1-pages-9-10.txt), which include all Section 4 and the preceding end of Section 3. Section 4 was also checked against [arXiv HTML](https://arxiv.org/html/1506.05305v1#S4).

Definition 1 gives −lambda_max at upper zero-gradient tests and −lambda_min at lower zero-gradient tests. The main normalized problem has constant source +1 and zero boundary data on a bounded convex domain in any R^N. Power concavity supplies local semiconcavity and C¹. Theorem 16 retains a semiconcavity assumption for its more general statement. Its displayed Δ∞ notation and the proof's Δ∞^+ notation differ; neither provides a basis for discarding semiconcavity or claiming arbitrary-forcing C^{1,alpha}. The normalized-versus-unnormalized distinction is explicit in the introduction.

## Lu–Wang

G. Lu and P. Wang, *A PDE Perspective of the Normalized Infinity Laplacian*, Comm. PDE 33 (2008), 1788–1817, [author-hosted PDF](https://www2.math.uconn.edu/~guozhenlu/papers/cpde_lu_wang_published.pdf), [DOI](https://doi.org/10.1080/03605300802289253).

Reused the I224 selected-pages extract, fully read PDF pages 8, 9, 11, 12, 13, 24, 25, 29, 30. Newly retained and fully read [page 23](lu-wang-2008-page-23.txt) to check the exact Theorem 5.3 hypotheses. The source PDF's broken font encoding is retained; normalized critical-gradient conventions were checked against the readable Crasta–Fragalà definition, not guessed from damaged glyphs.

Theorems 1.7/2.2/2.4 characterize solutions by polar-quadratic comparison for continuous forcing in arbitrary dimension. Theorem 5.3 is value stability around f bounded away from zero with one sign. Theorems 1.9/5.4 treat uniformly vanishing forcing and give uniform value convergence; the limiting boundary datum is in their Lipschitz class. They do not give uniform gradient Hölder bounds for the whole forced class. The small forcing sequence in the zero-forcing stability result need not have a fixed sign.

## Perturbation principles: exact applicability boundary

C. Imbert and L. Silvestre, *C^{1,alpha} regularity of solutions of degenerate fully non-linear elliptic equations*, [arXiv:1201.3739v1](https://arxiv.org/abs/1201.3739).

Fully read retained [PDF pages 1–5 and 10–11](imbert-silvestre-1201.3739v1-pages-1-5-10-11.txt) and [page 6](imbert-silvestre-1201.3739v1-page-6.txt). These give Theorem 1, the uniform ellipticity definition, homogeneous estimate, amplitude reduction, full shifted improvement-of-flatness statement/iteration, and its compactness proof/removability lemma. The intervening equicontinuity proof on pages 7–9 was not read.

Theorem 1 assumes |Du|^gamma F(D²u)=f, gamma≥0, uniformly elliptic F, F(0)=0, bounded f. Lemma 2 is uniform in every affine shift p. This demonstrates the established perturbative framework; it does not apply directly to the rank-one directional infinity operator. The candidate's use of the stronger pinned anisotropic operations is essential to any claim of automatic transfer. No p-uniform estimate or p→∞ passage is inferred.

## October 2026 qualitative-to-quantitative paper

A. Sobral, E. V. Teixeira and J. M. Urbano, *Qualitative-to-quantitative regularity for degenerate equations*, [arXiv:2610.13137v1](https://arxiv.org/abs/2610.13137v1), October 9, 2026.

Reused and fully read I224's PDF pages 1–4; newly retained and fully read [PDF pages 9–13](sobral-teixeira-urbano-2610.13137v1-pages-9-13.txt). The latter include the end of the p-harmonic argument, exponent comparison, and the entire Section 3. The [HTML Section 3](https://arxiv.org/html/2610.13137v1#S3) was checked as well.

Theorem 1.1 fixes p>2; its constants depend on p. Theorem 1.3 is for homogeneous planar infinity-harmonic functions and every beta<1/3. Section 3 uses homogeneous C¹ compactness and a separate near-affine theorem, and explicitly identifies the rank-one obstruction for unbounded affine shifts. Theorem 1.4 concerns a nonlocal equation with tail and differentiability hypotheses. None states R; a generic qualitative-to-quantitative slogan cannot bypass these contracts.

## Scope and conclusion

The complete supplied I224 brief, report, analytic proof and literature note were read. The source comparison judges the final bounded-error three-point argument and the explicit r_i/lambda_i selection, not an earlier incomplete version. The contribution verdict is the reviewer's inference: a useful new solution-class consequence, but a technical robustness extension of the stipulated proof package rather than a tenth nonroutine finding. No primary source found was claimed to contain R verbatim. All retained excerpts are read in full; complete PDFs used for extraction were not retained. SHA-256 values and exact scopes are in the I229 authentication manifest.
