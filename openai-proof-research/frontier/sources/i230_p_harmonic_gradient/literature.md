# I230 — primary literature and exact source contracts

All pinned OpenAI results and lower operations are stipulated. New-to-project does not imply new-to-literature. The positive convex-ring rate is classified as a technical quantitative refinement; the unrestricted result is unpaid.

## Pinned source

[OpenAI, Uniform Interior C¹,α Estimates for Infinity-Harmonic Functions, introduction at the immutable revision](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/01-introduction.tex): thm:main supplies dimension-only alpha_n>0 and interior norms for exact infinity-harmonic functions, n>=3. Complete introduction read in the reused corpus.

[02-flatness.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/02-flatness.tex): complete section read; its affine lift and three-point statement have exact infinity-harmonic hypotheses. No p-equation invariance is present.

[03-reduction.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/03-reduction.tex): complete section read with overlap after truncation. thm:liouville requires D²V[(D_xV,1)]=0 and one C0 for affine fits at every center and radius on |l|<=R, |h-p l|<=R. lem:cylinder-comparison is equation-independent but requires nonzero slopes with upper/lower norm bounds; prop:nonaffine-limit also contains a separate PDE passage. None asserts the corresponding finite-transverse-viscosity rigidity. The family-377 catalogue/path lookup found one matching manuscript, not a p-viscosity companion. No wider semantic search of all pinned manuscripts is claimed.

## Actual p-to-infinity value rates

[Leon Bungert, The convergence rate of p-harmonic to infinity-harmonic functions, arXiv:2302.08462v2](https://arxiv.org/abs/2302.08462v2), published CPDE 48 (2023), 1323–1339. Reused frontier/sources/i140_nonlinear_elliptic_discovery/external/bungert.txt, lines 1–310. Definition 2.1 specifies the variational solution. Theorem 1 assumes H=limsup [u_p]_{C^{0,alpha_p}}<infinity, alpha_p in [1-n/p,1], and gives value rates O(p^{-1/4}); the O(p^{-1/2}) improvement requires ess inf on the entire domain of |Du_infinity|>0. Remark 2.5 verifies H for uniformly controlled boundary extensions. These are not actual-gradient rates.

## Fixed-p regularity is not p-uniform regularity

[Sobral–Teixeira–Urbano, Qualitative-to-quantitative regularity for degenerate equations, arXiv:2610.13137v1](https://arxiv.org/abs/2610.13137v1). Reused and completely read PDF excerpts pages 1–4 and 9–13, stored under I224 and I229. Theorem 1.1 has C(n,p,gamma,beta), and the shifted large-slope matrix I+(p-2)e tensor e still has ratio p-1. Theorem 1.3 concerns exact planar infinity-harmonic functions. Its small-gradient/near-affine split does not handle all changing-p anisotropic regimes here.

## Convex-ring gradient convergence: relevant existing positive theorem

[Lindgren–Lindqvist, The Gradient Flow of Infinity-Harmonic Potentials, arXiv:2006.15328v1](https://arxiv.org/abs/2006.15328v1), later Adv. Math. 378 (2021), 107526. Retained and completely read [pages 1–3](lindgren-lindqvist-pages-1-3.txt), [pages 7–8](lindgren-lindqvist-pages-7-8.txt), [pages 9–11](lindgren-lindqvist-pages-9-11.txt), [page 12](lindgren-lindqvist-page-12.txt), and [pages 24–28](lindgren-lindqvist-pages-24-28.txt). Planar convex ring, boundary values 0 and 1. Theorem 7 controls the magnitude |Du_p| locally uniformly; page 12 distinguishes the then-unresolved full-vector convergence. The appendix supplies a planar p-adaptation of Sobolev/flatness estimates, not a general-dimensional uniform C¹ theorem. Source PDF SHA-256 before removal: 8587786c3778af716c6ea2f49b96244aef421ab0424f86aa7b46e8d3a6279815.

[Peng–Zhang–Zhou, Regularity from p-harmonic potentials to infinity-harmonic potentials in convex rings, arXiv:2310.08093v4](https://arxiv.org/abs/2310.08093v4), [published identification, Proc. London Math. Soc. 130 (2025), e70062](https://doi.org/10.1112/plms.70062). Retained and completely read [pages 1–8](peng-zhang-zhou-pages-1-8.txt), [pages 14–17](peng-zhang-zhou-pages-14-17.txt), and [pages 18–23](peng-zhang-zhou-pages-18-23.txt). Theorem 1.1 proves full local C¹ convergence in arbitrary-dimensional convex rings and nonvanishing of the infinity-potential gradient. Lemma 3.1 records smoothness, noncriticality and quasiconcavity of the p-potentials; Lemmas 4.2–4.4 give one-sided normal slopes and uniform interior gradient bounds. Lemma 5.2 explicitly proves convergence of normals and magnitudes. Its normal/slope method is close to the restricted I230 rate argument, which therefore is not nominated as independently substantial. Original Lewis 1977 is cited there but was not independently read. Source PDF SHA-256 before removal: 7d46e64b156a7ec747bc787468bb2962f05841fe869f0dafb1f45e2835f9b0ba.

## Conditional viscous rigidity input

[Dongsheng Li–Kai Zhang, A note on the Harnack inequality for elliptic equations in divergence form, arXiv:1901.06128v1](https://arxiv.org/abs/1901.06128v1). The entire three-page manuscript was retained and read: [pages 1–3](harnack-pages-1-3.txt). Theorem 1.1 applies to nonnegative weak solutions of div(A Dw)=0 on Q6 with uniform positive ellipticity constants, and the Harnack constant depends only on dimension and those constants. Used for derivatives of the finite-viscosity exponential Euler equation only after imposing a global full-gradient bound, which supplies the required global coefficient bounds. That additional hypothesis is not inherited from the pinned affine fits. Source PDF SHA-256 before removal: 2f656fca2bec1b7ab44021e507a31a6d01c2e4f1d722da4436e14fbf91309edf.

## Limits

All new retained source files above are text excerpts read completely. Omitted pages, later revisions, and the originals cited by these papers are not represented as read. No source discovered here closes the unrestricted actual-gradient rate. The scale calculations and the new restricted quantitative proof are fully recorded in the analytic note; the existence of that proof does not establish worldwide priority or an accepted contribution.
