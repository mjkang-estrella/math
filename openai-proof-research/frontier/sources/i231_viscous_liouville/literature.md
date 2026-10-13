# I231 — primary literature and exact source interfaces

This is a bounded source comparison, not a worldwide novelty determination. Existing pinned manuscript copies were reused; newly retained files are only page excerpts actually read in full. No whole unread PDFs were saved.

## Pinned manuscript

[OpenAI, Uniform Interior C¹,α Estimates for Infinity-Harmonic Functions, pinned source directory](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections).

The immutable revision is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Source 03, thm:liouville, assumes exactly F[V]=D²V[(DxV,1)]=0 and the all-center/all-radius sheared affine fits. It does not cover F[V]+tau Delta_x V=0. Source 04, lem:frame-invariance and the geometric portion of lem:fit-compactness, retain their contracts after the new trace is explicitly checked. Source 05, lem:barycentric-envelope, is geometric; lem:common-time-subsolution and cor:barycentric-subsolution require the additional common spatial translation directions proved in this task. Source 04's quadratic-envelope and slope operations do not transfer unchanged. Source 06's exact drift identity remains algebraic, but its inequalities lose a fixed amount per step. Source 07's finite-slope/stopped-expectation assumptions and source 08's constant-slope hypothesis are not supplied. The full line-by-line read scope is in reading-and-failures.md; hashes authenticate the reused files.

The complete matching family-377 tree lists one manuscript, build sources and bibliography; it does not list a same-family companion claiming the viscous theorem. Unrelated manuscript contents were not searched for semantic duplicates.

## Exact viscous equation in prior work

[Héctor Sánchez Morgado, Time-periodic Evans approach to weak KAM theory, arXiv:1712.10275v1](https://arxiv.org/abs/1712.10275v1). [Read PDF pages 1–5](sanchez-morgado-1712.10275v1-pages-1-5.txt). Equation (4), with H(p)=|p|²/2 and k=1/tau, is precisely G_tau=0. The paper starts from an exponential variational problem and notes the loss of ellipticity with growing gradients. Lemma 1 and Theorem 1 concern classical periodic solutions. Their periodic global argument does not establish interior control for every continuous fitted entire solution. No later sections were read or used. The equation and exponential variational representation are therefore not claimed as new here.

[Alessio Porretta, Regularizing effects of the entropy functional in optimal transport and planning problems, arXiv:2203.04856v1](https://arxiv.org/abs/2203.04856v1). [Read pages 1–7](porretta-2203.04856v1-pages-1-7.txt), [read pages 8–13](porretta-2203.04856v1-pages-8-13.txt). Equation (1.7), after replacing his potential u by -V, is G_epsilon=0. Theorems 1.1–1.3 impose positive smooth marginal densities and specific boundary conditions. Section 3 derives classical gradient estimates; Theorem 3.4 depends on those data, epsilon and solution bounds. These are useful prior methods, not the missing local viscosity estimate under affine fits. The appendix and pages 14 onward were not read.

## Strong comparison: the tempting citation and its limitation

[Masaki Ohnuma, Strong comparison principle of semicontinuous viscosity solutions to some nonlinear elliptic equations, RIMS Kôkyûroku 1481 (2006), 56–68](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1481-6.pdf). PDF pages 1–5 read; [retained pages 2–5](ohnuma-2006-pages-2-5.txt). Conditions F1–F3 and Theorem 3.1 apparently encompass locally strictly elliptic smooth gradient-dependent operators. This is a tempting formal match, but the broad theorem is not a proof dependency here because of the later warning below. Text extraction has OCR/math artifacts; no uncertain glyph is needed for the I231 deductions.

[Masaki Ohnuma and Shigeru Sakaguchi, A simple proof of a strong comparison principle for semicontinuous viscosity solutions of the prescribed mean curvature equation, arXiv:1806.03587v1](https://arxiv.org/abs/1806.03587v1). [Read pages 1–2](ohnuma-sakaguchi-1806.03587v1-pages-1-2.txt), [read pages 3–4](ohnuma-sakaguchi-1806.03587v1-pages-3-4.txt). The introduction reports that the earlier Giga–Ohnuma proof does not work for gradient-dependent nonuniformly elliptic equations. Theorem 2.1 concerns prescribed mean curvature; its replacement proof uses special smooth Dirichlet solutions and gradient estimates. I231 does not infer the corresponding theorem for G_tau. The warning is not a counterexample to G_tau strong comparison, only a reason the tempting citation leaves SC_tau unpaid.

## Contribution boundary

The only new checked deductions offered are the trace-aware barycentric input and conditional reductions, plus the explicit infinite-tau obstruction. No external read supplies the finite-tau Liouville conclusion, and no absence in this bounded search proves novelty. The finite-tau target remains unresolved; its displayed operator already has primary antecedents.
