# I239 — primary sources and checked contracts

All sources below were actually read in the stated scope. Existing excerpts were reused without copying or modifying them. This is a proof audit, not a worldwide novelty search. The pinned OpenAI results are stipulated true; only their interfaces with the changed equation were examined.

## Pinned package

Revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Local files were byte-matched to fresh pinned raw retrievals, and their Git blob hashes independently matched the exact family entries of `sources/preprints-tree.json`. The family-only path inventory and README identify one manuscript, with no same-family companion. This is not a search through unrelated papers.

- [03-reduction.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/03-reduction.tex): lines 1–80 read. `thm:liouville` and `eq:limit-fit` give the exact homogeneous theorem and fit contract. The homogeneous conclusion itself is not used to infer the viscous conclusion.
- [04-limiting-tools.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/04-limiting-tools.tex): lines 1–240 read. `lem:frame-invariance` and `lem:fit-compactness` separate the fit-only geometric estimates from the PDE limit. I239 verifies the trace scaling and new PDE limit. Later quadratic-envelope slope arguments were not used.
- [05-envelope-contact.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/05-envelope-contact.tex): complete file read. `lem:barycentric-envelope` supplies finite attainment, duality, measure admissibility, continuity and semiconcavity. The synchronized proof of `lem:common-time-subsolution` was inspected and extended with the trace directions in the independent analytic check. The geometric extremal-measure portion of `prop:envelope-contact` applies after the changed-PDE checks. Its original affine-slice proof and finite-Hamiltonian conclusion are not invoked.
- [02-flatness.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/02-flatness.tex): lines 70–137 read, including the complete `lem:sum-rule` contract. It supplies closed jets at an interior product maximum and the block upper matrix bound; no equation is part of this operation. Unrelated flatness conclusions are not used.

## Autonomous convolution and one-sided Fatou

V. Julin and P. Juutinen, [A new proof for the equivalence of weak and viscosity solutions for the p-Laplace equation, arXiv:1104.2197v1](https://arxiv.org/abs/1104.2197v1). [Reused primary excerpt, PDF pages 1–6](../i236_viscous_contact_propagation/julin-juutinen-1104.2197v1-pages-1-6.txt), read completely in two bounded displays. Fresh PDF retrieval and `pdftotext -layout` extraction matched the excerpt exactly.

Theorem 3.1 and its proof provide the autonomous-convolution/Fatou method. Remark 3.3 specifies the almost-everywhere Hessian convergence behind it. I239 checks that method for I236's explicit smooth exponential flux and independently verifies the remaining gradient limit. The p-Laplacian theorem is not being relabeled as a theorem about G_tau. Pages after 6 and Appendix A were not read. The v1 banner and the later internal compilation date are recorded as they appear; the fetched bytes, not an inferred publication history, are authenticated.

## Linear weak-solution Harnack

R. Crescimbeni, L. Forzani and A. Perini, [A new proof of Harnack's inequality for elliptic partial differential equations in divergence form, EJDE 2007, No. 38](https://ejde.math.txstate.edu/Volumes/2007/38/crescimbeni.pdf). [Reused primary excerpt, PDF pages 1–5](../i236_viscous_contact_propagation/crescimbeni-forzani-perini-2007-pages-1-5.txt), read completely. Fresh PDF retrieval/extraction matched it exactly.

Section 2 assumes measurable symmetric coefficients with positive uniform ellipticity bounds and defines the W¹,² weak-solution class. Theorems 3.1–3.2 give the solution Harnack/Hölder interface. I236 uses a linear harmonic replacement in this exact class, then a separate trace argument. It does not apply a theorem about a vector space of solutions directly to nonlinear supersolutions. Proof pages 6–12 were not read or treated as newly audited results.

## Excluded comparison shortcuts

M. Ohnuma and S. Sakaguchi, [A simple proof of a strong comparison principle for semicontinuous viscosity solutions of the prescribed mean curvature equation, arXiv:1806.03587v1](https://arxiv.org/abs/1806.03587v1). Both [pages 1–2](../i231_viscous_liouville/ohnuma-sakaguchi-1806.03587v1-pages-1-2.txt) and [pages 3–4](../i231_viscous_liouville/ohnuma-sakaguchi-1806.03587v1-pages-3-4.txt) read completely. The first excerpt was freshly byte-matched to PDF extraction. The introduction explicitly excludes the old proof for gradient-dependent nonuniform equations; its replacement concerns prescribed mean curvature. It supplies no ready-made theorem for G_tau here.

N. S. Trudinger, [Comparison principles and pointwise estimates for viscosity solutions of nonlinear elliptic equations, Rev. Mat. Iberoam. 4 (1988), 453–468](https://doi.org/10.4171/RMI/80). [Reused scanned PDF page 2, printed p. 454](../i236_viscous_contact_propagation/trudinger-1988-page-2.png) visually read in full. F2 requires a gradient-Lipschitz bound independent of the Hessian. The candidate's actual smooth solution jets refute that bound for G_tau. Only this page was read in I239; no theorem from the remainder is adopted.

## Existing exponential operator

H. Sánchez Morgado, [Time-periodic Evans approach to weak KAM theory, arXiv:1712.10275v1](https://arxiv.org/abs/1712.10275v1). [Reused pages 1–5 excerpt](../i231_viscous_liouville/sanchez-morgado-1712.10275v1-pages-1-5.txt): only lines 1–125, covering pages 1–2 and the next page heading, were read in this audit. Equations (EL) and (4) already contain the exponential divergence operator and its quadratic-Hamiltonian specialization. No periodic existence or regularity theorem is used. The rest of this excerpt was not read in I239.

The final verdict depends on the independent calculations in analytic-check.md, the stipulated source operations and standard linear weak-solution theory. It does not depend on a generic nonlinear strong-comparison citation or the novelty of the displayed operator.
