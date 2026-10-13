# I240 — actual primary sources, contracts and reading limits

All listed retained/reused excerpts were read over the indicated ranges. Search results were locators only unless explicitly described otherwise. No missing search hit certifies worldwide novelty.

## Pinned package and companion check

Revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, [family-377 directory](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026).

Reused root: `frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/`.

- README, complete; main.tex, complete; build/references/bibliography.tex, complete.
- 03-reduction.tex, lines 1–75: thm:liouville and eq:limit-fit. The PDE is F[V]=0, not G_tau[V]=0.
- 04-limiting-tools.tex, lines 1–235: lem:frame-invariance, lem:fit-compactness, full geometric growth/compactness proof. The proof states where the PDE first enters.
- 05-envelope-contact.tex, complete 597 lines: barycentric-duality, barycentric-semiconcavity, common-time-subsolution, barycentric-subsolution, envelope-contact, and the finite-slope tail. The extremal contact is supplied; the finite-slope tail is not imported into the viscous proof.
- 08-rigidity.tex, complete: constant-envelope-slope rigidity and the final homogeneous assembly. This establishes exactly how I236 changes the terminal argument.
- 02-flatness.tex, lines 70–102 and 110–129: the displayed fixed-center argument and exact equation-free theorem-of-sums contract. No claim to reread the full three-point proof.

All entries under the exact family prefix in sources/preprints-tree.json were inspected and the used files' Git blob IDs matched. There is one manuscript, plus its build files, figures, bibliography and PDF; no second same-family companion. sources/CONTENTS.md was read only at lines 9125–9142. No unrelated manuscript survey or history replay was performed.

## The same viscous equation before I236

**H. Sánchez Morgado, Time-periodic Evans approach to weak KAM theory**, [arXiv:1712.10275v1](https://arxiv.org/abs/1712.10275v1). Reused `../i231_viscous_liouville/sanchez-morgado-1712.10275v1-pages-1-5.txt`, complete. Equation (EL) and (4), for quadratic Hamiltonian and k=1/tau, give exactly the exponential divergence equation and G_tau. Equation (7) records its nonuniform ellipticity. Lemma 1 requires a C2 solution on the torus and its lower-order structural assumption; its two-point maximum proof uses periodicity. Theorem 1 supplies smooth solutions for the specified mechanical Hamiltonian. These are not an entire continuous FIT Liouville theorem. Page 5 already displays the symmetric elliptic linearization. Later sections were not read.

**A. Porretta, Regularizing effects of the entropy functional in optimal transport and planning problems**, [arXiv:2203.04856v1](https://arxiv.org/abs/2203.04856v1). Reused `../i231_viscous_liouville/porretta-2203.04856v1-pages-1-7.txt` and `...-pages-8-13.txt`, complete union of reads. Equation (1.7) has I236's operator after u=-V. Theorem 1.1 has bounded smooth convex spatial domain, positive W1,infinity marginals and spatial no-flux/temporal nonlinear data; Theorem 1.2's whole-space variant has finite time, a uniformly convex confining potential and Gaussian-comparable marginals. Theorem 3.4 is for a C3 interior/C2 closure solution of (3.4), with radial C3 H satisfying (2.5)–(2.6), C2 f satisfying (3.8), and constants depending on epsilon and the displayed boundary-data norms. Its full proof uses boundary control; it is not an interior estimate for every continuous solution under FIT. The appendix and pages 14 onward were not read.

## Old Liouville hypotheses actually examined

**L. A. Peletier and J. Serrin, Gradient bounds and Liouville theorems for quasilinear elliptic equations**, Ann. Scuola Norm. Sup. Pisa, ser. 4, 5 (1978), 65–104, [primary Numdam PDF](https://www.numdam.org/item/ASNSP_1978_4_5_1_65_0.pdf).

Retained [PDF pages 3 and 5, text](peletier-serrin-1978-pages-3-and-5.txt), with [page 3 image](peletier-serrin-1978-page-3.png) and [page 5 image](peletier-serrin-1978-page-5.png), corresponding to printed pp. 66 and 68. Both page images were read fully because text extraction loses the mathematical displays.

Theorem 1.1: C3 entire solution of Delta u=f(u,Du), bounded Du, and for every 0<epsilon<L constants mu,N>0 such that f_u+f^2/(n|p|^2)>=mu and |f_p|<=N on epsilon<=|p|<=L, uniformly in u. Conclusion: constant. Theorem 1.3 instead assumes f_u+f^2/(2n|p|^2)>=0, condition H (annular |f_p|<=C|f|), bounded Du and M(d)=o(d). It concludes constancy. The printed extension to A(Du):D2u=0 retains bounded Du and one-sided sublinear growth. For n=2 a footnote points to removal of the gradient bound under that sublinear-growth hypothesis; it does not remove the growth hypothesis or cover all dimensions/FIT. These are concrete different assumptions, not a proof that I236 is already known.

An initial text extraction of PDF pages 1–8 was read as text but contained missing display equations. It was replaced by the smaller exact two-page extraction and images above; no unread full PDF or incompletely checked eight-page excerpt is retained. Other introductory text seen there was not used as a theorem. No claim is made about the unexamined general statements later in this paper.

The classical global-Lipschitz affinity proof in contribution-analysis.md is an explicit translation-difference deduction from the linear source below, not an attribution of the exact FIT theorem to Peletier–Serrin.

## Established local methods

**V. Julin and P. Juutinen**, [A new proof for the equivalence of weak and viscosity solutions for the p-Laplace equation, arXiv:1104.2197v1](https://arxiv.org/abs/1104.2197v1). Reused `../i236_viscous_contact_propagation/julin-juutinen-1104.2197v1-pages-1-6.txt`, complete. Section 3, Theorems 3.1–3.2, (3.1)–(3.5), Remark 3.3 give inf-convolution, semiconcavity, Alexandrov differentiation, mollification, one-sided Fatou and the Hessian convergence fact. The introduction notes autonomous extensions including minimal surface, but not general x-dependent divergence equations. These are method precedents; their p-Laplacian theorem is not identified with G_tau. The singular section only begins on the last retained page; its later proof and Appendix A were not read.

**R. Crescimbeni, L. Forzani and A. Perini**, [A new proof of Harnack's inequality for elliptic partial differential equations in divergence form, EJDE 2007, No. 38](https://ejde.math.txstate.edu/Volumes/2007/38/crescimbeni.pdf). Reused `../i236_viscous_contact_propagation/crescimbeni-forzani-perini-2007-pages-1-5.txt`, complete. Section 2 assumes measurable symmetric coefficients with fixed 0<lambda<=Lambda and W1,2 weak solutions. Equations (2.4)–(2.5), scale invariance and Theorems 3.1–3.2 provide oscillation decay/Harnack. It is a theorem for solutions; I236's harmonic replacement supplies those hypotheses from its supersolution. The proof on later pages was not read. The 1961 Moser publisher page was located for bibliographic context only; its unavailable full text is not a separate theorem dependency.

**N. S. Trudinger**, [Comparison principles and pointwise estimates for viscosity solutions of nonlinear elliptic equations](https://doi.org/10.4171/RMI/80), Rev. Mat. Iberoam. 4 (1988), 453–468. Reused I236 extracted images `trudinger-1988-page-1.png` and `...-page-2.png`, both read fully. Printed p. 454 gives F1 uniform ellipticity and F2: |F(x,z,p,r)-F(x,z,q,r)|<=mu1|p-q| independently of r. G_tau fails this hypothesis on every nontrivial p-ball as r varies. No unexamined later theorem is cited to close SC_tau.

**M. Ohnuma and S. Sakaguchi**, [A simple proof of a strong comparison principle for semicontinuous viscosity solutions of the prescribed mean curvature equation, arXiv:1806.03587v1](https://arxiv.org/abs/1806.03587v1). Reused both `../i231_viscous_liouville/ohnuma-sakaguchi-1806.03587v1-pages-1-2.txt` and `...-pages-3-4.txt`, complete. Introduction explicitly rejects the earlier gradient-dependent nonuniform proof; Theorem 2.1 concerns mean curvature. Its classical replacement on each small ball and recovery of boundary equality are relevant methodological precedent, not a generic G_tau theorem. Later pages were not read.

The I236 Kawai–Ohnuma citation was read only through I236's literature account; its actual primary excerpt was not opened or relied on in I240. Broad searches returned other Liouville equations with gradient source terms; those are not evidence of an identical principal operator and were not retained.
