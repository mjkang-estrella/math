# I345 — primary antecedents and exact interfaces

2026-10-13. The result is a new-to-project unrestricted theorem candidate, not a demonstrated new-to-literature theorem. The search/read scope is bounded; priority is for a separate contribution gate.

## Pinned OpenAI corpus

Repository revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, as authenticated by sources/upstream.json. The prefix is `preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/`.

- [01-introduction.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/01-introduction.tex), actual `thm:main`: dimension-only interior C1,alpha bound for exact bounded infinity-harmonic functions in dimension d>=3. Entire Lipschitz rigidity follows by scaling; original n=2 uses the exact infinity lift into dimension three.
- [02-flatness.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/02-flatness.tex), `lem:linear-lift`, `lem:sum-rule`, `prop:three-point`. Its infinity lift is used only for exact infinity limits. Its three-point estimate is not extended to actual p-solutions by assertion.
- [03-reduction.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/03-reduction.tex), actual `thm:liouville`, `eq:limit-fit`, `lem:bad-scales`, `lem:cylinder-comparison`, geometric portions of `prop:nonaffine-limit`, and the gradient extraction. The PDE passage in that proposition is replaced for the modified lift. Its quadratic norm comparison has equal fitting parameters; the unequal-parameter entry in I344 needs the new Section 8 repair.
- [04-limiting-tools.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/04-limiting-tools.tex), `lem:frame-invariance`, `lem:fit-compactness`: equation-free fit/growth arguments reused after independently checking G_tau invariance and stability.
- [05-envelope-contact.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/05-envelope-contact.tex), `lem:barycentric-envelope` and geometric extremal-measure construction. The finite-tau common-time trace calculation is independently validated; homogeneous Hamiltonian-slope conclusions are not imported.

The complete pinned path listing and the relevant catalogue entry list one manuscript in this result family. No p-uniform or viscous companion is identified in that family. This is a matching-family check, not a semantic search of the entire corpus.

## Kotschwar–Ni: the uniform Lipschitz antecedent

Brett Kotschwar and Lei Ni, [Local gradient estimates of p-harmonic functions, 1/H-flow, and an entropy formula, arXiv:0711.2291v1](https://arxiv.org/html/0711.2291v1), Theorem 1.1 and equations (1.1)–(1.5). The transformed variable is w=-(p-1)log v. In Euclidean space its displayed constants give |Dw|=O_n((p-1)/R), hence a uniform logarithmic gradient bound after division. Shifting signed u to a positive function bounded between its oscillation and twice that oscillation gives the uniform local Lipschitz input. This is a classical corollary, not the new unrestricted gradient theorem. Introduction and the relevant Section 2 derivation were read; the flow and entropy results are not premises.

## Uhlenbeck: fixed-p rigidity and bounded-p coverage

Karen Uhlenbeck, [Regularity for a class of non-linear elliptic systems](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6219-11511_2006_Article_BF02392316.pdf), Acta Mathematica 138 (1977), 219–240, [DOI 10.1007/BF02392316](https://doi.org/10.1007/BF02392316).

The main/scalar statements on printed pp. 221–222 apply to rho(Q)=Q^{(p-2)/2}. Quantitative Theorem (5.4), pp. 238–239, bounds gradient Hölder oscillation using the bounded-gradient quantity M, structural K and the power parameter. Its proof, including (4.11)–(4.12) and (5.5), permits common choices when this power ranges over a compact interval with a common positive continuity exponent. This supplies classical 3<=p<=P coverage, not uniformity as P->infinity. Theorem (6.1), p. 239, yields affinity of entire bounded-gradient fixed-p solutions. Actual statements and Sections 4–6 were read; the exact compact-parameter check is in analysis Section 2.2.

The alternative Tolksdorf article was located bibliographically but its attempted primary PDF retrieval was blocked (403). No unseen Tolksdorf theorem is used. Uhlenbeck provides the needed primary interface independently.

## Savin: small solutions of the new lifted family

Ovidiu Savin, [Small Perturbation Solutions for Elliptic Equations](https://www.math.columbia.edu/~savin/Small_pert.pdf), CPDE 32 (2007), 557–578, [DOI 10.1080/03605300500394405](https://doi.org/10.1080/03605300500394405). H1 requires Hessian ellipticity; H2/H4 require uniform ellipticity and C2 control only near zero jets. Theorem 1.3 gives interior C2,alpha regularity at sufficiently small amplitude. Proposition 4.1's varying-operator argument makes the threshold uniform under common local structural bounds. Pages 1–4 and 14–18 were read via existing extractions and checked against the primary interface.

I345 supplies those bounds for its own modified operator, including max(B,0), parameter endpoints and an amplitude parameter. Its proportional derivative estimate and physical Hessian estimate are new deductions; neither small original gradients nor global uniform ellipticity is assumed.

## Weak/viscosity equivalence and linear Harnack

Vesa Julin and Petri Juutinen, [A new proof for the equivalence of weak and viscosity solutions for the p-Laplace equation, arXiv:1104.2197v1](https://arxiv.org/abs/1104.2197v1). Existing PDF pages 1–6 were read. Definitions 2.1–2.3 and the p>=2 equivalence interface identify actual weak solutions and their polynomial test equations. Remark 3.3 supplies the a.e. mollified-Hessian fact used in the independently proved exponential-flux passage. The p-Laplace equivalence theorem is not claimed to apply to that new flux.

Raquel Crescimbeni, Liliana Forzani and Alejandra Perini, [A new proof of Harnack's inequality for elliptic partial differential equations in divergence form](https://ejde.math.txstate.edu/Volumes/2007/38/crescimbeni.pdf), EJDE 2007, No. 38. Existing pages 1–5 were read. Equations (2.1), (2.2), (2.5) and Theorems 3.1–3.2 concern weak solutions with symmetric measurable uniformly elliptic coefficients. I345 uses them only after constructing a linear weak Dirichlet replacement, with all coefficient and function-space hypotheses paid.

## Internal predecessors and contribution limits

I230 is restricted to quasiconcave geometry and is not an unrestricted premise. I236's finite-positive-viscosity fitted-class rigidity and I239's proof check were read; I345 independently validates its non-stipulated contact, flux and envelope deductions in analysis Section 9. I241's selected high-viscosity estimate motivated the larger-cylinder/Savin method, but its unlifted operator is not reused for the new PDE without recalculation.

The proposed advance is the unrestricted p-uniform gradient theorem through a critical-safe constrained lift, exact projected fit contract, uniform lifted small-solution family and repaired quadratic norm transfer. Standard primary inputs, prior restricted results and the resulting actual-gradient convergence are not separate findings. No assertion of worldwide novelty, endpoint regularity, boundary regularity, independent gate approval, or count increment follows from this bounded comparison.
