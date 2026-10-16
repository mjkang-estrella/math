# Primary-source reading record

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Inputs retained privately with third-party rights unchanged. Retrieved for this review on 2026-10-16. Hashes are in `inputs/primary/retrieval.json`; exact HTML/PDF and text extractions are retained. Download authentication is not a reading claim. The following extents describe actual mathematical reading, not possession of entire papers.

## Accepted source 374

Immutable revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Directory: `preprints/Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/`.

I read the complete README, main.tex, introduction.tex, cells.tex, moments.tex, finite_stability.tex, gradient.tex, sharpness.tex, and bibliography entries. The complete statements and proofs of `cells:calculus`, `cells:weights`, `cells:optimality` (in sharpness.tex), `moments:midpoint`, `moments:derivative`, `finite:potentials`, `gradient:interpolation`, `gradient:finite`, `gradient:extension`, `main:stability`, and `sharpness:exponent` were inspected. All nine blobs are independently matched to the complete preprints catalogue in `inputs/source-authentication.json`. Article PDF and Lean files were not used.

The theorem contract is uniform rho=1_K dx/|K|, compact convex full-dimensional K, d>=2, arbitrary compact Y and all targets in P(Y). Its explicit interpolation constants are 12 and 28; moment constant is 162. Its statements alone do not establish weighted LC. Its proof operations and their weighted substitutions are reconstructed in review Sections 2–8, with upstream truth accepted as directed.

Pinned primary URL pattern: `https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/build/source/` followed by the retained source-relative path. README is directly under the manuscript directory.

## McCann 1997

[A convexity principle for interacting gases, published primary PDF](https://www.math.toronto.edu/mccann/papers/advances.pdf), Advances in Mathematics 128, 153–179. Retained as `mccann1997.pdf`.

Read §2 including Lemma 2.1, Theorems 2.2–2.3 and their complete proofs, the Brunn–Minkowski remark; §4 Theorem 4.4 and its complete proof, plus Remark 4.5 and equation (32). Earlier definitions/claims were inspected as needed for displacement interpolation, not the full article or Appendix proofs. The operative comparison is the pointwise density/Jacobian argument and determinant concavity. Review §9 explicitly derives the weighted midpoint bound from that mechanism. Theorem 2.3 itself is a global unweighted Lq norm statement, not a quoted weighted domination theorem. No new novelty is assigned to AM–GM or this standard log-concave specialization.

## Prékopa 1973

[On logarithmic concave measures and functions, author-hosted primary text](https://rutcor.rutgers.edu/Prekopa/pdf/SCIENT2.pdf), Acta Scientiarum Mathematicarum 34, 335–343. Retained typeset text `prekopa1973.pdf` identifies that publication; PDF page numbers 1–9 are reprint pagination.

Read §1 through Theorems 1–2, §2 Theorem 3 and the full induction proof, and the proof of Theorem 2 at the beginning of §3 using restrictions of the density. Did not audit the later strictness theorem or remaining applications. This is a primary antecedent for the log-concave restriction/product integral mechanism. Its set inequality rho((U+V)/2)>=sqrt(rho(U)rho(V)) by itself is weaker than existence of a midpoint coupling dominated by rho. The review does not conflate them; the coupling conclusion is independently checked and compared using transport Jacobians.

## Delalande–Mérigot

[arXiv:2103.05934v2, primary full HTML](https://arxiv.org/html/2103.05934v2). Retained version header identifies v2. Read Proposition 4.1 and Theorem 4.2 statements, and **all of §5**, including Lemma 5.1, its complete proof, the integral-geometry formulas and the complete Proposition 4.1 proof. Also inspected the introductory source/target hypotheses. Did not read the complete strong-convexity machinery in §§2–3 or all noncompact-target proofs.

The interpolation is a one-third norm estimate between convex Lipschitz potentials and their gradients on a rectifiable domain. The proof passes from a one-dimensional bound to lines and Crofton integration. The map theorem assumes the source density bounded above and below and gives W1^(1/6); that condition is not inherited by LC. The established interpolation mechanism, together with the pinned explicit h-form, is the relevant operation antecedent. Review §9 gives its own exact layer-cake deduction, without claiming that this paper states LC.

## Letrouit–Mérigot

[arXiv:2411.04908v3, primary full HTML](https://arxiv.org/html/2411.04908v3). Header: v3, 16 July 2026; body date August 24, 2026. Read Theorems 1.4, 1.7, 1.10, 1.11 and their surrounding hypothesis descriptions; **complete §2**, including Theorem 2.1, Proposition 2.2, all four steps of Theorem 2.1's proof, and the truncation/tail/interpolation proof of Theorem 1.4. Did not audit subsequent Whitney/spectral-graph or boundary-power proof sections.

Theorem 2.1 already permits a compact log-concave reference with comparison ratio m/M=1 when rho itself is log-concave. Its dual-pairing variance estimate uses Brascamp–Lieb with V+psi_t*, scaling, and controlled oscillation; it is not the linear W2 potential estimate P. Theorem 1.4's displayed full-support map result imposes strong convexity and an upper Hessian bound; the abstract's broader phrase is not a replacement for this contract. The boundary-power theorem assumes two-sided comparison with a prescribed power. These primary statements neither duplicate the complete LC conclusion nor establish a substantial new operation in the candidate.

## Mérigot HAL

[Sharp stability of Brenier maps via quantitative regularity of potentials, HAL v1 primary PDF](https://hal.science/hal-05616391v1/document). Retained PDF cover identifies **hal-05616391v1, submitted 7 May 2026**, 17 PDF pages including cover. Web extraction returned an Anubis denial; direct read-only retrieval from the same primary URL successfully returned the retained PDF. Its cover states CC BY-NC-ND 4.0; this review does not relicense it.

Read the full introduction, complete §2 (Proposition 2.1, Theorems 2.2–2.3, Lemma 2.4 and the proof of Theorem 2.2(i)), and §3.1–3.2 including Theorems 3.1–3.2 and full proofs. Did not read all of later simultaneous-perturbation, entropic, or appendix arguments.

Theorem 3.1 treats bounded compactly supported densities without a positive lower bound, yielding W1^(1/4). The main proof uses Jensen/Bregman divergences and quantitative singularities of convex functions. This is a different operation from the source-374 fixed-mass linear potential estimate. W1<=W2 alone leaves exponent 1/4. No theorem from this item is used to prove LC, and no duplication claim is based on its title.

## Wang–Wang

[arXiv:2610.09640v1, primary full HTML](https://arxiv.org/html/2610.09640v1). Read introduction, §1.1 hypotheses and Theorem 1, Theorem 2 and Proposition 4 statements, and complete §2 through the proof of Theorem 1 (Lemmas 6–8 and the optimization). Read surrounding remarks about compact sources. Did not audit optimality-example proofs or later moment proofs.

Theorem 1 assumes an Lp change of a BV probability reference and gives norm exponent (p-1)/(4p-2), hence 1/4 at infinity, with only one bounded target required. It regularizes with Moreau–Yosida, uses a second-order BV gap bound, and glues target and source graph plans. The asserted sharpness class is broader than LC; its statement is not an obstruction to LC. The intro explicitly describes source 374 as uniform-only. These facts locate the candidate without proving global priority.

## Additional bounded primary screen

[Ruan, arXiv:2610.07577v1](https://arxiv.org/html/2610.07577v1): read Theorem 8 and its full §12 proof, as well as relevant introductory hypotheses. Its compact/compact specialization gives W1 exponent s/[2(1+s)], s=1-1/p, hence 1/4 for bounded densities. Its plan-error/repair machinery is different from the source-374 argument. I did not audit all conditioning theorems or Appendix B; no correctness inference about those proofs is claimed.

[Ford, arXiv:2609.35574v1](https://arxiv.org/html/2609.35574v1): read Assumption 1.1, Lemma 2.5 and proof, Theorem 4.6 and proof, and adjacent fixed-source interpretation. At q=2 and Ahlfors theta=1 its stated bound gives W1^(1/4) for a fixed source, also covering bounded densities. Its subgradient-plan coupling and Fenchel-gap route does not state LC. The dependencies establishing its dual coercivity were not fully audited.

These readings go beyond the author's abstract/snippet screen but remain bounded. No survey, search snippet, AI audit page, or citation-only record is used as proof of a theorem or of worldwide novelty. The mathematical verdict does not depend on truth of any external primary result. The contribution verdict instead has the constructive reduction in review §9 relative to accepted source 374 and the identified standard operations.
