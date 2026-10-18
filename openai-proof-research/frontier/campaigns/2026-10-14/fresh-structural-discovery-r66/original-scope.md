# Original scope T314C — frozen before candidate proof assembly

Author: Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.
Author research, not independent review. Source truth stipulated only at openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Count remains14. This scope is frozen after exploratory derivation and primary comparison, not before discovering the proposed last-p²-step mechanism. Parent has independently suggested the same bookkeeping as author collaboration; this is not a review gate.

For every odd prime p, every integer d>=1, every d-dimensional F_p-vector space L, and every alternating bilinear map beta:L×L→L, choose any basis and let R=(Z/p²Z)^d. Identify L with R/pR and define i:L→pR by i(v)=p times any lift of v. Define a multiplication on R by
    x*y = x+y+i((1/2) beta(x mod p,y mod p)).
Call the resulting group G_beta. Let
    rho(beta)= (1/2) min_{0!=f in L*} rank[(u,v)↦f(beta(u,v))].
The intended general theorem is: G_beta is a powerful group of exponent p², order p^(2d), with central elementary abelian subgroup pR and with pth-power isomorphism G_beta/pR→pR induced by i. Its sectional rank (maximum minimal generator number of S/N over all N normal in S<=G_beta) is exactly d. Its minimal length ell(G_beta,1) of an arbitrary subnormal series with cyclic quotients satisfies
    ell(G_beta,1) >= d+rho(beta).
Normality is required only in the next group, not in the ambient group, and no central-chain restriction is permitted. The argument must cover every cyclic series, including intervening p-factors and arbitrary nongraded subgroups. For beta=0 the nilpotency class is1; class at most2 is the general assertion. The displayed central subgroup need not be the whole center in general.

The principal explicit family uses every odd prime p and every odd integer d>=3, L=F_(p^d), beta(x,y)=x y^p−x^p y. For these groups G_(p,d), the intended claims are Z(G)=G^p=Phi(G)=[G,G]=pR, sectional rank d, and
    ell(G_(p,d),1) >= (3d−1)/2.
In particular the excess over sectional rank is at least (d−1)/2 for each fixed odd prime. The trace forms have rank exactly d−1, fully credited to the classical Gow–Quinlan construction; the group/algebra correspondence is also prior work.

Applying source314 thm:main gives, for every h>=0, r_h(G_(p,d),1)>= (3d−1)/2, where r_h is exactly the source's least loss in the implication on all finite p-local genuine G-spectra. Consequently for every integer 0<=t<(3d−1)/2 there is a finite p-local genuine G-spectrum X with K(h+t)_*(Phi^1 X)=0 and K(h)_*(Phi^G X)!=0. This includes h=0 and compact retracts in the source convention. No explicit cell bound, sharp value of ell or r_h, bounded-size spectrum, or global priority claim is part of this scope.

Exact upstream interface read before freeze: complete01-introduction.tex (definition eq:def-loss and thm:main) and02-background.tex;05-profinite.tex lines1–38 inspected to distinguish its extra congruence hypotheses from a sectional-rank assumption alone. All12 source text blobs were authenticated against the full13223-entry canonical tree; other retained bodies are not claimed read.

Nearest primary readings before freeze: de las Heras–Traustason arXiv2006.12593v1 introduction and full§6 through Cor6.10 (powerful type-(2,…,2) groups, pth-power identification, alternating-algebra correspondence, powerful composition series); Gow–Quinlan arXiv0709.0741v1 introduction, Lemmas1–3 and Theorem1 (the exact trace forms and constant rank); Kuhn–Lloyd arXiv2008.00330 retrieved version, Definitions2.5–2.6, discussion of r_minus/r_plus and §5 including Examples5.12–5.15 (unbounded relative gaps and failure of product additivity). No claim is made that unbounded cyclic-length gaps in general are new. The proposed new operation is the lower bound for arbitrary subnormal cyclic chains through the last order-p² factor, controlling all earlier such factors by a single commutator form.

Prior I105 quantitative spectrum realization is excluded: that asks for cell bounds, absent here. Source297 prescribed traces and118 hierarchy gaps were excluded by r55/r51 history. Source164 mixed-expression screen is not reopened. The sl_n matrix-family idea was only pre-freeze exploration; no matrix-family theorem is nominated in this scope.
