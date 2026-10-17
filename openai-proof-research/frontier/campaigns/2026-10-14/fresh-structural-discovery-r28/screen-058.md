# Family058: finite volume does not pay prescribed scaling normalization

Unfrozen feasibility screen, not a candidate or proof/contribution verdict. Source truth remains stipulated. The intended broad question was whether a bounded semialgebraic pseudoconvex domain with finite complete Kähler–Einstein quotient volume must be bounded symmetric. No scope was frozen: no complete new mechanism was found.

Actual source contracts: the bounded-domain paper thm:main assumes a properly discontinuous **cocompact** action, allows finite stabilizers and initially singular affine ambient spaces, and concludes smoothness and bounded symmetry. The companion universal-cover classification thm:main assumes a connected normal **projective** variety. Neither statement provides finite-volume noncompact quotients. In thm:quadratic-model, points p_j=Phi(0,i t_j a_0) on a prescribed normal approach are written gamma_j(k_j), with all k_j in one compact K. This supplies forward Schwarz bounds and compact inverse images. The complete source Vey transfer also explicitly requires divisibility (compact covering set).

A real obstruction to the proposed replacement is already present in dimension one. Let H={Im z>0}, Gamma=PSL_2(Z), and z_y=i y, y→infinity. For gamma represented by integers a,b,c,d with ad−bc=1,

    Im(gamma z_y)=y/(c²y²+d²).

If c=0 then d=±1 and this equals y. If c!=0 then it is at most1/y. Given compact K subset H, choose0<eta<=Im z<=B on K. For y>max(B,1/eta), no gamma z_y lies in K. More strongly the curvature-minus-one hyperbolic distance satisfies |log(Im u/Im v)|<=d_H(u,v); consequently

    inf_{gamma in Gamma, v in K} d_H(gamma z_y,v)
       >= min(log(y/B),log(eta y)) -> infinity.

Thus even normalization within a fixed intrinsic radius of K fails. This calculation is universal in gamma and y, not a finite test.

The quotient has finite area. The standard fundamental region |Re z|<=1/2, |z|>=1 has hyperbolic area integral from−1/2 to1/2 of dx/sqrt(1−x²)=pi/3. To see coverage, maximize Im(gamma z) by minimizing |cz+d| over primitive integer pairs, which has a positive attained minimum; translate the real part into the interval, and apply inversion if |z|<1 to contradict maximality. Standard side pairing gives the fundamental region, with boundary sets of zero area. Cayley transform sends H to the bounded semialgebraic disk and z_y to the radial normal sequence(y−1)/(y+1)→1, preserving the example. Restricting to the index-six principal congruence subgroup Gamma(2) gives a finite-area free-action version: an elliptic nonidentity element would have trace0, but a,d odd and b,c even imply det=−a²−bc=−1 mod4 when d=−a, contradicting det1. No counterexample to bounded symmetry is claimed; the disk is symmetric. The example refutes a proof step only.

Closest primary operation: Kuai–Liu–Wu, arXiv1801.00459v3, https://arxiv.org/html/1801.00459v3, Theorem1 proves finite-volume convex rigidity; Theorem2 splits contractible HHR/USq domains into symmetric and discrete-automorphism factors. Read actual Lemma6.3 proof: a supremum of translates of a peak function and finite-volume Liouville give orbit accumulation at a peak. The §7 proof uses convex supporting half-spaces to retain uniformly deep translated segments, then pulls them back to compact Kobayashi balls to prove a complete holomorphic flow. These are actual prior operations. General boundary-orbit accumulation does not supply the controlled normal/tangential scales used in the source's fixed quadratic model. Convex half-space control is unavailable for arbitrary semialgebraic domains. Obtaining compatible orbit/scaling selection and preventing collapse remains unpaid. A smooth/convex subclass is not substituted as a candidate.

A Zaitsev search lead concerns the **algebraic automorphism subgroup** with Levi-nondegeneracy hypotheses; its abstract is not a theorem about all automorphisms of every semialgebraic domain. No general finite-component theorem is assumed. The full Zaitsev body was not read. No global novelty or impossibility claim follows.

Reading: bounded-domain paper.tex65–215; 04_scaling.tex130–180 and220–385; all05_symmetry.tex; companion main.tex1–150. Other retained058 source files are byte-authenticated but not claimed semantically read. Primary HTML introduction/main statements and actual §6.1–6.2 plus §7 through Lemma7.5/proposition proof and beginning Lemma7.7 read. Later parts and full splitting proof not read. Exact source/primary receipts retained privately. Prose Myeongjin Kang/no affiliation, CC BY4; no count or publication.
