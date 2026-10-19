# Arithmetic/algebraic discovery r77 — research archive

No target was frozen and no candidate is nominated. This is an author research record, not an independent proof or contribution verdict. No count or gate is assigned. The supplied campaign status is 18/20, separate from its historical baseline. All OpenAI statements and operative proof operations used here are stipulated at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

The opening historical screens covered 194 (Lech), 195 (small Cohen–Macaulay modules), 204 (spin saturation), and 044 (Hikita). The sustained source/primary investigations were 208 (finite tensor categories), 054 (arithmetic points on the cubic-fourfold loci), and 069 (central quotient compatibility). This is not seven fresh full proof audits: the first four were history-based exclusions. The later investigations included actual finite symmetrizer and coend calculations, a motivic specialization reduction, and a two-cocycle lifting calculation. All calculations below preceded any possible scope freeze. There are no frozen theorem bytes and no narrower substitute nominee.

## Historical exclusions by operation

AB194's actual contribution review explains the enlarged root windows and the cardinal-node primitive H_i: changing the omitted interpolation node retains the source's arbitrary-root bundle, layer functional, rounding and Frobenius descent. It is not an untouched multiplicity mechanism. I28's filtered small-CM construction already constructs a finite filtered model from the associated graded surface algebra; the missing genuinely nonconical example is not supplied by repeating Rees arguments. The I28 display in this round was partial, so this is a bounded exclusion, not fresh proof clearance.

I104 and `spin-four-factor-r2/candidate.md` already distinguish three-factor saturation from a common integral root-congruent diagonal in two moment polytopes. Their real polygon, special-vertex, signed-cycle and local repair calculations are actual prior work. Neither their old common-diagonal problem nor a tensor-arity reformulation was selected.

Arithmetic r24's actual 044 screen identifies Dumanski–Krylov's completed-kernel descent as the existing K-theoretic reduction and distinguishes the unprovided shifted quantum relations. That report was read; its primary bodies were not newly reopened. No cohomological-to-quantum transfer is claimed here.

The r75 and r76 research and limits were read as exclusion context, not as verdicts on a new candidate. In particular, the two-norm lattice, bounded-complement discrepancy interpolation, matrix algebraicity/external-parameter issue, integral surface motives, and relative complete-intersection presentation issue were not resumed.

## 208: quantitative height and finite reconstruction have compatible existing reductions

The source's complete introduction, projectivity section, dimension descent and consequences were read. They already supply the full finite-category functor, restricted-tilting input, exact higher Frobenius selection, scalar-compatible iteration, finite-simple trapping, characteristic-two extension, incompressible classification, uniqueness in characteristic two, and internal affine-group reconstruction. Relevant labels are `thm:main`, `prop:first-nonprojective`, `lem:internal-norm-products`, `lem:equality-descent`, `eq:scalar-iteration`, `eq:combined-functor`, and `cor:generalized-tannaka`.

The old I104 nonfinite moderate-growth target is excluded. The finite generator and finite graph are retained in this screen, rather than silently assumed for a nonfinite category.

### A finite version of the source's projectivity calculation

Let P be a projective generator in a finite symmetric tensor category C over an algebraically closed field of characteristic p. Put L=length(P) and b=max_S length(S tensor P), where S runs over the finitely many simples. Exact tensor products and composition-series counting give

    length(P^tensor d) <= L b^(d-1),
    dim End(P^tensor d) <= L^2 b^(2d-2).

Choose an integer a>=2 with a!>L²b^(2a-2). The action of k[S_a] on P^tensor a has a nonzero kernel element. Such a exists because factorial growth eventually exceeds fixed exponential growth.

The strongest directly compatible primary operation is not merely an existential symmetrizer lemma. Coulembier–Etingof–Ostrik, arXiv:2107.02372v2, Lemma 4.10 and Kleshchev's complete Appendix A prove that a nonzero element of k[S_a] in a tensor ideal produces a total symmetrizer in degree

    m = a (p-1) (p^ell_p(a)-1),
    ell_p(a) = min {j>=0 : a < p^j}.

This explicit m is Remark A.4. The proof of Lemma 4.10 uses the faithful restriction of the projective cover of the trivial S_m-module, then its simple socle, to put the total symmetrizer in the ideal. Thus the source's total symmetrizer on P^tensor m is zero with this finite m.

Suppose all M(t)=Hom(P,P^tensor(p^t)) were projective for 1<=t<=floor(log_p m). For any elementary abelian p-subgroup H of S_m, each orbit of its permutation action has size p^t<=m and is regular for a quotient of H. The source's internal-norm product lemma makes evaluation of the product of all orbit powers projective for the product of the quotient groups. Their joint action is faithful, so restriction to H is projective. Chouinard's criterion, exactly as used by the source, makes Hom(P,P^tensor m) projective over S_m.

The epimorphism P→1 gives a nonzero coinvariant quotient of this module. The norm on a projective group module is an isomorphism. The total symmetrizer therefore acts nontrivially, a contradiction. Consequently the source's least nonprojective rank satisfies

    r <= floor(log_p m).

Its completed construction then gives a level at most max(2,floor(log_p m)). The number of simple objects controls the number of iterations, not an additional multiplication of the tower height: the source already tensors all target factors in one level and corrects their common scalar twist.

This entire quantitative calculation is an application of the **actual explicit** primary bound to the source's actual norm argument. No new representation-theoretic estimate, support selection, or coherence construction remains in it. It is not nominated. The historical r74 screen, located later during screening but before any freeze, had already flagged quantitative-height navigation; it is explicitly credited, not described as a newly untouched question.

### A stronger dimension-based comparison was also checked

Benson–Etingof–Ostrik, arXiv:2003.10499v4, Corollary 4.61 and its proof classify the tensor subcategories of a higher Verlinde category. Given a source fiber functor, let I be the full subcategory of subquotients of its image. The source already proves that this is a finite tensor subcategory and that the corestriction is dominant. Its cited Frobenius–Perron dimension inequality gives FPdim(I)<=FPdim(C). The primary classification confines I to the full/plus tower categories and the low-level Vec/sVec cases, with the usual low-level conventions. Thus the known dimensions of those categories already constrain how high the image must sit.

Proposition 4.10 gives FPdim(Ver_(p^n))=p^n/(2 sin²(pi/p^n)); Corollary 4.11 gives the odd-characteristic factorization with sVec. Their actual proofs and the subcategory proof were read. The characteristic-two subcategory proof refers to the authors' earlier paper, which was not newly read here. No new sharp minimal-level formula is asserted. This comparison prevents promoting the cruder symmetrizer bound simply because the source introduction left its level nonexplicit.

### Finite-object coend calculation

The source only states that the reconstructed group is affine. The r74 screen already distinguished the finite-type claim from finiteness of its coordinate object and left the latter unverified. That antecedent was found before any freeze and is retained here.

CEO arXiv:2306.09745v1, §4.1.1 gives the actual coend

    O(Aut^tensor(F)) = integral^X F(X) tensor F(X)^dual

in Ind(V). Its Theorem 4.2.1 is the generalized Tannaka equivalence; Lemma 4.2.3 and proof retain the extra base-category factor. Lemma 4.3.3 is a **finite-type** criterion under that section's GR/MN assumptions, and is not silently cited as finite-object finiteness.

Here there is an elementary finite calculation using the coend itself. For any X choose an epimorphism q:P^n→X. Exactness of F gives an epimorphism F(q) and dual monomorphism F(q)^dual. Dinaturality on F(P^n) tensor F(X)^dual says

    i_X (F(q) tensor id) = i_(P^n) (id tensor F(q)^dual).

The first map into F(X) tensor F(X)^dual is epic. Hence the image of i_X is contained in the image of i_(P^n). Additivity and the inclusions/projections of P^n show that the latter image is contained in the image of i_P: the off-diagonal matrix components vanish under the coend relation and each diagonal component is the coefficient map for P. All coend structure maps therefore land in im(i_P). Their universal epimorphism onto the coend implies

    F(P) tensor F(P)^dual → O(Aut^tensor(F))

is epic. Its source has finite length in V, so the coordinate object has finite length and belongs to V, rather than only Ind(V).

This is a direct application of the primary coend construction and projective-generator quotient presentation. It does not produce a faithful symmetric functor V→Vec, an ordinary finite group scheme over k, or a cohomological finite-generation theorem. In particular, a faithful exact functor need not inject Ext groups (the forgetful functor from representations of a finite p-group to vector spaces is the elementary warning). Cohomology and invariant-theory searches were navigation only; no such broad target was frozen. There is no residual finite reconstruction operation submitted for review here.

Primary URLs: https://arxiv.org/pdf/2107.02372v2 ; https://arxiv.org/pdf/2306.09745v1 ; https://arxiv.org/pdf/2003.10499v4 .

## 054: arithmetic specialization is paid by the motivic theorem

The source's `cub:criterion` is pointwise: every smooth complex cubic with rank(T)=21, |det(T)| above its common ineffective threshold, and End_Hdg(T_Q)=Q is irrational. Its `cub:generic` supplies these data very generally on each admissible Hassett divisor. The introduction and `cubics.tex` were read through the actual criterion and generic proof. The K3 association, categorical equivalence, Hilbert-square subfamily and integral diagonal consequences are already source consequences. The old r11 stable-rationality gap was read and excluded.

A natural arithmetic feasibility question is to find points over algebraic numbers satisfying the same pointwise criterion. Merely removing countably many proper closed sets over C cannot do this: those sets may contain every algebraic point. That tempting countability argument was not used.

The strongest compatible primary reduction is André, *Pour une théorie inconditionnelle des motifs* (1996), Theorem 5.2(3), together with §6.3 and Theorem 7.2. The actual proof of 5.2, including its arithmetic part, was read. For a family of motivated projectors over a number field and an étale chart to projective space, it gives a thin exceptional image and algebraic points outside the motivic-group drop locus. The proof passes to the l-adic monodromy image and invokes Serre's Hilbert specialization theorem. It is stronger than retaining only Picard rank. Section 6.3 makes Hodge realization fully faithful on abelian motives. Theorem 7.2, with its full cubic-fourfold proof, places the cohomology of smooth cubic fourfolds in that category, using the relative Kuga–Satake embedding and the Fermat fiber. Thus this controls Hodge tensors in endomorphism spaces as well as Hodge classes.

The compatibility check is as follows. On a smooth parameter chart dominating the marked Hassett divisor, use the full middle-cohomology motive (or its marked complement). The generic source calculation fixes the rank-two algebraic lattice and has scalar endomorphisms on its complement. At an André-generic arithmetic point the motivic group equals the generic group under parallel transport. Full faithfulness for the cubic's abelian motive identifies its invariant tensors with Hodge tensors. Thus the same rational Hodge classes and endomorphism space persist. The marking is primitive; equality of its rational span with the entire algebraic lattice gives the integral equality by saturation, and the source's unimodular-lattice calculation retains determinant d. The pointwise irrationality criterion then applies, with the same ineffective threshold.

One may spread the required parameter chart over a number field; the finite-type equations, level cover and cycle marking can be retained after extending that field. A way to justify the cycle marking without choosing an unproved arithmetic period correspondence is to use the Hilbert/Chow parameter spaces for the algebraic middle classes of cubic fourfolds, and a component dominating the divisor. The source already uses algebraicity of those middle Hodge classes. Countability and uncountability here serve only to locate a dominant finite-type parameter component; they do **not** select arithmetic points outside the Hodge exceptional locus. André supplies that latter step. No uniform field, explicit equation, or effective discriminant threshold is asserted in this screen.

The proposed integration therefore has an existing operation that preserves exactly the endomorphism data the source needs. It is not an additional research nominee. The original Serre proof and a fresh construction of an arithmetic marked moduli chart were not separately re-proved here; the point is the identified compatible primary theorem, not a claimed standalone new arithmetic paper. Stronger demands such as an explicit rational cubic over Q would need additional work and were not frozen.

Primary body: https://www.numdam.org/article/PMIHES_1996__83__5_0.pdf . The OCR has damaged symbols; theorem numbering and the operative prose are readable. Reading limits are recorded separately.

## 069: ordinary central torsors versus all lifting-gerbe sectors

The source's `thm:main` already retains every global form and connected component for a simple group. `equivalence:sectors` gives (character,component)→(component,−character), and `equivalence:central` supplies coherent isomorphisms on **full groupoids** of central torsors, not just their isomorphism classes. Its proof constructs section covers at colliding divisors, uniquely extends through formal thickenings, compares transgression using excision, and descends through localization. These entire central sections were read. Thus ordinary central equivariance, collision coherence and signs are paid operations.

The finite structural test was a diagonal central quotient. For H=(SL2×SL2)/diagonal(mu2), a pair of PGL2-bundles has lifting classes a,b in H²(X,mu2). Its lift to H requires a=b. This follows directly from the quotient homomorphism mu2×mu2→mu2, (z1,z2)↦z1 z2^(-1): the pushed-out lifting cocycle is a−b. The stack of choices of a lift, when nonempty, is a torsor under the groupoid of mu2-torsors. The sector a=b≠0 is therefore real data; a quotient of Bun(SL2×SL2) by central torsors reaches only a=b=0. Keeping automorphisms is essential even in the latter sector.

This small calculation is not a counterexample to a Langlands theorem, nor a nominee. It identifies why the naive product-plus-quotient construction does not yet give all components. The faithful tensor product of the simple-group equivalences does not by itself construct the requisite equivalence on every common nontrivial gerbe.

The strongest located primary operation is Bogdanova, *Quantum Betti geometric Langlands functor*, arXiv:2606.29585v1, §7 and Theorem 7.2.1. Its actual construction treats an arbitrary central gerbe, chooses a trivialization away from one point, replaces Ran by pointed Ran, and selects the matching affine-Grassmannian component and dual character summand. It then glues as a sheaf of categories over the gerbe 2-stack; Corollary 7.2.3 is its ordinary torsor-convolution consequence. The proof of 7.2.1 was read through its end, not inferred from the abstract.

That is the existing mechanism to try before calling the gerbe operation new. But its theorem is a **Betti functor** with its specified nilpotent-singular-support/spectral categories, while source069 is an equivalence of the full de Rham twisted D-module categories. I did not construct the gerbe-relative de Rham localization/period equivalences, prove that the primary pointed-gerbe argument satisfies all of those source contracts, or identify its completed output with every diagonal-quotient category. Ordinary Riemann–Hilbert terminology alone does not justify that transfer for all D-modules.

Accordingly this screen supplies neither a full central-quotient theorem nor a proof that the extension is unavailable. The exact unclosed interface is the full family of nontrivial lifting-gerbe fibers and its de Rham equivalence/descent, preserving all components. No zero-obstruction, Betti-only, product-only, or torus-only replacement is nominated. No broad reductive Langlands conjecture was frozen on the basis of this diagnostic.

Primary URL: https://arxiv.org/pdf/2606.29585v1 .

## Handoff

No independent review, formalization, manuscript, release-for-publication, shared-index edit, git operation, nested agent, contact, upload or browser UI was used. Public original notes and verifier code are separate from private source/primary bodies under their original rights. The packet seal authenticates these bytes; the controls are not mathematical gates. This bounded round found no candidate ready for a full-scope freeze. It does not claim that all arithmetic or algebraic avenues are exhausted.
