# Source058: deck-group linearity feasibility and compatible reductions

No frozen theorem. The following is a preselection calculation, not a submitted full proof or a mathematical verdict. All pinned source statements and operative proofs are stipulated true. Classical and external interfaces are compared at the reading extents below; they are not silently added to that stipulation.

The provisional full question was: for every connected normal projective complex variety X whose ordinary universal cover U is biholomorphic to a semialgebraic open subset of a projective variety, is there some finite N and an injective homomorphism pi_1(X) -> GL_N(C)? N may depend on X and every finite cover used. There is no dimension-only N, effectivity claim, freeness assumption on the source's intermediate action, or isotriviality assumption. No target of this form was frozen. This question is distinct from the normal compact-Kähler classification in arithmetic r17–r18.

## Actual source operations

Source058 main thm:main gives U = D x C^a x F, where F is simply connected, normal and projective. The stronger operative contract is in compact.tex, not just that unmarked product statement. Labels cmp:characteristic, cmp:albanese and cmp:affine-base construct the saturated integral relative Albanese data, its descended torsor, and a proper flat map j:U -> T=D x C^a with simply connected normal projective fibers. Gamma=pi_1(X) acts properly and cocompactly on T with finite stabilizers. A Gamma-invariant line bundle L is ample on the fibers. Groups.tex grp:compactifiable-cover and grp:kernel-abelian supply the virtually abelian kernel of the action on the bounded symmetric factor.

The proof of cmp:product preserves the polarization. The whole-fiber Chow parameter space, integral c1 marking, Pic^0(F)=0, cmp:closed-rigidity and cmp:polarized-locus first make every polarized fiber isomorphic. A sufficiently high power L_F^r embeds F in projective space. The resulting bundle has structure group G, the closed algebraic stabilizer of that embedded F inside PGL. Its principal G-bundle is trivialized over the contractible Stein T. This is substantially stronger than independently choosing arbitrary fiber identifications. No new singular-fiber Fischer–Grauert theorem is needed: the source already gives the Hilbert-orbit/base-change construction for normal singular fibers.

The bounded-domain companion paper's thm:main already allows finite stabilizers, initial affine singularities, and a proper cocompact action. Its hypotheses do not include a projective quotient. This strengthens the available geometric input but does not itself solve the old normal compact-Kähler relative-Albanese problem.

## Finite stabilizers: the actual compatibility calculation

Use the polarized trivialization, so a deck transformation has the form

    gamma(t,z) = (gamma t, g_gamma(t) z),   g_gamma:T -> G holomorphic.

Because T is connected, the component of g_gamma(t) in the finite group pi_0(G) is constant in t. The cocycle identity makes these components a homomorphism Gamma -> pi_0(G). Its kernel Gamma_0 has finite index. This uses a single polarized structure group for all deck transformations; arbitrary product trivializations alone would not justify it.

Suppose gamma in Gamma_0 fixes t. Properness of the action on T makes its stabilizer finite, so gamma has finite order. The element g_gamma(t) therefore has finite order in the connected linear algebraic group G^0. Over C such an element is semisimple and belongs to an algebraic torus. A torus acting on the complete variety F has a fixed point. One concrete version uses an equivariant projective embedding and a generic one-parameter subgroup: a limit of a point lies in a weight space, which is fixed projectively by the torus. The standard connected-linear-group maximal-torus theorem is used here; a fresh proof of that theorem was not read in this round.

Consequently gamma fixes a point of U, impossible for a nonidentity deck transformation. Thus Gamma_0 acts freely on T. This simultaneously removes the finite kernel of its T-action and all finite stabilizers. It does not use the false general implication that any finite-kernel extension of a linear group is automatically linear. Normal singular F is harmless to this fixed-point argument; completeness and the linear polarized automorphism group are the relevant hypotheses.

The quotient X_0 -> Y=T/Gamma_0 is then an F-bundle. The simply connected fiber identifies pi_1(X_0) with pi_1(Y). The projective quotient tower is already in Kollár–Pardon, arXiv:1104.2309v2, Remark 5, together with the compatible source relative-Albanese construction. The paper's Theorem 3 by itself has an irreducibility and dimension hypothesis; that theorem must not be misquoted as the unrestricted product statement. Remark 5 is the relevant stronger comparison. A separate full algebraization proof of the quotient via Chow cycles is not supplied here.

## Virtual abelian kernel without an unjustified splitting

At the level of the source's group contracts, let K be the virtually abelian normal kernel of Gamma_0 -> Lambda, the bounded-symmetric-factor action. The characteristic lattice K' in K is free abelian of finite rank r=2a and has finite index. Conjugation gives Gamma_0 -> GL_r(Z). The image of K in this representation is finite because K' centralizes itself.

Passing to the inverse image of the principal congruence subgroup of level 3 kills this finite image: that congruence subgroup is torsion free. In the resulting kernel K_1, the intersection with K' is central of finite index. Also Gamma_0 is torsion free: it acts freely on the finite-dimensional contractible manifold T, so it has finite integral cohomological dimension, whereas a nontrivial finite cyclic subgroup does not. Schur's theorem makes [K_1,K_1] finite; torsion freeness makes it trivial. Thus K_1 is free abelian. This is a compatibility calculation using classical group operations, not an effective presentation or a uniform-index assertion. The level-3 and Schur helper proofs were not newly read from their primary publications.

The source relative-Albanese/torsor operation with this full abelian kernel, followed by a torsion-free finite-index subgroup of Lambda, yields the abelian-family portion of the quotient tower. It is crucial to retain the whole family: Y -> B=D/Lambda can have nonconstant periods and nontrivial monodromy. Kollár–Pardon's Remark 5 explicitly warns that the smooth abelian family need not be a holomorphic fiber bundle. Replacing it by a fixed torus would be an unsupported strengthening.

## The strongest splitting operation is already available

Claudon, *Smooth families of tori and linear Kähler groups*, published 2018, Section 2.2, Propositions 2.1 and 2.2, gives the exact compatible operation. A smooth family of tori is a torsor with class eta in H^1(B,J(H)), for its Jacobian family. Projectivity supplies a multisection. Remark 2.3 identifies the degree of that relative cycle in the relative Deligne sequence and hence makes eta torsion. This is torsion of the holomorphic torsor class itself, not merely its image in H^2(B,H_Z).

If m eta=0, local multiplication by m glues to a finite étale map from the torsor to its Jacobian. Pulling back the zero section produces a finite étale multisection over B. A connected component is a finite étale cover of the connected base; after that base change the pulled-back family has a section. This operation applies to varying abelian families. The full operative proof through the relative-cycle argument was read. The weaker Kähler topological-class observation later in the paper is not substituted for it.

Since the base has contractible universal cover D, the homotopy exact sequence identifies the fiber lattice with the kernel of pi_1 of the family. The section splits the group extension. After finite étale cover the group therefore has the form Z^r semidirect Lambda_2, with an integral action rho. If sigma is a faithful finite-dimensional linear representation of Lambda_2, the direct sum of

    (v,lambda) -> [[rho(lambda), v], [0,1]]

and sigma(lambda) is faithful. The matrix product matches (v,lambda)(w,mu)=(v+rho(lambda)w,lambda mu). The second summand detects elements invisible to rho. The lattice Lambda_2 in the bounded symmetric automorphism group has the required linear representation after the usual finite-index component reduction. Induction of a faithful representation from a finite-index subgroup gives a faithful representation of the whole group. All dimensions and indices depend on the input. These observations do not force a direct-product decomposition.

## Disposition and limits

The finite-component/polarized fixed-point check is the most concrete calculation of the round. Combined with the actual quotient tower and the projective torsor multisection operation, it did not leave an identifiable unpaid operation for a fresh campaign nomination. This conclusion is a research selection decision, not a contribution rating or independent correctness PASS. No complete theorem is submitted, and no full worldwide literature clearance is claimed.

The old normal compact-Kähler extension remains untouched. It lacks the required normal-space relative-Albanese/all-fiber bundle descent in arithmetic r17–r18. A Kähler graph-volume estimate is already in the cited classical operation; merely changing projective to Kähler does not supply the missing descent. Structural r28's finite-volume bounded-domain question is also separate: its cusp calculation obstructs only prescribed compact normalization, not the full rigidity target.

Timing: initial source feasibility preceded the full r17–r18 checkpoint reads. Those reads, the actual primary quotient-tower/torsor proofs, and the final expanded alias search all preceded this extended note. Structural r28's screen was read late, after the alias search, before this note. No scope freeze occurred at any time.
