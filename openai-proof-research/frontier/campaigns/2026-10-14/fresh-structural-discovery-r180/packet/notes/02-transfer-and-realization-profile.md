# r180: full finite-group reduction (paid composition, no nominee)

Notation and hypotheses are those authenticated in note 01. The arguments below were developed after reading the operative primary and original-history bodies. They are elementary finite-group consequences of the source, retained to avoid stopping at its advertised pair or mistaking a routine amplification for the remaining campaign result.

## 1. Recovering A inside F by finite-order lifts

Let T be the set of x∈F having a finite-order lift in Aut(Π). Full-preimage equality E=preimage(F) matters: a lift cannot evade the source's obstruction by lying outside E. Projecting E→H shows T⊂A×{0}. The generating panel reflections show (a_s,0)∈T for every s. Thus

    ⟨T⟩=A×{0}.

Conjugation in O preserves T whenever it preserves F. Indeed choose a representative automorphism of Π and conjugate a finite-order lift by it; the result is again a finite-order lift of the conjugate outer element. Therefore N_O(F) normalizes ⟨T⟩=A. The source equality N_O(A)=F now gives

    N_O(F)=F.                                                   (2.1)

This does not assert that every element of A has a finite-order lift. Only spanning is needed.

Take a Sylow 2-subgroup S of O containing F. A proper subgroup of a finite p-group is properly contained in its normalizer. If F<S, this would contradict N_S(F)⊂N_O(F)=F. Hence F itself is Sylow and |O|_2=2^{n+1}.

## 2. Trivial fusion and the odd normal kernel

Here is the subgroup form of the fusion calculation, rather than just the element version. Suppose P≤F and gPg^{-1}≤F. Put Q=gPg^{-1}. Both F and gFg^{-1} lie in C_O(Q), because F is abelian, and both are Sylow 2-subgroups of that centralizer. Choose c∈C_O(Q) with cgFg^{-1}c^{-1}=F. Then cg∈N_O(F)=F. For every p∈P,

    gpg^{-1}=c(gpg^{-1})c^{-1}=(cg)p(cg)^{-1}=p.                 (2.2)

In particular, two subgroups of F conjugate in O are equal, and any such conjugation is pointwise the identity on the subgroup being conjugated.

One can also compute the transfer directly. Choose a right-coset transversal for F in O and let

    τ:O→F,  τ(g)=∏_{Ft∈F\O} t g t_{Ftg}^{-1}.

The factors lie in F. Since F is abelian, changing the transversal cancels its factors pairwise and the cocycle formula proves τ(gh)=τ(g)τ(h). For x∈F, group the cosets into x-orbits. An orbit of length d contributes a conjugate in F of x^d. By (2.2) that factor is exactly x^d. Consequently

    τ(x)=x^{[O:F]}=x,

since [O:F] is odd and F has exponent two. Thus K=ker τ is a normal odd-order subgroup, τ is a retraction, and

    O=K⋊F.                                                      (2.3)

This is Burnside's classical transfer argument, not a new operation. The actual transfer proof in Flavell's 2007 author notes, §§2–3.8, was read, but those notes are not mislabelled as Burnside's original publication. The direct calculation above removes dependence on an unread historical original. No solvability or triviality of K is claimed. In particular, N_O(F)=F does not imply O=F.

## 3. A canonical profile for every manifold model

Let X be any closed topological four-manifold with a homotopy equivalence f:X→Q2. Write R_X≤O for the image of all self-homeomorphisms under this marking. This is an image subgroup; it is not assumed to be a simultaneous finite group action on X.

The source cyclic argument applies to this very model and marking. It excludes δ∈R_X. Replacing f by an arbitrary self-equivalence of Q2 composed with f excludes every O-conjugate of δ from R_X.

For any subgroup R≤O, ker(τ|R)=R∩K has odd order. Therefore τ(R) is a 2-subgroup and its order equals the full 2-part of |R|. If S_R is Sylow in R, τ maps S_R isomorphically to τ(R). Conjugate S_R into F. Transfer is invariant under conjugation (its target is abelian), and τ|F=id, so the conjugated subgroup is literally τ(R)≤F.

Apply this with R=R_X. If δ∈τ(R_X), a conjugate of δ would lie in R_X, impossible. Projection F=A×F2→A is therefore injective on

    P(X):=τ(R_X).

There is a unique subspace U(X)≤A and unique linear functional ε_X:U(X)→F2 with

    P(X)={(a,ε_X(a)):a∈U(X)},    dim U(X)≤n.                    (2.4)

P(X) is independent of a change of marking by any element of O: R changes by conjugation and τ is conjugation invariant. A homeomorphism between two models likewise forces equality of their profiles in the common source coordinates. This is a necessary invariant; completeness is not asserted.

For the source's Mε, actual Bε-actions give Bε⊂R_Mε and hence Bε⊂P(Mε). Since Bε has dimension n while (2.4) bounds the profile by n,

    P(Mε)=Bε.                                                   (2.5)

It follows that all 2^n linear source models are pairwise nonhomeomorphic, not just distinguished as marked structures. This conclusion is a source/classical amplification and is NOT submitted as a nominee. The calculation also does not determine R_Mε: it can contain an odd-order kernel inside K.

## 4. What this reduction leaves open

For any constructed model, an explicit subgroup of coordinate translations gives a lower bound on P(X). The bound dim P(X)≤n becomes exact for the source linear models because their lower bound already has dimension n. For a model with a smaller explicit translation subgroup this argument has no equality step. One cannot declare the explicit translations to be the Sylow image, nor manufacture an action of a larger profile from individual homeomorphisms. Note 03 tests this point on a fully specified nonlinear family.
