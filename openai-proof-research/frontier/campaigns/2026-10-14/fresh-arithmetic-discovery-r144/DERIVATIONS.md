# Arithmetic r144: multiplicative multipartition calculations

PREFREEZE. These are working derivations and operation comparisons, not a frozen theorem or an author-proof nominee. The source at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and all of its operative upstream proofs are stipulated true. The developed question is whether its invariant-theoretic multipartition construction and geometric comparison can be upgraded to an explicit multiplication between layers, compatible with flavor deformation and removal of auxiliary loops. The paid algebra isomorphism, its existing generality, and routine presentations are not candidates.

## 1. The actual source interfaces

Write G=product GL(V_i), N=sum Hom(V_i,V_j) over arrows plus sum Hom(V_i,W_i). A commuting flavor torus F acts on N. The character nu is regular in the source's exact sense: all nu-semistable points of the zero cotangent moment fiber are stable and G acts freely there. The empty locus is allowed. The coefficient ring is

    R = C[Lie(T) + Lie(F)]^W = H*(B(G x F); C).

Every linear parameter has cohomological degree two. The Coulomb algebra A_F is commutative BFN homology, WITHOUT the loop-rotation parameter. Its topological charge and cohomological grading are different gradings. The source identifies the two coefficient kernels, and hence

    H_F*(X; C) = R/I = A_F / <all nonzero nu-weight spaces>.

The last quotient is scheme-theoretic. Neither nilpotents nor the empty case may be discarded. No integral, positive-characteristic, derived, nonfree or singular quotient extension is being made here.

The entire 11-object canonical TeX/Bib closure was authenticated and read. The operative mechanisms are more than the headline:

* In `lem:correspondence-factorization`, bounded lattice chains realize neutral words as finite sheaf correspondences. Intermediate lattice ranks vary; their shifts telescope only at the neutral endpoint. Localization is faithful by parity and freeness of finite orbit strata.
* In `lem:stable-section-degree`, a global stable pair on P1 has nonnegative character-line degree. In degree zero, its G-bundle is uniquely trivialized using freeness. The finite critical test kills a nontrivial first modification of nonpositive degree. On the neutral component the critical graph has a global split quadratic normal form, and ordinary restriction onto D has an R-linear section. This proves the coefficient ideal inclusion in `prop:kernel-inclusion`, not just a comparison of dimensions.
* With one loop available at each vertex, `prop:laurent-model` cancels tangent denominators and constructs every dressed orbit sum by a squared-norm induction. `prop:filtration-bound` then eliminates zero-slot dressings with derivations and obtains cut-ideal symbol maps with exact degree shifts and Reynolds traces.
* `prop:cut-recurrence` proves the cut presentation through the reachable-open stratification. The incoming-coordinate Euler product is injective even over a nonreduced coefficient ring: its leading monomial in the new variables has coefficient one. Hausel's formula, with the ordinary/compact-support degree conversion made explicitly, turns the upper bound into equality.
* `lem:flavor-lift` uses cohomological freeness and a bounded-below graded Nakayama argument. `prop:loop-removal` compares both algebras near gauge zero and an added-loop mass equal to one. The Coulomb side inverts Weyl norms of added Euler factors; the Higgs side localizes the PREQUOTIENT fixed locus. Equality at the graded origin descends homogeneous coefficient ideals. It does not automatically transport any supplementary filtration.
* `prop:cocharacter-fixed` is separate. Polynomial Hall identities survive parameter specialization without inverses of arrow or rotation parameters. A rank-one framing vertex supplies complementary monopoles. Their hypothetical survival would produce at least two zero-weight indecomposable blocks and a positive-dimensional stabilizer after the ineffective scalar is removed. Regularity excludes this. No assumption that every bounded dimension vector has nonzero nu-weight is substituted for the actual argument.

These operations are already paid. The source additionally proves flavor base change and cohomological freeness over C[Lie(F)]. Standard restrictions of flavor, finite flatness of the fixed scheme over that ring, and the coefficient-compatible independence of regular stability therefore do not furnish a new nominee.

## 2. The exact module structure hidden in the symbol calculation

First assume no flavor and at least one loop at every positive-rank vertex. Delete one loop per vertex, as the source does. Let c_ij count the two directions of the remaining arrows, so c_ii is even. For a multipartition m of v, let d range over its positive slots, with color i(d) and size s(d). Put

    l_i = number of positive slots of color i,       n = sum_i v_i,
    P_m = C[x_d],       W_m = product_(i,s) S_(m_(i,s)),
    q_S = product_(d in S) x_d^(w_i(d))
          product_(d in S,e notin S) (x_d-x_e)^(c_i(d),i(e) min(s(d),s(e))),
    C_m = (P_m / (q_S: nonempty S))^W_m,
    delta_m = C(v)-D_m + w.(v-l).

The source's F_L is spanned by dressed orbit sums S_(lambda_m)(p) with |l|<=L, where lambda_m has entries s(d)-1, including -1 at the zero slots. The symbol map is

    direct sum_(|l|=L) C_m[delta_m] --> F_L/F_(L-1).

It is surjective. The summed Hilbert series equals that of B_0 by the full source proof. Each kernel has a nonnegative graded dimension, and there are finitely many layers. Therefore every displayed symbol map is an isomorphism. This is a direct consequence of the source's equality argument, not a new dimension theorem.

There is a useful stronger description of the coefficient action. Let p_(i,k)=sum_(a=1)^v_i x_ia^k. The zero-slot relation, including arbitrary dressing multipliers, is

    S_lambda(p [ sum_(positive d of color i) (s(d)-1)x_d^k
                 - sum_(zero z of color i) x_z^k ]) = 0.

Consequently p_(i,k) acts on the m-symbol by multiplication by

    psi_m(p_(i,k)) = sum_(positive d of color i) s(d) x_d^k.       (2.1)

This is an actual ring homomorphism R_0 -> P_m^W_m: replace the v_i roots by the multiset in which each x_d is repeated s(d) times. Newton relations are respected for all k, including k>v_i. Thus the symbol isomorphisms are isomorphisms of graded R_0-modules with these specified actions.

Multiplication by an R_0 coefficient preserves each F_L. Since R_0 surjects onto B_0, every F_L is an IDEAL of B_0. This proves only

    F_L F_M subset F_min(L,M).                              (2.2)

For D^a=F_(n-a), an honest multiplicative decreasing filtration would require

    D^a D^b subset D^(a+b),                                 (2.3)

which is stronger than (2.2). The source's vector-space filtration does not assert (2.3). Nor is an arbitrary splitting of its exact module sequences multiplicative.

The root vertex in every slot graph is fixed by W_m. Its cut products are precisely cocircuit products when the graph is connected; a disconnected unframed component gives the unit cut and zero quotient. RRT's actual construction identifies cocircuit quotients with slim-subgraph spaces as graded representations and identifies the latter with the power-ideal/orbit-harmonic representation. These are not identifications of their polynomial multiplication. In particular a set of break divisors is not automatically a spectrum for the cut algebra, much less for the extension between different m.

## 3. A complete rank-two calculation, with all g and w

This diagnostic is developed through its full algebra, rather than retaining an unspecified extension gap. Take a single vertex, v=2, g>=1 loops, w>=1 framing rows, trivial flavor and determinant stability. All conclusions here are source-derived calculations at this specified diagnostic scope, not a restricted substitute for an older full target and not a nominee.

Set

    a=g-1,   e=x+y,   f=xy,   Delta=(x-y)^2=e^2-4f,
    p_k=x^k+y^k,   p_0=2, p_1=e, p_k=e p_(k-1)-f p_(k-2).

All displayed polynomial degrees are half cohomological degrees: deg(e)=1, deg(f)=2. There are two multipartitions. The (2)-layer has length one, shift 2a+w, and is C[t]/(t^w), with

    e -> 2t,       f -> t^2.                               (3.1)

The (1,1)-layer is the invariant cut quotient

    C_11 = (C[x,y]/(x^w(x-y)^(2a), y^w(x-y)^(2a), x^w y^w))^S2.

Its kernel in R=C[e,f] is

    K = (Delta^a p_w, Delta^a p_(w+1), f^w).                (3.2)

Indeed C[x,y] is free over R with basis 1,x. Reynolds averaging an arbitrary multiple of x^w Delta^a gives an R-linear combination of Delta^a p_w and Delta^a p_(w+1); the swapped cut contributes the same invariant span. The remaining invariant generator is f^w. This argument proves the entire invariant ideal, not just inclusion of three polynomials.

To compute the extension, use Laurent variables T_1,T_2 in the source model. Its singleton representatives are

    r_(1,0)  = T_1 (y-x)^a (-x)^w,
    r_(0,1)  = T_2 (x-y)^a (-y)^w,
    r_(-1,0) = T_1^(-1) (x-y)^a,
    r_(0,-1) = T_2^(-1) (y-x)^a.

Their positive and negative orbit sums have nonzero topological charge and vanish in B. Their product before quotienting is the EXACT identity

    S_(1,0)(1) S_(-1,0)(1)
      = S_(1,-1)(1) + (-1)^(a+w) Delta^a p_w.              (3.3)

The same product with dressing x^k on the positive selected slot gives

    S_(1,-1)(x^k) = -(-1)^(a+w) Delta^a p_(w+k)  in B.     (3.4)

Write u=Delta^a p_w. Equation (3.3) identifies the cyclic length-one ideal with (u). The zero-slot derivation gives

    S_(1,-1)(h(x-y))=0   for EVERY polynomial dressing h.

Taking h=1 and h=x-y, and using (3.4), yields

    2 Delta^a p_(w+1) = e u,       Delta u=0.               (3.5)

The length-one cut is x^w. Because there is no lower nonzero layer, its relation is exact, so S_(1,-1)(x^w)=0. Iterating the first-power zero-slot relation gives

    e^w u=0.                                               (3.6)

The product of the positive and negative CENTRAL minuscule classes is f^w, up to the harmless framing sign; hence f^w=0 in B.

These relations supply the presentation

    B = C[e,f] / I,
    I = ( f^w,
          Delta^a (2p_(w+1)-e p_w),
          Delta^(a+1) p_w,
          e^w Delta^a p_w ).                               (3.7)

Here is why they are complete, including all parameter values g>=1,w>=1. We have a surjection Q=C[e,f]/I -> B. By (3.2), its kernel onto C_11 is generated as an R-module by u: the other cut generator becomes e u/2, and f^w is zero. Equations (3.5)-(3.6) make this cyclic module a quotient of R/(Delta,e^w)[2a+w], which has dimension w and Hilbert series q^(2a+w)(1+...+q^(w-1)). Therefore

    Hilb(Q) <= Hilb(C_11) + q^(2a+w)(1+...+q^(w-1)).

The source's two symbol isomorphisms say the right side equals Hilb(B). The surjection Q->B gives the reverse inequality in every degree. The presentation follows, and the cyclic kernel has exactly the stated module structure (3.1). No nonreduced factor was removed in this argument.

The product in that ideal is now determined as well. By (3.1), multiplication by u acts on it through

    psi_2(u) = ( (2t)^2-4t^2 )^a * 2t^w = 0

in C[t]/t^w. For a=0 the first factor is one, and the second factor is still zero. Thus

    (u)^2=0                                                 (3.8)

for every g,w in this diagnostic. In the special case w=1, (3.7) simplifies to f=0 and e^(2a+2)=0, so B=C[e]/e^(2g). Its lower ideal is generated by e^(2g-1).

Already g=w=1 gives a nonsplit R-module extension

    0 -> C.e -> C[e]/e^2 -> C -> 0,       f=0.

An R-linear section would send 1 to 1+b e and would have to be annihilated by e, but e(1+b e)=e is nonzero. This explicitly prevents replacing the filtered algebra by the direct sum of its coefficient modules. In particular the positive-degree square-zero ideal does not have its own identity element; it is not a unital algebra factor.

The retained dependency-free rational calculation tests (3.7) for g=1,...,4 and w=1,...,5, degree by degree through 2(g-1)+2w+4, and checks that u^2 belongs to the generated ideal. All 20 comparisons match. The dimension argument above is the general derivation; those finite calculations are diagnostics only. An initial SymPy attempt failed because the package was absent. No package was installed.

## 4. What the source already permits in arbitrary rank

It would be inaccurate to call multiplication in B uncomputable or to stop at a vague unknown presentation. There is a terminating source-based reduction for the looped no-flavor case.

For any nonzero neutral coweight lambda, choose its positive level-set indicator alpha=1_(lambda>0), and gamma=lambda-alpha. Because lambda is neutral vertexwise and nonzero, alpha has nonzero topological charge. The source's rearrangement argument makes the orbit of lambda the unique maximal squared-norm orbit in products S_alpha(p_alpha) S_gamma(p_gamma); all other orbits have smaller norm. The combined level blocks of alpha and gamma generate the dressing invariants of lambda, by the prefix power-sum argument. Any prescribed homogeneous dressing can therefore be realized by a finite sum of such products, with exactly that leading dressing. In B every product is zero because its alpha factor has nonzero charge. This expresses S_lambda(p) by finitely many lower-norm neutral orbit sums. Repetition reaches lambda=0.

This is termination in a nonnegative integer norm. It does not require denominators in gauge variables, and homogeneous dressings keep the cohomological degrees consistent. Multiplying two explicit orbit sums first gives finitely many terms by the Laurent multiplication formula. The reduction then returns coefficient-polynomial representatives. It does NOT establish the additional reverse-length bound (2.3): intermediate coweights can have entries below -1, and norm decrease is not the desired length inequality.

There is even a routine finite elimination route. For every minuscule coweight, its stabilizer-invariant dressing ring is a finite module over R_0 (products of symmetric polynomial rings over their full symmetric ring). Choose finite homogeneous module generators. The corresponding finite collection of dressed orbit sums, together with the elementary symmetric coefficients, generates A_0. Each is an explicit Laurent polynomial in finitely many variables x_d,T_d. Introduce T_d inverse variables and equations T_d U_d=1. The kernel of the map from a polynomial algebra on these generators is an elimination ideal in this finite polynomial ring. Add equations killing all nontrivial minuscule generators and eliminate again. This computes the coefficient ideal and all products for each input, with no assertion of an efficient complexity bound.

Such finite elimination or a collection of multiplication matrices is routine presentation bookkeeping already available from the source. It is not the sought nonroutine operation. The sharper direction would relate the SPECIFIED multipartition symbols and their cut geometry to a uniform product rule and geometric filtration, with the required flavor and loop-removal compatibilities. Neither a finite algorithm nor the source's Hilbert-series equality supplies that geometric comparison.

## 5. Flavor deformation: an explicit obstruction and a compatible alternative

The first nontrivial example tests the proposed lift before any theorem freeze. Take g=w=1,v=2, and let H=C* scale the loop with weight one, with parameter z of cohomological degree two. Its cotangent partner has weight minus one. The Higgs variety is Hilb^2(A2). The center-of-mass factor is equivariantly contractible. The centered factor is the minimal resolution of A2/{+1,-1}, equivalently Tot O_P1(-2), and retracts equivariantly onto the exceptional P1. The two tangent-coordinate weights are z and -z. The tautological rank-two bundle has an invariant constant section and a quotient line of these two weights (switching the dual convention switches both signs and leaves the relation unchanged). The equivariant projective-bundle relation therefore gives

    B_H = C[z,e,f]/(f, e^2-z^2).                            (5.1)

This can also be read from the two fixed length-two monomial ideals: the tautological roots are (0,z) and (0,-z). The geometric retraction/projective-bundle calculation establishes the entire algebra; fixed-point values alone would not have justified an integral coefficient presentation. Formula (5.1) is a familiar Hikita special case used as a test, not a nominee.

At z=0, the length-one ideal is (e) and its square is zero. Over C(z), (5.1) becomes the product C(z) x C(z), so every square-zero ideal is zero. If an S=C[z]-flat submodule J of B_H had J/(z)J=(e) and J^2=0, then J tensor C(z)=0. But J is a submodule of the torsion-free S-module B_H, so J=0, a contradiction. Thus an unchanged square-zero multiplication law cannot have the required flat lift, even here.

This is NOT an obstruction to every flavor-compatible construction. In fact the ideal

    J_+ = (v),        v=e-z,
    e v=-z v,        v^2=-2z v                              (5.2)

is a free rank-one S-module and has free rank-one quotient, obtained by e=z. It specializes to the desired ideal. Choosing e+z gives the other branch. The same module flag can therefore lift with a deformed product. At nonzero z, division by -2z turns v into an idempotent; division is not allowed at the special fiber. A proposed uniform construction must retain precisely this distinction.

The tempting invariant lift (e) has quotient S/(z^2), which is not S-flat. The ideal itself is free of rank TWO, generated over S by e and z^2. Its fiber modulo z therefore has dimension two, but its image in B_H/(z) has dimension one. The lost generator is the Tor phenomenon from the nonflat quotient. Hence mere image specialization of an ideal is not a flat filtration lift.

This example also checks the source's loop removal. Removing the only loop gives the no-arrow theory with v=2,w=1, whose determinant-stable locus is empty: a single incoming framing vector cannot generate a two-dimensional space without arrows. At the localization used by the source, e=f=0,z=1, the relation e^2-z^2 is a unit and (5.1) becomes zero. The two generic supports e=+z and e=-z are discarded by that gauge-origin localization. This is fully compatible with the source. It shows why a vector-space decomposition at zero mass cannot simply be followed unchanged through that localization and homogeneous descent.

## 6. Strongest actual primary comparison and the remaining interface

The comparison uses proof bodies, not titles or abstracts.

[Dumanski–Krylov v2](https://arxiv.org/abs/2509.06226v2), §§2.2–2.3, localizes the stable prequotient and the BFN triples at semisimple gauge/flavor parameters. The residual representation is another quiver theory. Its §3.3 constructs a Todd-corrected Riemann–Roch map on bounded pieces and then takes the colimit of their completions; this is not an unspecified completion of an infinite direct limit. Its §§4.2–4.4 compare fixed quotients at all coefficient completions and recover global coefficient ideals. Thus the nonquantized K-theoretic transfer in Theorem 4.13 is a paid conditional-on-the-residual-theories operation. We do not nominate its composition with a verified instance of the source, and we do not assert its unrestricted application to every regular inherited stability without checking that interface. It supplies no transport of the particular F_L flag or chosen square-zero extension. The quantized statement is separate.

[Reineke–Rhoades–Tewari v2](https://arxiv.org/abs/2207.11861v2), §§2–3.3 and 4.1–4.4, gives the cocircuit/slim-subgraph representation, the break-divisor orbit-harmonic proof, and the symmetric-quiver/toric-cohomology identification. The power ideal and cocircuit ideal are different constructions. Their equality of representation characters does not supply multiplication between source multipartition layers. The two fonts were checked on the rendered PDF page 5.

[Jindal–Negut v1](https://arxiv.org/abs/2607.23544v1) supplies polynomial shuffle generation, loop-nilpotent BPS generation, and strictness of the inclusion into the full CoHA with its own perverse filtration. Its actual companion [K-theoretic Hall algebras v1](https://arxiv.org/abs/2605.19487v1), §5, constructs generators by a descending partition specialization, including the cross-factor divisibility and the additional factors forced by vanishing on larger partitions. Its §6 uses nilpotent Jordan strata, torsion-freeness, and Zhao's punctured affine-space test. These are stronger than a bare generation statement and were followed where the cohomological paper sketches the analogous proof. The companion [BPS/perverse paper v2](https://arxiv.org/abs/2604.00124v2), §§3.5–3.6, Proposition 3.15 and §§3.10–3.11, makes the strictness argument explicit: injectivity on primitive BPS pieces yields injectivity on the symmetric associated graded. None of these maps is automatically the quotient onto the source's length filtration.

To use this stronger Hall mechanism for the developed operation one would need a specified map from its filtered objects to the neutral, fixed-scheme quotient, with an identification of its induced filtration with the F_L defined by the actual source orbit sums. One must then prove that the relevant kernel and the induced products have the required filtration behavior, including zero rotation and arbitrary arrow/flavor specialization. Generic injectivity or abstract PBW decomposition does not establish that. In the flavor example, insisting on the undeformed law is actually false; a workable construction must instead explain the deformation in (5.2), its choices, and its compatibility with removal of loops.

The exact unpaid bridge is therefore not generic freeness, a missing numerical dimension, the existence of some algorithmic product, or an unperformed rank-two computation. It is a uniform geometric/product comparison for these particular layers that survives the specified deformation/localization operations. No such construction is completed here. Its special cases and the explicit obstruction above are not substituted for it.

## 7. Scope decision and history compatibility

No viable substantial full-scope operation has closed, and no theorem has been frozen. Formula (3.7), its square-zero ideal, and the finite all-rank reduction are retained because they close concrete algebraic reductions. They are source/classical consequences and are not promoted to nominees. Formula (5.1) rules out one precise undeformed flavor lift, while (5.2) expressly preserves a compatible deformed alternative. No general impossibility follows.

The bounded eligible original-history searches found no operative Hikita/quiver-cohomology predecessor. The literal Hikita lead in completed structural149 was the unrelated chromatic symmetric-function work, and its three original sections were read completely; it supplies no mathematical premise here. The actual i07 extension-cocycle section, structural19 module-realization comparison, structural41 equivariant attachment construction, and arithmetic58 integral-cycle full scope were read as adjacent-interface controls. Their domains differ. In particular equality of a quotient or a representation is not a construction of the extra extension, module realization, integral lift, or fixed-point compatibility required by those old targets. No old scope or disposition is altered. The coarse path exclusions omit genuine historical material, so absence of an eligible hit is not clearance.

The exact completed arithmetic143 originals preserve the paid projective K3 rank-four construction and rank-two obstruction, the nonsplit rank-three two-jet equation with its quadratic extension term, and the limited split-negative obstructions on two models. They have no bearing on the Hikita deductions. R98/E98/P98/S98, i102/i74/i80, r142, the supplied fixed-determinant P=W/variant, integral-cycle, relative/deformation and uniformity scopes, S176A's undischarged condition, and every other supplied disposition stay unchanged. No peer body was used to certify any of this.

This is PREFREEZE/no nominee, not an exhaustion claim, an assertion of worldwide novelty, a mathematical self-grade, or an acceptance/count decision.
