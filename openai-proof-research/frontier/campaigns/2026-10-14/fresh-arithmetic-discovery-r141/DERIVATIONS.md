# Arithmetic r141: prefreeze derivations

Codex / GPT-6 Astra / high / default service tier. All pinned source proofs are stipulated true. These are discovery calculations, not a frozen statement, author manuscript, correctness/contribution grade, or campaign count.

## 1. Operative source, before deduction

All twelve canonical TeX bodies were authenticated and read. The rational relation of thm:chow-relation is an identity of correspondences, not merely a numerical identity. The marked Hilbert recursion leaves two outputs unintegrated, with graph components joining the outputs producing the diagonal. The nonrank branch constructs an effective pair and a negative orthogonal class after at most three blowups; the rank-one branch compares actual determinant-fixed fibers on the Cartwright–Steger surface and computes the middle coefficient 12. Torsion twists are retained in the effective-pair count. Source truth is stipulated, not audited.

The integral conclusion uses Roitman only over the complex field. The irregular case is genuinely the Bloch–Kas–Lieberman mechanism: elliptic multisection/Jacobian transfer and quotient averaging, followed by divisibility of the complex Albanese kernel. These are distinct from a universal integral Chow assertion. The source already proves t2(S)=0 for every pg=0 surface and pure rational Tate motives for q=0, all powers, and all Hilbert schemes.

The strongest primary operations read before this durable development include Kahn's complete arXiv v4 proof and appendix, the published Section 6 and appendix A.1 proof, Sato–Yamazaki's published integral projectors and torsion-order comparison (Section 3), KMP's actual surface projectors and generic-point/Albanese mechanism, and the complete main proofs of BKL and Bloch's Roitman theorem. The scanned BKL and Roitman proof pages were recovered visually because text extraction omitted formulas. Exact limits are recorded privately. No new theorem has been frozen.

## 2. Integral projector for every regular source surface

Let S/C be any smooth connected projective surface with pg=q=0. Put T=NS(S)_tors and e=exp(T), with e=1 if T=0. Choose o in S(C) and divisors D_1,...,D_r lifting a Z-basis of NS(S)/T. The exponential sequence identifies Pic(S)=H^2(S,Z). Poincare duality makes the free intersection matrix Q=(D_i.D_j) unimodular. Let (q^{ij})=Q^{-1}, with integral entries.

Use correspondence action Z_*(z)=p2_*(p1^*z.Z). Define

    P0=S×o, P4=o×S, P2=sum_(i,j) q^{ij} D_i×D_j,
    P=P0+P2+P4, E=Delta_S-P.

Composition of two divisor products is

    (D_a×D_b) o (D_i×D_j)=(D_j.D_a) D_i×D_b.

Thus P2^2=P2. The degree-one point makes P0 and P4 idempotent. Their cross-compositions and compositions with P2 vanish, by dimension and proper pushforward. Consequently P^2=P, E^2=E, PE=EP=0, integrally. No division by an intersection determinant is hidden here.

The source's rational cycle-class isomorphism for S^2 says E_Q=0: its rational cohomology class is zero. Thus E is torsion in CH^2(S^2). The integral cohomology class of E is killed by e. To see this without identifying torsion with a free lattice, H^1(S,Z)=0, H^2(S,Z)_tors=T, H^3(S,Z)=T^vee, and H^0,H^4 are free of rank one. The integral Kunneth exact sequence for H^4(S^2,Z) splits as abelian groups. Every torsion tensor or Tor term is killed by e. The rationally zero class cl(E) therefore has e cl(E)=0.

Kahn, published Corollary 6.4(a), gives injectivity of the codimension-two cycle map after tensoring with the product of all Z_l. A torsion element which vanishes there vanishes integrally: tensor the injection of its finite cyclic subgroup, using flatness, and detect it modulo its order. Therefore

    e E = 0 in CH^2(S×S).                                      (2.1)

This is also the effective torsion-motive conclusion in Sato–Yamazaki, Proposition 3.6(2), following their integral projector construction. It is a PRIMARY PAYMENT, not a new discovery. It is stronger than merely clearing the denominators in the source Quot relation. It does not imply E=0 if e>1.

## 3. Universal action and sharpness

Flat base change carries (2.1) to every extension F/C, with no algebraic-closedness assumption on F. On zero-cycles P2 and P4 act as zero by dimension, while P0 sends z to deg(z)o_F. Hence

    e (z-deg(z)o_F)=0 for every z in CH0(S_F).                   (3.1)

This conclusion does not use divisibility or Roitman over F. In particular degree is universally an isomorphism when T=0. Conversely a coefficient-one universal decomposition would force T=0; Kahn's published Corollary 6.4(b) says the exact order of eta_S-o in CH0(S_C(S)) is e. The universal exponent in (3.1) is therefore sharp for the fixed S, even though A0(S_C)=0. No common numerical bound over all surfaces is asserted.

This corrects the tempting but unpaid shortcut from the complex-point headline: a universal exponent is available, but its exact value comes from Kahn's integral operation, not from applying complex Roitman to a nonclosed field.

## 4. Products: carry the same projector all the way

For arbitrary m>=1 and regular source surfaces S_1,...,S_m, choose their P_i,E_i as above and let e_i=exp(NS(S_i)_tors). For a subset I of {1,...,m} set

    Q_I = tensor_(i in I) E_i tensor_(i not in I) P_i.

The Q_I are mutually orthogonal integral idempotents and sum to Delta_X for X=product S_i. The empty-subset projector is a sum of integral Tate projectors. Every nonempty Q_I is killed by each e_i with i in I, hence by gcd_(i in I)e_i. With L=lcm_i e_i,

    L (Delta_X - tensor_i P_i)=0.                              (4.1)

The same identity holds over every F/C. Every Tate summand of positive twist has zero CH0 over a field, so tensor_i P_i acts on CH0(X_F) by z -> deg(z)(o_1,...,o_m). Thus L annihilates A0(X_F) for EVERY extension F/C. The projection X->S_i has the section inserting the other basepoints. These maps split A0(S_i,F) into A0(X_F); taking F=C(S_i) shows every universal annihilator is divisible by each e_i. Hence the exact universal exponent for this product is L, not the product of the e_i.

In particular all powers of a fixed S retain exponent e. This is a fully carried construction, but the lcm follows from the paid integral projector by distributivity of tensor product and split projections. It is not nominated as a nonroutine theorem. It does not determine every torsion Chow group of a product or give a full integral Hodge theorem: those would discard the nonzero tensor summands Q_I.

## 5. The irregular interface: a single bounded inverse, not pointwise division

Now let S/C have pg=0, with arbitrary q, let o be a complex point, and write a:S->A=Alb(S), normalized by a(o)=0. For every extension F/C let alpha_F:A0(S_F)->A(F) be the cycle Albanese map, including residue-field traces. Here is a concrete way to keep all denominators uniform in F.

Choose a smooth ample connected curve i:C->S with c0 in C(C). The induced f:J(C)->A is surjective. There is a homomorphism s:A->J(C) and an integer m>0 with fs=[m]. One construction chooses a polarization on J(C), takes the connected orthogonal complement of ker(f)^0, and uses the resulting isogeny to A. An isogeny of degree d has an inverse in Hom tensor Q; clearing its finite kernel gives the stated integral s and m. No surjectivity on F-points of an isogeny is being used.

The normalized Poincare bundle on J(C)×C, pulled back along s×1 and then pushed along i, defines

    beta_F:A(F)->Pic^0(C_F)=A0(C_F)->A0(S_F).

The rational point c0 ensures that Pic^0(C)(F) really is represented by degree-zero line bundles on C_F, without a Brauer descent obstruction. The biextension identity makes beta_F additive. Functoriality of Albanese gives

    alpha_F beta_F = [m] on A(F).                              (5.1)

This already kills coker(alpha_F) by m. It does not prove surjectivity of alpha_F.

Pull the same Poincare class back along a×1_C and push to S×S. Call the resulting integral codimension-two correspondence G. Its action on A0(S_F) is beta_F alpha_F, and its restriction at o is zero. The KMP rational surface decomposition, with the source's t2(S)=0, identifies the birational motive with 1 plus h1(S). The endomorphisms of h1 are the homomorphisms of A up to isogeny. Consequently the correspondence

    R = m(Delta_S-S×o)-G

is zero in the rational birational category: it is zero on the degree summand by normalization, and on h1 by (5.1). The possible map from 1 to h1 is removed by the restriction at o; the map from h1 to 1 is zero by degree. Thus no off-diagonal summand is being discarded. This uses the actual generic-point description, not the vanishing of R on complex closed points. It gives an integer n>0 for which nR restricts to zero in CH0(S_C(S)). Integral localization then gives a proper closed subset D of the first S with nR represented by a cycle supported on D×S. Enlarging D to a divisor is harmless.

For any F/C, the zero-cycle moving lemma moves a representative away from D_F. Thus this supported correspondence acts by zero. On A0(S_F) we obtain the SAME identity for ALL F:

    nm z = n beta_F alpha_F(z).                                (5.2)

In particular nm kills ker(alpha_F); m kills its cokernel. Restriction in F commutes with all the constructions. For finite extensions the proper-pushforward/projection formula gives the corresponding trace compatibility. The integers depend on S and the chosen splitting but not on F or z. Both equations are integral, after the one finite clearing n. A statement that every element is torsion with an element-dependent order would be strictly weaker than (5.2).

This reduction is fully paid by the rational surface projector, the generic-point/localization operation, and the curve Jacobian splitting. KMP's actual description of pi1 as a divisor on S×a normalized curve, including its correction term on curves×curves, explains why the factorization is legitimate. The preceding explicit beta construction avoids treating a rational projector as an integral projector. It supplies no effective or optimal n and no coefficient-one universal Albanese assertion. It is not a new nominee.

## 6. Nonclosed descent: carry restriction and corestriction exactly

Let k have characteristic zero, X/k be a smooth projective geometrically connected surface with geometric pg=q=0, X(k) nonempty, and trivial Galois action on NS(X_bar)/tors. Write e for the exponent of geometric NS torsion. These hypotheses are maintained explicitly; this is not an assertion about an arbitrary form with a chosen point silently adjoined.

The complex source conclusion extends to algebraically closed characteristic-zero fields for this purpose by spreading the finite surface and zero-cycle data to finite type over Q, embedding a field of definition into C, and specializing finite rational-equivalence data to algebraically closed fields. This is the standard finite-data change-of-universal-domain argument also used in KMP's generic-point proof, not an embedding of an arbitrary enormous field into C. Hence A0(X_bar)=0, and A0(X) is the kernel of restriction on CH0.

Colliot-Thelene's published appendix to Kahn, Theorem A.1(a), gives e2 e3 annihilation of this restriction kernel. For these surfaces e2=e3=e, so

    e^2 A0(X_F)=0 for every extension F/k.                      (6.1)

Indeed the point, trivial free-lattice Galois action, and geometric Betti hypotheses persist under F. The exponent remains geometric e. This bound is already primary mathematics; the source supplies its full geometric hypothesis in the regular pg=0 case. The same appendix proves the necessary bounded torsion rather than merely elementwise torsion.

Without the point or split free lattice over k, choose ONE finite extension L/k of degree d over which both hold. Such an extension exists: a closed point has finite residue degree, and the continuous Galois action on the finitely generated free NS lattice has finite image. For any F/k write the finite etale algebra L tensor_k F as product_j F_j. Applying (6.1) on each factor and summing corestrictions yields

    sum_j cor_(F_j/F) res_(F_j/F) = sum_j [F_j:F] = d,
    d e^2 A0(X_F)=0.                                           (6.2)

This is uniform in all F, including extensions intersecting L, since the sum of the factor degrees stays d. No division by d is valid integrally. It does not make the degree map surjective when X lacks a degree-one cycle.

The actual descent proof shows where a possible improvement would have to operate. Set

    U = H^1(k, K2(kbar(X))/H^0(X_bar,K2)),
    V = H^1(k, H^1(X_bar,K2)).

There is an exact sequence U -> A0(X) -> V. Under the point and split-lattice hypotheses, the appendix injects U into H^2(k,H^2(X_bar,Zhat(1))_tors) and V into H^1(k,H^3(X_bar,Zhat(2))_tors); in particular eU=eV=0. (The actual injections apply to these groups as identified in the proof; the first follows through the K2 Hilbert-90 sequence.) For z in A0, e z is an image of U, and then e^2 z=0. The missing operation for the tempting e-bound is precisely

    e A0(X) = 0, rather than only e A0(X) contained in im(U).

The information on the two ends does not settle that assertion. The abstract extension 0->Z/e->Z/e^2->Z/e->0 exhibits the logical issue when e>1. This is not a geometric counterexample, and there is no claim that this extension is realized by X. To close an improvement one would need a geometric splitting, an annihilation of the image reached after the first multiplication, or a separate integral correspondence descending with coefficient e. None was constructed here.

An attempted projector descent makes the same obstruction visible. Even when all divisor classes lift over k, a geometric identity eE_bar=0 does not imply eE=0 over k. Restriction of rational equivalence can lose descent information; averaging after a finite extension costs its degree. Cohomology alone cannot remove this degree. The stronger e bound in Sections 2–4 uses a constant complex surface and Kahn's algebraically closed-base correspondence result, and cannot simply be pasted into (6.1).

## 7. Specialization of the actual identity

Let R be a DVR, and let X/R be smooth projective of relative dimension two. Suppose its generic fiber has an ACTUAL integral relation a(Delta-P)=0, with P built from a degree-one point and divisor products as in Section 2, and with these data extended over R. For the product model, lift the zero generic class to a cycle class. Localization makes its lift vertical; Gysin to the special fiber kills that ambiguity because the fiber is principal and its normal line is trivial. Gysin respects rational equivalence, proper pushforward and divisor intersections. Thus a(Delta_special-P_special)=0. Acting after ANY residue-field extension kills a A0 of that fiber.

This includes residue characteristic dividing a: no etale prime-to-p argument entered. If the identity only becomes defined over a finite generic extension, these statements apply over its valuation rings; descent back retains the trace degree. Fiberwise complex-point vanishing alone has not supplied the assumed relation over R. No common relative projector over an arbitrary base, choice-free specialization of Albanese inverses, or uniform family denominator is asserted. The Stacks proofs of Cartier Gysin and rational-equivalence compatibility were read before writing this section.

## 8. Outcome of the integrated construction

The calculations retain three different quantities: geometric e for regular constant surfaces, the actual denominator nm of a rational Albanese inverse, and the descent factor d e^2 for forms. Their roles cannot be interchanged. For products of regular constant surfaces, the exact lcm survives all field extensions; it follows by a routine tensor calculation once the strongest primary integral projector is applied. For smooth specialization, an existing integral identity already does the work. For irregular surfaces, (5.2) supplies a common bounded kernel, but not a new optimal integral formula. For nonclosed forms, the primary proof carries the construction to the explicit U-to-A0-to-V extension above.

No nonroutine bridge beyond these source/primary operations has been closed. No viable distinct full theorem was frozen, and no author proof is submitted. The disposition of this discovery packet is PREFREEZE / no nominee. This records a local failure to find the requested additional operation, not a worldwide novelty or exhaustion assertion, and not a counterexample to an enhanced statement.

The original r58 integral Chow/lattice target is unchanged: replacing its arbitrary abelian varieties/all codimensions/all good-place requirements by rational cycles on surfaces would not resolve it. No older scope, disposition, review condition, or campaign count is changed here.
