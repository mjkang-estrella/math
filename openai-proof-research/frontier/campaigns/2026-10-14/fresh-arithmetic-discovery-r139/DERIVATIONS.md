# Arithmetic r139 — prefreeze derivations

Provenance: Codex / GPT-6 Astra / high / default service tier. Source209 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, including every operative proof, is stipulated true. No frozen discovery statement, mathematical self-grade, acceptance or count. These are feasibility calculations and strongest-reduction comparisons, not a manuscript.

## 1. Source payment and the distinct direction examined

Both entire canonical TeX/Bib families were authenticated and read before these notes. Write G3 for the degree-three manuscript and G5 for the degree-five manuscript. G3 constructs its integral lift on the horizontal divisor: coefficient boundary is the Steinberg product {zeta,t}=5{eta,1-eta}=0, then K2(F5)=0 supplies extension over the DVR. Proper support kills generic restriction integrally. Its arbitrary omitted-point classes are ALL tested using the actual field isomorphism beta·[-]:E*/E*5 -> K3(E;5), the projection formula, and the residue-degree norm identity. G5 separately supplies a global integral K5 cyclotomic lift, exact parenthesized Bott operations, the arbitrary-localization Picard specialization criterion, and the signed quartic orbit. Neither finite coefficient detection says that the integral kernel class is torsion or rationally nonzero.

The investigation asks how much independent integral kernel data can be realized on ONE regular local surface. Merely adjoining variables, substituting primes/degrees, or renaming the old even-degree G4 target is not the requested distinct operation. The completed original G4 scope was read and remains immutable; it asks for a two-dimensional integral K4 counterexample with no restrictions on construction. It is not pursued here.

## 2. Full same-ring rank amplification: prefreeze feasibility

This section carries the geometric route concretely; its source and classical ingredients are credited. Put s>=1, d=5^s-1, N=d/4, f=3^s-2, and

    M_f = |GL_f(F5)| = product_(j=0)^(f-1) (5^f-5^j),
    n=2s M_f, k=F_(5^n), V=W(k), H0=Frac(V).

The numbers are finite explicit integers, not a feasible computational prescription at large s. Both d and N are prime to5. The field k contains mu_(2d), since 2s divides n and 2d divides 5^(2s)-1. Consider

    D: X^d+Y^d=Z^d,
    H: w^2=z^d+1,
    h:D -> H, z=X/Y, w=(Z/Y)^(d/2),
    J=Jac(H).

The degree of h is d/2, prime to5: over the function field of H it adjoins v=Z/Y with v^(d/2)=w. The valuation of w at each simple zero is1, so this extension has full degree d/2. Both curves are smooth, geometrically integral; H has genus d/2-1 and D has genus g_D=(d-1)(d-2)/2. Choose a branch point o of H over k. Hyperelliptic involution acts as negation on the Abel map a(R)=[R-o] into J, since R+ιR is linearly equivalent to2o. Every branch point has 2-torsion Abel class.

The actual primary result of Borges–Goncalves, arXiv2212.03987v3, Theorem3.1/Corollary3.4 and Theorem5.4, pays the exact p-rank f. Concretely, its Cartier iterate on z^(i-1) dz/w is multiplication by binom((5^s-1)/2,i). Lucas reduces nonvanishing to all s base5 digits of i belonging to{0,1,2}. Omitting i=0 and i=d/2 leaves3^s-2 indices. This exact rank, rather than the weaker provisional2^s-1 digit lower bound, is used. It is not a new p-rank computation. Since Frobenius acts in GL_f(F5) on J[5](F5bar), all these points are k-rational. Therefore

    dim_F5 J(k)/5J(k) = dim_F5 J(k)[5] = f.

No claim is made about rational points of the connected, non-etale part of J[5].

### 2.1 Rational points generate the required quotient

Let B=J(k)/5J(k). For any nonzero linear functional ell:B->F5, quotient the Lang isogeny Frob_k-1:J->J by the kernel of J(k)->B->F5. The resulting cover J_ell->J is a geometrically connected finite etale isogeny of degree5. Pulling back along a:H->J is geometrically connected: this is the Albanese/Jacobian covering operation proved in the actual Serre exposition of Lang, sections4 and6, and Milne's Jacobian covering theorem (access limitations recorded separately). It can also be checked for this prime-degree case by the universal property: a section after algebraic closure would lift the Abel map to J_ell and induce a splitting of a degree5 isogeny, impossible. A degree5 constant-group torsor is either connected or split geometrically.

Pull this degree5 cover back along h:D->H. It remains geometrically connected, because the degree5 Galois function-field extension and the extension of degree d/2 are linearly disjoint (their degrees are coprime). Denote the resulting smooth projective curve by D_ell. Etale Hurwitz gives g(D_ell)=5(g_D-1)+1=5g_D-4. For P in D(k), the Frobenius translation in its fiber is ell(a(h(P))). This follows directly from Frob(y)-y=a(h(P)) in the Lang construction.

If ell killed every a(h(P)), each rational P would have exactly5 rational preimages, and there could be no other rational points upstairs. Thus #D_ell(k)=5#D(k). Weil bounds would force

    5(q+1-2g_D sqrt(q)) <= q+1+2(5g_D-4)sqrt(q),
    q+1 <= (5g_D-2)sqrt(q),  q=5^n.

But n>=8s, so sqrt(q)>=5^(4s)>5g_D. Contradiction. Hence the vectors a(h(P)), P in D(k), span B. The points with Z=0 map to branch points and have zero image in B, so points on the affine chart already span. Choose P_1,...,P_f on that chart whose images form a basis of B. No unsupported assumption that rational curve points generate J(k) is used.

### 2.2 The same ramified local ring and all supporting divisors

Take

    A_d=(V[x,y]/(5+x^d+y^d))_(5,x,y).

The relation is a regular parameter in the3-dimensional ambient regular local ring: modulo the square it is5. Hence A_d is a2-dimensional Noetherian regular local domain, with maximal ideal(x,y), characteristic(0,5), and5=-(x^d+y^d). Its associated graded is k[x,y], so5 lies in m^d but not m^(d+1).

Choose the cyclotomic uniformizer t0 in H0(zeta5) from G5, with t0^4=-5, and t satisfying t^N=t0. Then t^d=-5. Its polynomial is Eisenstein over V. Thus L=H0(t) has degree d, O_L=V[t] is a DVR, its residue field is k, and it contains zeta5. Since mu_d is in V, L/H0 is cyclic Galois with delta_a(t)=a t for a in mu_d(V). Restriction to the cyclotomic degree4 subfield has character chi(delta_a)=bar(a)^N in F5*. This follows from delta(t0)/t0=a^N and the source's cyclotomic-uniformizer comparison. In particular chi^2=bar(a)^(d/2) is a sign.

Write P_i=(bar X_i:bar Y_i:1). Smooth Hensel lifting supplies X_i,Y_i in V with X_i^d+Y_i^d=1. At least one is a unit. The map

    A_d -> O_L, x |-> tX_i, y |-> tY_i

is well-defined, local and surjective, because its image contains t and every denominator maps to a unit. Its kernel is generated by the regular parameter Y_i x-X_i y: eliminating one variable shows that the quotient is V[t]. This yields a closed horizontal divisor j_i:Spec O_L -> Spec A_d for EVERY selected P_i, all on the SAME ring.

G5's global integral class c0 in K5(Z[zeta5,1/5]) restricts to K5(L). Localization lifts it to b in K5(O_L), using K4(k)=0 integrally. Fix one b and define gamma_i=(j_i)_*b. Its fraction-field restriction is zero because it has proper closed support. No coefficient vanishing is substituted for integral generic vanishing.

### 2.3 Simultaneous detection with all character and valuation factors

Let T=Spec(A_d tensor_V L). Under x=tX,y=tY this is an arbitrary localization of the affine Fermat curve X^d+Y^d=1. It is flat over A_d and is regular, integral, Noetherian and1-dimensional. The model D over O_L is smooth projective. Every point of its generic curve specializing away from Z=0 is retained by T, by the same positive-valuation denominator argument as G5 lem:splitting and main-proof.

The i-th divisor splits into d distinct L-rational points p_(a,i), with specializations g_a P_i, where g_a(X:Y:Z)=(bar(a)X:bar(a)Y:Z). Flat base change is the exact functor identity

    (A_d tensor_V L) tensor_A (j_i)_*M
      = direct_sum_(a in mu_d) L tensor_(O_L,delta_a) M.

It respects the actual factor maps. If beta is the G5 equivariant coefficient class and b_op is its left multiplication, source conjugacy gives

    rho(gamma_i|T)=sum_a (p_(a,i))_* (chi(delta_a)^2 b_op^2[delta_a(zeta5-1)]_5).

The chosen b need not be equivariant. Its conjugate generic restrictions are those of c0. Since L has ramification degree N over H0(zeta5), EVERY delta_a(zeta5-1) has normalized L-valuation N, not1. Keeping this factor is essential.

Define psi:Pic(D_k)->B by

    psi([E]) = [h_*E-deg(E)o] modulo5J(k).

This is defined on all divisors, including nonrational ones; norm sends principal divisors to principal divisors and h_* preserves degree. It kills all points at Z=0 because their images are branch points. Moreover

    a(h(g_a P_i)) = bar(a)^(-d/2) a(h(P_i))

integrally in J(k), with the right scalar interpreted as the sign +/-1. Thus the G5 Picard specialization detector for gamma_i equals

    sum_a chi(delta_a)^2 N psi([g_aP_i]) = dN a(h(P_i)) in B.

Here dN is a unit modulo5. For any linear relation among rho(gamma_i|T), combine coincident supporting points before applying the source criterion; its contrapositive gives the corresponding relation among dN a(h(P_i)). Independence of the latter forces every coefficient zero. Therefore the gamma_i are independent in K5(A_d)/5K5(A_d), and all lie in the integral generic kernel. Equivalently, for integers e_i,

    sum_i e_i gamma_i in5K5(A_d)  ==>  all e_i in5Z.

This is a complete feasibility construction of arbitrarily large finite coefficient images on a single ring at each s. It is NOT a construction of elements of exact order5, of a free abelian subgroup, of a full kernel presentation, or of a single fixed ring covering every s.

### 2.4 Strongest-payment comparison

The exact p-rank and its full digit count were already paid by the actual primary paper; the Lang isogeny and connected pullback are classical; G5 already supplies the global integral lift and a specialization test with an arbitrary5-torsion target on the entire Picard group. Replacing its quartic/elliptic geometry by the higher Fermat/hyperelliptic quotient and retaining dN closes the compatibility. There is no new field comparison, boundary cancellation or integral lifting operation in this calculation. It is retained as the strongest integrated construction rather than advertised as a distinct substantial discovery by changing a parameter or naming a larger rank.

## 3. Low-weight elimination of an arbitrary boundary

This is a further prefreeze calculation, made after reading Levine's actual filtered localization and purity proofs. It is retained as a source/primary composition, not as a frozen author-proof nominee. It is useful because it avoids treating a failed full Bott-surjectivity argument as an obstruction.

Let L be any characteristic-zero field containing mu5, let C/L be a smooth geometrically integral curve, J=L(C), and beta in K2(L;5) have primitive coefficient boundary. All products below are the source's fixed left-iterated products. Write F^j for the decreasing motivic filtration. On a field H of characteristic zero the weight-j term contributing to K_n(H;5) is

    H^(2j-n)(H,Z/5(j)).

By the field vanishing and norm-residue comparison in G5, it is zero unless 0<=2j-n<=j. Thus for each fixed n there are only finitely many possible weights, ceil(n/2)<=j<=n, WITHOUT a cohomological-dimension assumption. The actual localization tower gives

    partial_q(F^j K_n(J;5)) subset F^(j-1) K_(n-1)(kappa(q);5).

This is a codimension-one shift, not preservation of the same weight. Levine, K-theory and motivic cohomology of schemes I, Proposition6.8 and its proof (PDF19–20), constructs compatible boundary maps of towers. In codimension indexing the dimension of the closed point drops by one. Independently, the homotopy coniveau tower, Corollary3.2.2 and Proposition4.2.2 (PDF18,24–25), gives localization with supported level j identified with level j−1 on a smooth closed point. Characteristic zero ensures that the closed residue extensions are separable. Localizing at q and taking limits gives the displayed inclusion. Finite coefficients are obtained by smashing the triangles with the fixed Moore spectrum. No mixed-characteristic motivic comparison is used: this filtration calculation takes place entirely on the characteristic-zero generic curve.

The multiplicative filtration and the usual cup product on its layers are the operations of Friedlander–Suslin §16 and Levine §11. In the latter, take the base B=Spec L, so the mixed-characteristic equidimensional-cycle restrictions of that paper do not apply. Its products on cycle layers agree with the usual products (PDF51–52). The corrected K-theory layers are supplied by Levine's later Theorem6.4.2 (PDF36–37); G5 also stipulates and explicitly uses the corrected field spectral sequence and the same finite-coefficient product. This is not an assumption of conjectural Gersten exactness.

Let alpha be the nonzero edge of beta in H0(L,mu5), as computed in G5. Its restriction trivializes every relevant Tate twist. For K6(J;5), the first two possible weights are

    j=3: H0(J,mu5^3),
    j=4: H2(J,mu5^4).

The first is represented by b^3(1), hence all of it survives. The second is represented by b^2 rho(z), z in integral K2(J): Matsumoto and the degree-two norm-residue isomorphism identify K2(J)/5 with H2(J,mu5^2), and multiplication by alpha^2 identifies the twists. Integral symbols are in F^2 K2(J;5), since each of their two unit factors is in F^1; therefore b^2 rho(z) lies in F^4. These representatives make every element of the second term permanent as well. There are no incoming differentials: in (s,j) coordinates a d_r incoming into s=0 or s=2 starts in negative cohomological degree for r>=2. Consequently

    K6(J;5)=F^3,
    gr^3 K6(J;5)=H0(J,mu5^3),
    gr^4 K6(J;5)=H2(J,mu5^4).

Similarly K5(H;5)=F^3 and its first graded quotient is

    gr^3 K5(H;5)=H1(H,mu5^3).

Here b^2 K1(H;5) represents every H1 class, using Kummer and multiplication by alpha^2. Incoming differentials again start in negative degree; the representatives kill all outgoing differentials. In particular the map from H*/H*5 to this GRADED QUOTIENT is an isomorphism. No assertion that b^2:K1->K5 is onto is made for arbitrary H.

Now suppose xi in K6(J;5) has prescribed residues e_i b^2[a_i]_5 at distinct L-rational points p_i of an arbitrary localization U of C, and zero residues at every other retained point. Subtract lambda b^3(1), with lambda in F5 chosen to cancel gr^3(xi). This constant class extends over C, so ALL its localization residues are zero. The remainder lies in F^4. Choose integral z in K2(J) so that b^2 rho(z) has the same gr^4 component. Then

    xi − lambda b^3(1) − b^2 rho(z) belongs to F^5 K6(J;5).

At each q of U its residue belongs to F^4 K5(kappa(q);5). Projecting the residue equation onto gr^3, and using the injectivity of b^2 on this quotient, gives EXACTLY

    [partial_q z]_5 = e_i[a_i]_5  if q=p_i,
    [partial_q z]_5 = 0          otherwise in U.

The input xi was arbitrary. Its H4 and H6 weight components have not been assumed zero: their boundaries simply cannot enter gr^3. Nor was a coefficient preimage confused with an integral one: z was selected from integral K2 at the outset. This is the strongest low-weight replacement for the source's full Bott untwisting obtained here.

### 3.1 Completing the specialization calculation

Let R be a complete characteristic-zero DVR with residue characteristic five, with fraction field L containing mu5. Let X/R be a smooth projective relative curve with geometrically integral fibers C,D. Let U,Z,B,psi,p_i,a_i,e_i have precisely the meanings and hypotheses of G5 prop:specialization, except that R is no longer required to be finite over Z5. Thus B is killed by5, psi is defined on ALL Pic(D), kills every point of Z, and U retains every closed generic point specializing outside Z.

If the supported coefficient sum vanishes, torsion-category localization on the arbitrary localized affine curve U gives xi as above. Section3 produces integral z with the required tame-symbol congruences. Complete Noetherian DVRs are excellent; the normalization R_q in a finite residue-field extension kappa(q)/L is therefore finite, is a DVR, and has a unique valuation extension. For every closed q define r(q), normalized v_q and f_q=[k_q:kappa(r(q))] exactly as in the source. The regular surface coniveau differential gives

    sum_q f_q v_q(partial_q z)(r(q))
       + div_D(partial_D z) = 0.

This identity uses only d1²=0. It includes nonnormal horizontal closures by the finite map Spec R_q->X, with the exact normalized residue-degree factor f_q; there is no extra ramification multiplier. Applying psi kills omitted points and fifth powers and gives

    sum_i e_i v_L(a_i) psi([r_i]) = 0.

Thus the contrapositive of the source criterion still follows. The complete argument combines its already-paid surface operation with the elementary first-two-weight elimination above. It is a comparison consequence of the actual primary filtered-localization machinery, not a new solution of a higher-kernel conjecture.

## 4. Countably many independent integral classes on one fixed-ramification ring

This calculation uses Section3.1, so it does not depend on the unverified-in-this-packet classical cohomological-dimension shortcut discussed in PREFREEZE-INFINITE.md. It is another prefreeze feasibility construction, not a nominee.

Let k0=F_(5^8). Use the source D:X⁴+Y⁴=Z⁴, E:w²=s⁴+1, h:D->E of degree2, and choose a k0-rational branch point o as origin. Let P_* in D(k0) on Z=0 map to o. Set

    K_m = k0(D^m),
    K_infinity = colim_m K_m (coordinate projections),
    k = perfect closure of K_infinity.

D is geometrically integral, so these inclusions are field inclusions. Let P_i be the generic point in the i-th factor, viewed as a D(k)-point, and Q_i=h(P_i) in E(k). These points have Z≠0.

Here is the precise divisibility test. E is ordinary: its source-computed Frobenius trace over F5 is2, prime to5. The separable Verschiebung V_E:E^(5)->E has degree5 and geometrically connected source. Its kernel is a constant Z/5 over k0: the source count #E(F_(5^4))=640 gives a rational point of order5; the nontrivial étale group has geometric order5; Frobenius transports this to the Verschiebung kernel. These are the usual Frobenius/Verschiebung operations on an ordinary elliptic curve.

For a finite combination with coefficients a_i in{0,1,2,3,4}, at least one nonzero, consider phi:D^m->E, phi=sum_i [a_i]h_i. The pullback of V_E is a degree-five constant-group torsor. It is geometrically nontrivial: fix all coordinates except a nonzero a_j at P_*. The restricted map is [a_j]h:D->E, finite of degree2a_j² prime to5. A degree-five connected Galois field extension cannot become split after an extension of degree prime to5. This restricted torsor is geometrically connected; hence the original torsor is geometrically nontrivial and, since its group has prime order, geometrically connected. It is finite étale over the smooth integral D^m, so its total space is integral.

Passing from K_m to K_M for M>m preserves connectedness: on varieties it is pullback by the projection D^M->D^m, a product with geometrically integral factors. Passing to perfect closure preserves a nontrivial finite étale extension, since a separable extension cannot be contained in a purely inseparable extension. Thus phi(P_1,...,P_m) has no k-rational preimage under V_E. If sum a_i Q_i=5R, the factorization [5]=V_E composed with relative Frobenius would supply such a preimage. Contradiction. Therefore the Q_i are F5-linearly independent in E(k)/5E(k).

Take V=W(k), a complete Noetherian DVR with uniformizer5, and

    A=(V[x,y]/(5+x⁴+y⁴))_(5,x,y).

As in Section2, A is a2-dimensional regular local domain and ord_m(5)=4. Base-change the source unramified V0=W(k0), its cyclotomic DVR O0, and its ALREADY INTEGRAL lift b0 in K5(O0) to

    O=V[t]/(t⁴+5), L=Frac(O).

The maps V0->V and O0->O are flat (torsion-free modules over DVRs); O is a DVR. This step avoids the false assertion K4(k)=0 for the new infinite field. Put b=res(b0) in K5(O). Its generic restriction is still the restriction of the source global c0, so the complete source conjugacy formula remains valid.

For each i, Hensel-lift P_i to X_i,Y_i in V with X_i⁴+Y_i⁴=1 and use the closed divisor j_i:A->O, x->tX_i,y->tY_i. Fixing b for all i, set gamma_i=(j_i)_*b in integral K5(A). Every gamma_i vanishes in K5(Frac A) by support.

After the single flat base change V->L, these divisors split into the four source-conjugate points. The fixed elliptic Picard map

    psi:Pic(D_k)->E(k)/5E(k), [D']->[h_*D'−deg(D')o]

kills infinity. For each gamma_i the normalized valuations are1, the source character is a², and h(g_aP_i)=a²Q_i, so the detector is4Q_i. Section3.1 applies to any finite linear combination, combining coincident supports if necessary. Independence of the Q_i proves

    sum_(finite i) e_i gamma_i in 5K5(A) implies every e_i in5Z.

This is genuine simultaneous independence on ONE ring, not a collection of unrelated examples. It says nothing about the additive orders of the gamma_i, a free abelian subgroup, or a presentation of the whole Gersten kernel. The lower-bound mechanism is still the source Picard detector plus classical connected-cover and filtered-localization operations. Neither its cardinality nor its fixed ramification is used to self-award a contribution grade.

## 5. What the integrated construction does not pay

The investigated rank constructions do not supply a distinct nonroutine integral operation after the source and primary mechanisms are combined. No exact discovery statement was frozen. The following are precise limits of these calculations, not replacement conjectures or claims of impossibility.

1. **Integral order.** Injectivity K5(A)/5 -> K5(A;5) proves the displayed independence modulo5. It does not prove 5 gamma_i=0, infinite additive order, or any exact order. To prove an annihilator for a supported integral combination one would need a compatible integral localization preimage with that multiple as its complete residue vector, not merely the coefficient preimage used to derive necessary relations. No such integral preimage is constructed here.
2. **Exact recognition of relations.** We show ker(supported pushforward) is contained in ker(Picard detector). The reverse containment is not established. A zero Picard class is not by itself an integral K6 class with all prescribed residues and no unwanted retained residues. This is the exact missing sufficiency operation, not a disguised assertion of Gersten exactness.
3. **Wild degree or higher precision.** The finite-rank construction deliberately takes N=d/4 prime to5. Its detector has the exact factor dN, where d comes from the orbit and N from normalized cyclotomic valuation. If one inserts N divisible by5 into that calculation, dN is zero modulo5. Discarding N or replacing the wild orbit by one reduced point is invalid. Such a computation is a limitation of this detector, not an impossibility result. No nonreduced-special-fiber or higher-coefficient replacement cancelling these losses has been constructed.
4. **Fixed finite residue target.** The infinite-rank construction changes the residue field to k above. On the original finite-field elliptic quotient the available target E(k0)/5 is finite and has dimension1. The countable construction does not prove an infinite-rank conclusion on the source ring with finite residue field. No such conclusion is proposed.

The G3 integral Steinberg lift, the G5 global cyclotomic integral lift, arbitrary support localization, exact character factors, normalized valuation/residue-degree pushforwards, field comparisons, and the available primary cover operations have all been used in deciding not to nominate a routine amplification. This is PREFREEZE/no nominee, not a mathematical self-grade and not an exhaustion claim.
