# Equivariant reconstruction: strongest paid reduction

PREFREEZE/no nominee. These are research notes, not a frozen author-proof submission or an independent gate. One selected family, Source009, is investigated. The stipulated pin is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, including its operative proofs. No truth audit is made. The initial catalogue overrun and history false admissions remain disclosed in READING.md.

## 1. Precise interface and proposed operation

Let ell be a prime, k an algebraically closed field of characteristic different from ell, and K/k a finitely generated field of transcendence degree at least two. Put

    V(K)=K^*/K^{*ell},
    R(K)=span_Fell{[x] tensor [1-x]: x != 0,1},
    W(K)=(V(K) tensor V(K))/R(K).

Let A(K) be the group of Fell-linear automorphisms of V(K) preserving R(K). All scalars Fell^* belong to A(K), and write Q(K)=A(K)/Fell^*. Denote K^perf by P (and P=K in characteristic zero). Source009's mod-ell thm:main, with its actual sections07–08, supplies a natural group isomorphism

    Aut(P,k)/<F> = Q(K)                                  (1)

in characteristic p>0, where F is absolute p-Frobenius and its powers are indexed by Z. In characteristic zero the left side has no Frobenius quotient. A field isomorphism between two such pairs induces the corresponding Isom bijection. Naturality under composition follows directly from the forward map induced on symbols and bijectivity, not from separately choosing representatives.

The exploratory operation was to reconstruct finite symmetry actions and arithmetic descent data from symbol automorphisms modulo scalars, including all noncommuting group relations, without assuming that the group order is prime to either p or ell. An individual lift from (1) does not by itself prove simultaneous lifting. The calculations below show that the apparent coherence problem is paid.

This is distinct from r118's cycle specialization, from the equal-characteristic finite-prime-power T009P102, and from a noninjective Hom classification. No old scope is narrowed or renamed.

## 2. Operations already in the stipulated source and primary

The mod-ell source constructs the field through simultaneous values of good rational functions: blowups detect a whole finite tuple, transported additive relations give perfect rational operations, affine-group comparisons align the constants, and identities on dense opens preserve every polynomial relation. Section08 then fixes true divisors by restrictions to rational subfields, aligns point-order scalars using their sum relation, and compares different good subfields at an exceptional divisor. Its last proposition proves that an automorphism acting by a scalar on V is exactly an integral Frobenius power. Thus (1) is an actual functorial reconstruction interface with a precisely known central kernel.

The pro-ell companion's final proof recovers actual rational quotient diagrams and their flag restrictions, then invokes Pop's Isom theorem. It also retains a single global unit and exactly the Frobenius ambiguity. It does not provide a new independent obstruction to the mod-ell calculation. The equal-characteristic companion instead reconstructs the original field and named base from mod-p symbols, with no Frobenius quotient: F->F is not a surjective field map there and kills V. Its projective-lifting proof cannot be substituted into (1) while pretending the input prime is unchanged.

Topaz, arXiv1408.5194v3, Theorem B and the full section7 proof, already give the mod-ell Isom mechanism when all rational subgroups are supplied and relative dimension is at least five. The proof constructs the geometric lattice, uses combinatorial-geometry reconstruction, and then removes the scalar kernel with valuation-unit subgroups, rational divisor sequences, Bertini good functions and a two-generator comparison. Those are credited primary operations. Source009 supplies the stronger rational-subfield recovery and dimension-two interface; r119 does not invent these.

Topaz, arXiv1910.03563v1, Theorems A/B and section5.3, explicitly reconstructs arithmetic fixed fields using integral ell-adic cohomology and a projective Galois action under its stated nonlocal-base and dimension-at-least-three assumptions. The final proof passes from geometric reconstruction modulo Frobenius to equivariance and then takes fixed fields. The present finite-orbit calculation makes that last compatibility explicit at the stronger stipulated mod-ell source interface. Removing the earlier base/dimension restrictions by changing the reconstruction input does not itself identify a nonroutine operation.

## 3. Every finite projective action lifts coherently

Assume char k=p>0. Inside P there is the intrinsic subfield c consisting of elements algebraic over Fp; it is an algebraic closure of Fp and lies in k. Restriction gives

    r: Aut(P,k) -> Aut(c/Fp) = Zhat,
    r(F)=1.                                               (2)

The last equality uses arithmetic p-Frobenius. The identification is the elementary inverse limit of the cyclic groups of F_(p^n)/Fp. It can be checked without a topology on Aut(P): restriction to every finite field is compatible, and an automorphism of c is precisely such a compatible system.

Let q in Q(K) have finite order m, and choose any lift beta under (1). Then beta^m=F^n for an integer n. Restriction gives m r(beta)=n in Zhat. Reducing modulo m shows m divides n in Z. Writing n=ma, the torsionfreeness of Zhat gives r(beta)=a. For completeness, if m z=0 in Zhat, reduction modulo mt implies z=0 modulo t for every t, hence z=0. Therefore

    s(q)=F^(-a) beta                                       (3)

fixes c and has order dividing m. Changing beta to F^j beta changes a to a+j, so (3) is independent of the initial lift. It is the unique lift fixing c, since a Frobenius power fixing c is the identity.

Now let a finite group G act through any homomorphism q:G->Q(K), not necessarily injectively. The product s(q(g))s(q(h)) fixes c and lifts q(gh), hence is s(q(gh)) by uniqueness. This proves every relation, including noncommuting ones, at once. The identity is normalized to the identity. The resulting field action has kernel exactly ker q. No averaging, division by |G| in the field, semisimplicity or coprimality condition was used. In particular p||G and ell||G are allowed. In characteristic zero the source has no central kernel, so lifting is immediate.

If the given action is an actual representation rho:G->A(K), there are unique scalars chi(g) with

    rho(g)=chi(g) s(q(g))_* .                              (4)

Since both other maps are representations and scalars are central, chi is a group character into Fell^*. There is no remaining scalar two-cocycle. This does not mean chi is trivial: a scalar-only representation is an immediate example. Its projective action, and hence its reconstructed field action, is trivial. The scalar group acts freely on automorphisms of the nonzero vector space V. At ell=2, the scalar group is trivial.

These finite lifts are compatible with restriction to subgroups and with conjugating the symbol data by an Isom map. Indeed conjugation by any field isomorphism takes the intrinsic c onto the corresponding prime-field closure, so it preserves the normalization in (3). Any change of that isomorphism by absolute Frobenius leaves the action conjugation unchanged. Thus the calculation gives simultaneous actions and their naturality, not just isolated cyclic examples.

## 4. Fixed fields and finite models are also paid

Replace G by its faithful image H when taking degrees. Artin's fixed-field theorem gives P/P^H finite Galois with group H and degree |H|, irrespective of characteristic or divisibility. The relevant actual proof was read in Stacks09DU, Lemma9.21.6: orbit polynomials provide algebraicity and separability, and a finite set of separating elements reduces the degree calculation to a finite extension. The following compatibility with perfection is elementary.

The field P^H is perfect. If z^p=x in P and x is fixed, every h(z) is the unique pth root of x, so z is fixed. Form the compositum

    L = product_{h in H} h(K) inside P.

Here product means field compositum. Each h preserves k as a set. Finitely many generators of the h(K) lie in one K^(1/p^r), so L/K is a finite purely inseparable extension, L/k is finitely generated, and L^perf=P. The action preserves L. For x in P^H some x^(p^r) lies in L and is H-fixed. The converse inclusion follows from uniqueness of roots. Hence

    P^H=(L^H)^perf.                                        (5)

In characteristic zero L=K, so no enlargement is needed. This supplies one common model for every subgroup: for J<=H, P^J=(L^J)^perf. The whole fixed-field lattice, normal-subgroup quotients and all inclusion maps follow from Artin's fundamental theorem. No projective choice is made anew for each subgroup.

Even without invoking the stronger classification of finite automorphism groups of algebraically closed fields, finite generation over the fixed constants is enough. Put k0=k^H. Artin gives k/k0 finite with degree the size of the restriction image; k0 is perfect by unique pth roots. Thus L/k0 is finitely generated. Choose finitely many field generators a_i of L/k0 and let E0 be generated over k0 by all coefficients of their H-orbit polynomials. Then E0 lies in L^H and L/E0 is finite. Consequently L^H/E0 is finite and L^H/k0 is finitely generated. No real-closed-field classification is needed for this assertion.

A failed norm method in mod-ell symbols is irrelevant here: when ell divides |H|, restriction followed by norm can vanish, but the reconstructed field and its actual fixed-field construction remain available. Requiring norm inversion would discard the strongest compatible operation.

## 5. Locally finite actions remove the arithmetic Frobenius ambiguity

A group action on a field is called locally finite here if each individual field element has a finite orbit. This is a property of the action, not an assertion that the acting group is locally finite.

Suppose u,v:G->Aut(P,k) are two locally finite actions with equal images in Aut(P,k)/<F>. Since F is central and has infinite order, there is a unique n(g) in Z with

    u(g)=F^(n(g)) v(g).

Multiplication shows n(gh)=n(g)+n(h). Choose x transcendental over k. Its u-orbit A and v-orbit B are finite. The equality implies that for every g there are a in A and b in B with a=F^(n(g))(b). For each pair (a,b) there is at most one integer exponent: equality of two Frobenius powers of b would make b algebraic over Fp, contrary to transcendence over k. Thus n(G) is a finite subgroup of Z, and is zero. The two actions are identical.

This avoids assuming that n is continuous, or that a lift is continuous merely because a quotient action is. It uses finite orbits directly. If alpha:P->P' is a field isomorphism between reconstructed pairs, conjugation transports a locally finite action to a locally finite action; therefore projective equivariance under alpha forces exact equivariance. In characteristic zero the same conclusion follows immediately from the source's trivial kernel.

## 6. Arithmetic input, full fixed-field descent, and scalar compatibility

Here is the precise geometric-input setting examined, still not a nominated statement. Let k0 and l0 be arbitrary perfect fields of characteristic different from ell. Let K0/k0 and L0/l0 be finitely generated regular extensions, both of transcendence degree at least two. Choose algebraic closures k,l and geometric composita K=K0 k,L=L0 l. Regularity ensures these are fields, the constant extensions are linearly disjoint, and

    Gal(K/K0)=Gal(k/k0)=Gamma,
    Gal(L/L0)=Gal(l/l0)=Delta.

Take a compatible symbol isomorphism Theta:V(K)->V(L), and a group isomorphism eta:Gamma->Delta such that Theta is equivariant modulo Fell^*. A continuous profinite eta is allowed, but the finite-orbit argument only needs the stated group isomorphism and the actual geometric actions. The projective condition may equivalently be stated on nonzero vectors modulo scalars: an invertible linear map fixing every line is scalar, as follows by comparing independent u,v and u+v. Source good rational subfields ensure V has dimension at least two.

Source009 gives alpha:K^perf->L^perf, respecting k,l, whose induced map is Theta up to one scalar. Equality of the projective Galois actions then says

    alpha sigma alpha^(-1) = F^(n(sigma)) eta(sigma)

in characteristic p. Both actions are locally finite: an element of K0 k uses only finitely many algebraic constants, and adjoining a p-power root preserves its finite orbit by uniqueness. Apply section5 on L^perf to get n=0. Thus alpha is exactly equivariant.

The invariants have the required form:

    (K^perf)^Gamma=K0^perf,       k^Gamma=k0.               (6)

To see the first equality, for x fixed choose r with x^(p^r) in K. It is fixed, so is in K0 by the constant-extension Galois identity; conversely every p-power root of a K0 element is fixed. Characteristic zero is the r=0 case. Therefore alpha descends to K0^perf->L0^perf and restricts to k0->l0, with all four inclusions preserved. The same alpha and scalar give the original geometric symbol isomorphism. Its Frobenius ambiguity remains exactly the source ambiguity; the scalar changes accordingly when alpha is composed with Frobenius, so one must not assert uniqueness of a pair (scalar,alpha) before making that quotient.

No nonlocality, non-Henselianity or real-closed exclusion is needed in this final descent argument once the stronger geometric source theorem is supplied. Dimension two suffices because the source supplies that dimension. These improvements in the visible conclusion are entirely attributable to replacing the reconstruction input, followed by the same primary fixed-field operation. They do not independently establish a substantial contribution.

## 7. Exact boundaries: the original embedded model and abstract actions

There is no residual finite-group coherence defect after sections3–4, and no residual Frobenius-equivariance defect for actual geometric actions after sections5–6. Two limitations should not be mistaken for new nominated targets.

First, a prime-to-p invariant cannot force the reconstructed action to preserve the original named nonperfect subfield K inside P. For a concrete example let k be algebraically closed of characteristic p, K=k(x,y), P=K^perf, and define the k-automorphism

    beta(x)=y^p,      beta(y)=x^(1/p).

It has order two on P. Its induced symbol automorphism is defined on V(K) through the canonical V(K)=V(P), preserves all Steinberg relations, and has order two. It does not preserve K, since x^(1/p) is not in k(x,y). Its normalized finite lift is beta itself. If another lift of its projective symbol class came from an automorphism of K, source uniqueness would make that lift F^n beta. For n<0 its image of y is x^(p^(n-1)), outside K. For n=0 the same failure occurs. For n>=1 the images generate k(y^(p^(n+1)),x^(p^(n-1))), a proper subfield of K, as the y-exponent is at least p^2. Thus no F^n beta restricts to an automorphism of K. This is a failure of preserving that particular embedded model, not a claim that all purely inseparable models are abstractly nonisomorphic.

A common invariant model nevertheless exists explicitly: L=k(x^(1/p),y) contains K, has perfection P, and beta swaps x^(1/p) and y. Section4's construction already predicts this. The example reinforces why the paid conclusion uses a common purely inseparable model rather than silently strengthening it to the initial K.

Second, an arbitrary action on the abstract quotient group need not be supplied with any locally finite field lift. For G=Z, the trivial quotient action has lifts sending its generator to F^n for every integer n. All n!=0 have infinite orbits on a transcendental element, so the locally finite lift is uniquely n=0. Dropping the finite-orbit condition creates ambiguity immediately. This observation is not a classification theorem for arbitrary quotient actions. Existence of a locally finite lift for arbitrary abstract profinite input, its continuity, or finite-type geometric realizability has not been established here. The geometric hypotheses in section6 provide existence; they cannot simply be deleted.

## 8. Outcome and unchanged scopes

The investigated full finite-action and geometric arithmetic-descent operations close by the strongest compatible source/primary composition. No additional nonroutine operation has been identified. This round ends PREFREEZE/no nominee, with no theorem freeze, supporting substitute, independent grade, acceptance or count. The remaining research obligation is to identify and pay a genuinely additional full-scope operation; none is asserted here. Abstract-action realization and recovery of a designated nonperfect model are boundaries, not renamed conjectures submitted for credit.

T009P102's all-primes/all-finite-level equal-characteristic scope and its Proposition I remain unchanged. Its full original proof was read, including the logarithmic-derivative rigidity, no-p-torsion coefficient filtration and level induction. None is being regraded or represented as a new r119 operation. The earlier noninjective Hom scopes are not closed by an automorphism argument. r118's rational-cycle conclusion, the original uniform-integral T001U58 boundary, H138 and T185R144 dispositions, and all other user-listed old full targets remain unchanged. No exhaustion, global clearance, worldwide priority or current-open assertion is made.
