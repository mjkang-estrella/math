# r146 — moving centers, their complements, and the remaining extension problem

PREFREEZE / no nominee. These are retained research calculations, not a frozen author theorem or a mathematical self-grade. The one developed family is Source047. All source proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. The old T047S74 scope, r29's full thickness target T047N, F004, and all supplied earlier dispositions remain unchanged. The earlier r29 moving-polynomial idea was prefreeze; it is acknowledged here rather than represented as a newly discovered direction.

## 1. The exact paid source operation

The canonical source defines

    P = C[p,s,u,F,J], x=s²+u³+p²F,
    y=s+x(x−u³), z=sx+p²J,
    H=x²F−(1+2sx)J−p²J²−pu, A=P/(H).

Its identity xy−z(z+1)=p²(H+pu) gives the embedded ring

    S=C[p,x,y,z,u]/(xy−z(z+1)−p³u),
    A[p⁻¹]=S[p⁻¹]=C[p,p⁻¹,x,y,z].

The source supplies the complete polynomial cylinder, including its inverse at p=0, not just a residual-coordinate assertion. On P[p⁻¹], Δ=−p²∂u with p,x,y,z fixed preserves P and satisfies ΔH=p³. Thus exp(wΔ) takes H to H+p³w. With x0=s²+u³, its determinant-one change is

    L=x0²F−(1+2sx0)J, M=(1−2sx0)F+4s²J,
    F=4s²L+(1+2sx0)M, J=−(1−2sx0)L+x0²M.

Writing B=C[p,s,u,M], H(L)=L−pu+p²Q(L)+p⁴F(L)³, set C0=Q(0), Q1=(Q−C0)/L, L*=pu−p²C0. The source proves H(L*)∈p³B and gives a polynomial e with p³e=L−L*. Then w=−H(L*+p³e)/p³ is polynomial, so the quotient is B[e]. Transport through exp(−wΔ) gives actual coordinates of A[w]. All this is already paid.

For nonpolynomiality, the source identifies the exact valuation graded algebra

    R=S/pS=C[x,y,z,u]/(xy−z(z+1)),
    s_R=y−x(x−u³), I=(x−s_R²−u³,z−s_R x),
    gr A=G=R[τ,I/τ²].

The weight reduction terminates at the actual valuation of each element, so this is an equality with its specified coefficient ring, not a guessed initial presentation. The smooth G has a line-bundle torsor

    T=C[a,d,b,c,u]/(ac−bd−1),
    x=ab, y=dc, z=db,
    I T=(v), v=a³b−a²u³−d²,
    G⊗R T=T[τ,V]/(τ²V−v).

Fiber weights of (a,d,b,c,u,V) are (1,1,−1,−1,0,2). The normalized additive lift works over Spec G without assuming an action preserves R. A positive valuation-degree invariant forces V invariant. The exact homogeneous pieces then produce a nonzero LND E of T with nonpositive fiber shift and E²(v)=0. The source's auxiliary grading, polynomial abc, and nonsquare argument exclude it.

The maps p:Spec A→A¹ and (p,H):A⁵→A² are smooth, hence flat, and surjective, with A³ over every residue field, including nonclosed points. Source §7 proves this using the actual coordinate change over C[p,p⁻¹], the p=0 determinant-one change, and the unit Jacobian ideal. Nontriviality is Zariski non-local-triviality with arbitrary polynomial transition functions. These headlines, their stable-coordinate version, and their routine transports are not nominations.

## 2. Fixed-thickness moving center: carry the compatible algebra

Let f∈C[u] be monic of odd degree r≥3. Define A_f by the same presentation, replacing u³ by f(u) wherever it occurs in x and y, but retaining the term −pu in H. Write s_f=y−x(x−f(u)) in S. Put

    f1=x−s_f²−f(u), g1=z−s_f x, I_f=(f1 mod p,g1 mod p)⊂R.

The identity remains xy−z(z+1)=p²(H_f+pu). Inverting p still gives the SAME S[p⁻¹], with u=p⁻³(xy−z(z+1)). Thus the auxiliary S itself does not depend on f.

The cylinder construction remains exact, not merely plausible: Δu=−p², Δs=−p²x f'(u), ΔF=(2sx+1)f'(u), ΔJ=x²f'(u), and ΔH_f=p³. The determinant-one L,M transformation and the displayed root/certificate calculations of §1 are unchanged with x0=s²+f(u). Consequently A_f[w] is polynomial over C[p]. Integrality follows by localization and p-nondivisibility of H_f, exactly as in the source. Smoothness follows from the cylinder, or from the source's relative Jacobian argument. Its residue-field A³-fibrations follow from the same coordinate computation. These are source/classical payments.

The valuation argument gives

    gr A_f=R[τ,I_f/τ²],
    G_f⊗R T=T[τ,V]/(τ²V−v_f),
    v_f=a³b−a²f(u)−d².

The source's global principalization certificates use only h=x−f(u), so they remain valid: g1=b²v_f and f1=(c²−b²h)v_f, and the coefficients displayed in the source generate the unit ideal. There is no unproved change of the coefficient inclusion.

The rigidity step also carries through. Give (a,d,b,c,u) auxiliary weights (0,r,−r,0,2). The highest part of v_f is −(d²+a²u^r), of degree 2r; all lower terms of f and a³b have smaller degree. A highest auxiliary component E' of a hypothetical nonpositive-fiber-weight LND with E²(v_f)=0 therefore satisfies (E')²(d²+a²u^r)=0. Its orbit polynomials give

    d(q)²+a(q)²u(q)^r = N+qE'(N).

Any common root of the two summands would have multiplicity at least two in their nonzero linear sum, so the summands are coprime. If either is nonconstant, Mason–Stothers gives

    2D_d=2D_a+rD_u ≤ D_d+D_a+D_u,
    (r−2)D_u≤0.

Hence D_u=0 and D_a=D_d>0. Leading-coefficient cancellation would make −u^r a square in C(a,d,b)(u), impossible by its odd u-order. Thus E' fixes a,d,u. Differentiating ac−bd=1 gives E'(b)=ah and E'(c)=dh. The two a/d charts give h∈C[a,d,u]; its required negative fiber weight forces h=0. This is the source rigidity proof with the highest odd term retained, not a distinct rigidity theorem offered for acceptance.

The same source lifting/extraction now excludes positive-degree invariants of every nonzero LND of A_f. Consequently DK(A_f)⊂S. Conversely, clear p-denominators from the three coordinate partial derivatives on C[p,p⁻¹,x,y,z]; their kernels together contain p,x,y,z. The derivation δp=δx=δu=0, δz=x, δy=2z+1 on S becomes an LND of A_f after multiplication by p² and fixes u. Thus

    DK(A_f)=S.                                                (2.1)

This is r29's already-developed intrinsic operation at fixed thickness, with the compatible odd-degree rigidity checked. It implies A_f is not A⁴ but does not distinguish different f.

## 3. What arbitrary isomorphisms must preserve

The intrinsic morphism Spec A_f→Spec DK(A_f)=Spec S is an isomorphism precisely over D(p). Over p=0, the image lies in D_f=V(I_f)⊂Y=Spec R; points outside D_f have empty fiber, and points on D_f have A¹ as residue-field fiber because the coefficients x² and −(1+2s_f x) form a unimodular row. Hence the reduced divisor (p) in S is recovered intrinsically.

The same exact graded computation as r29 gives

    ((p^j A_f∩S)+pS)/pS=I_f^ceil(j/2), j≥1.                   (3.1)

In particular an arbitrary C-isomorphism A_f≅A_g induces an automorphism of Y taking D_f to D_g. The special centers are smooth embedded A²'s: modulo I_f the inverse parameter is s=s_f and

    x=s²+f(u), z=sx, y=s+x(x−f(u)),

so R/I_f=C[s,u]. A marked comparison fixing u, x, or a ruling is not enough. Pair equivalence is only a necessary reduction; it does not by itself give an isomorphism of the original modifications over S. Higher p-adic center data could still matter.

For an exact formulation retaining all data, let K_j(f)=p^jA_f∩S. Since A_f⊂S[p⁻¹], it is recovered as the union of p⁻jK_j(f). Thus an automorphism of S taking p to a nonzero constant multiple of p and carrying every K_j(f) to K_j(g) extends to an isomorphism A_f≅A_g, and conversely every isomorphism has these properties. Formula (3.1) recovers only the reduced part of this data. No unproved formula for every unreduced K_j is asserted.

## 4. Principalization is compatible with arbitrary pair isomorphisms

The class group of Y=Q₂×A¹ is Z. Indeed, inverting x gives the factorial ring C[x,x⁻¹,z,u]. The two components of x=0 are B0=(x,z) and B−1=(x,z+1). They generate the class group with the relation div(x)=B0+B−1. There are no further relations: a function whose divisor is supported on these components becomes a unit in the localization, hence is c x^n, which gives only multiples of that relation. Smoothness identifies this class group with Pic(Y).

The torsor T→Y represents a generator: the ideal (x,z+1) pulls back to (a), since x=ab, z+1=ac and (b,c)=T. The ideal I_f pulls back to (v_f), where v_f has fiber weight two. Therefore its ideal class is twice that generator, with the same sign convention for both ideals. It is nonzero and independent of f. In particular I_f is invertible and nonprincipal.

If an automorphism of Y carries I_g to I_f, it preserves this twice-generator class, hence preserves the generator because Pic(Y)=Z is torsion-free. It therefore lifts to an automorphism of the associated Gm-torsor, commuting with fiber scaling. The unit group of T is C*: after inverting a, a unit is c a^n, and the nonempty a=0 divisor forces n=0 for a unit and its inverse. Thus the lift takes v_g to c v_f for some c∈C*. Rescaling the torsor by a square root of c normalizes the value to one.

We obtain a necessary intrinsic comparison of the affine threefolds

    E_f=Spec T/(v_f−1),

with the involution ι:(a,d,b,c,u)↦(−a,−d,−b,−c,u). This is more than merely observing that the ideal is nonprincipal. Moreover E_f/⟨ι⟩≅Y\D_f: on each trivialization of the line bundle a nonvanishing weight-two section can be normalized to one in two ways. Equivalently, the torsor over the complement is (E_f×Gm)/μ₂, with the diagonal sign action. Thus this comparison tracks the actual complement and its canonical double cover.

## 5. Exact principal hypersurface and charts of E_f

There is a useful complete algebraic simplification. In E_f, put

    k=(b−d)/a = a²b²−ab f(u)−dc,
    Z=d−a³/2, Y0=k+a²/4.

The equality for k follows without localization:

    b−d=b(1+d²)−d(1+bd)
        =b(a³b−a²f(u))−dac
        =a(a²b²−abf(u)−dc).

Since b=d+ak, the equation v_f=1 becomes

    a⁴k=d²+1+a²f(u)−a³d,
    a⁴Y0=Z²+1+a²f(u).                                       (5.1)

Conversely, from (a,Z,u,Y0) satisfying (5.1), set

    d=Z+a³/2, k=Y0−a²/4,
    b=d+ak, c=a³k−a f(u)+a²d+dk.

Then ac−bd=1 and a³b−a²f(u)−d²=1, by substituting (5.1). The formulas in both directions are polynomial and inverse; cancellation of a can either be avoided by these identities or justified in the displayed domains. Therefore

    E_f ≅ {a⁴Y0=Z²+1+a²f(u)}⊂A⁴.                           (5.2)

In these coordinates the involution is (a,Z,u,Y0)↦(−a,−Z,u,Y0).

The two special components at a=0 are Z=±i, each an A². Removing the opposite component gives a chart U_ε≅A³, ε=±i. In the original d-coordinate, write

    σ_ε=ε+(ε/2)a²f(u)+a³/2,
    d=σ_ε+a⁴t_ε,
    b=(d²+a²f(u)+1)/a³,
    c=(d³+d+a²df(u)+a³)/a⁴.                                 (5.3)

The two quotients in (5.3) are polynomials: their numerators vanish respectively modulo a³ and a⁴ after the displayed substitution. The resulting map A³→E_f has image U_ε. To verify its inverse everywhere on U_ε, use (5.1) and the simple root ε: near a=0, Z−ε−(ε/2)a²f(u) is divisible by a⁴, because the product with the other factor has that divisibility and the other factor is a unit there. Away from a=0 the formula is immediate. These local regular functions agree, giving t_ε globally. The polynomial forward and inverse formulas agree on the dense set a≠0, hence everywhere.

On the overlap,

    t_- = t_+ + 2i/a⁴ + i f(u)/a².                          (5.4)

Thus E_f is an additive torsor over B=L₂×A¹_u, where L₂ is the affine a-line with doubled origin. The involution exchanges the two origins, sends a to −a, and sends t_ε to −t_ε in the opposite chart; u is fixed. The term a³/2 cancels exactly in this check.

For this fixed base and fixed additive action, the cocycle class of (5.4) lies in

    C[u][a,a⁻¹] / C[u][a].

The difference i(f−g)/a² is nonzero unless f=g. This marked distinction does NOT survive arbitrary changes of the total space, as the next calculation shows. Likewise, studying the surface fibers u=c and their Danielewski root jets requires u to remain marked. It is not an intrinsic invariant of the threefold.

## 6. First strongest payment: the actual fiber-product operation

The classical operation of Danielewski, read in Moser-Jauslin–Poloni §2.2 and its constructive §4, applies to the charts, not just to an analogy with them. The fiber product E_f×_B E_g is a Ga-torsor over each affine E_f and E_g. H¹(E_f,O)=H¹(E_g,O)=0 makes both torsors trivial, giving

    E_f×A¹ ≅ E_g×A¹.

This also respects the involution after choosing the extra line with the sign action. Indeed, the involution acts affinely on the space of sections of either trivial torsor. If s is a section, the affine average (s+ιs)/2 is an invariant section. Relative to it, the action on the fiber coordinate is multiplication by −1. This is a standard finite-group averaging payment, not an obstruction to equivariant stabilization.

This already prevents a cylinder invariant from recovering f. But it is not the strongest available reduction: the actual deformation-normalization operation removes the parameter before stabilization.

## 7. Stronger payment: an equivariant polynomial normalizer removes f

Set r0=Z²+1, rf=r0+a²f(u), and choose any polynomial antiderivative F0'(u)=f(u). On C[a,Z,u], use the polynomial shears

    A_t:(Z,u)↦(Z+t F0(u)/4,u),
    B_t:(Z,u)↦(Z,u+t Z),

where t=±a and a is fixed. Each has an explicit inverse with −t. Each commutes with (a,Z,u)↦(−a,−Z,u).

Apply, in this stated order to a coordinate pair, the eight maps

    A_a, B_a, A_−a, B_−a, A_−a, B_−a, A_a, B_a.             (7.1)

Call the resulting polynomial automorphism Φ. For the first four maps (call the composite C(a)), Taylor expansion through a³ gives

    C(a)(Z)=Z−a²Z f/4−a³(F0 f/16+Z²f'/8) mod a⁴,
    C(a)(u)=u+a²F0/4+a³Z f/4 mod a⁴.

Replacing a by −a cancels the order-three terms when the two four-map composites are applied in succession; their cross effects start in order four. Thus

    Φ(Z)=Z−(a²/2)Zf(u) mod a⁴,
    Φ(u)=u+(a²/2)F0(u) mod a⁴,
    Φ(r0)=(1−a²f(u))rf mod a⁴.                              (7.2)

These congruences follow by polynomial Taylor expansion, so they hold for every f, not only a sampled cubic. Since 1−a²f is a unit modulo a⁴, (7.2) gives the exact ideal equality

    Φ((a⁴,r0))=(a⁴,rf).                                     (7.3)

The affine-modification lifting argument of Dubouloz–Moser-Jauslin–Poloni §2 now applies directly: C[E_f]=C[a,Z,u][rf/a⁴] inside C[a,a⁻¹,Z,u]. The automorphism Φ fixes a and maps the two ideals onto one another, so it induces mutually inverse isomorphisms between E_f and E_0. Concretely, if Φ(r0)=(1−a²f)rf+a⁴q, the image of Y0 in the direction C[E_0]→C[E_f] is (1−a²f)Y0+q. Surjectivity follows from the inverse ideal equality, not from incorrectly calling 1−a²f a polynomial unit.

All maps commute with the involution, including the lift (r0 and rf are invariant). Consequently

    (E_f,ι) ≅ (E_0,ι),
    Y\D_f ≅ Y\D_0                                            (7.4)

for every polynomial f∈C[u]. The zero polynomial in (7.4) is only a normal form for the complement; it is not asserted to satisfy the odd-degree cancellation obstruction for A_f.

This is the decisive compatibility check: even the involution-marked double cover and the un-stabilized complement lose the parameter. Stopping at the nonzero cocycle in §5 would have produced a false full-algebra distinction. The explicit symmetric commutator is an implementation of the primary Hamiltonian finite-jet normalization and affine-modification method. The primary Theorem4.2 concerns singular curves z^k+t^ℓ and is NOT applied to our smooth disconnected r0 by assertion; (7.1)–(7.3) supply the needed calculation in this case. No DK/ML hypothesis from that theorem is presumed for E_f.

## 8. Carry the normalizer back to the deleted divisor

An isomorphism of complements is not an isomorphism of pairs. Here one can concretely test the normalizer, instead of merely naming that general caution.

On the a≠0 chart of the original torsor, use capital A,D for its a,d coordinates and put V=v_f. Then

    T[A⁻¹]=C[A,A⁻¹,D,u,V],
    b=(V+D²+A²f(u))/A³,
    c=(1+bD)/A.

In particular A,D,u,V are algebraically independent in this chart. Normalize V to one after adjoining T0 with T0²=V. The coordinates in (5.2) are

    a=A/T0, Z=D/T0−A³/(2T0³), u=u.

Because (7.1) is equivariant, it descends from this double cover to an isomorphism of the original Gm-torsor complements. In the original coordinates, its elementary steps are

    A_±: D↦D ± A F0(u)/4, with u fixed,
    B_±: u↦u ± (AD/V−A⁴/(2V²)), with D fixed.                (8.1)

Both keep A,V fixed. Formula (8.1) is independent of the choice of T0. The full eight-step word is A+,B+,A−,B−,A−,B−,A+,B+.

Let m=deg F0=deg f+1≥4. Work at the generic point V=0 in this a≠0 chart. Initially D,u have pole order zero. The first A-step keeps them finite. In the first B-step the term −A⁴/(2V²) has uniquely largest pole order, so the new u has pole order two. Thereafter, each F0(u) has exactly m times the pole order of u, with nonzero leading coefficient; each subsequent B-step has uniquely dominant term AD/V. The successive orders are

    after B+ : ord_pole(u)=2,
    after A− : ord_pole(D)=2m,
    after B− : ord_pole(u)=2m+1,
    after A− : ord_pole(D)=m(2m+1),
    after B− : ord_pole(u)=2m²+m+1,
    after A+ : ord_pole(D)=m(2m²+m+1),
    after B+ : ord_pole(u)=2m³+m²+m+1.                       (8.2)

At every step the new dominant order is strictly larger than all competing orders, so no cancellation assumption is hidden here. Thus the explicit complement isomorphism has a genuine pole in the pullback of the target regular function u along V=0. It does not extend to a morphism across that divisor. Since u is invariant under fiber scaling, multiplying a torsor lift by a scalar cannot remove this pole. The same obstruction prevents this particular quotient-complement map from extending to an isomorphism of Y with its center.

For example, for cubic f one has m=4 and the final order is 149. This number diagnoses this normalizer only; it is not a lower bound for all possible isomorphisms, an effective complexity theorem, or an invariant claimed to distinguish A_f. Other complement automorphisms could change its boundary behavior. Establishing or excluding an alternative extending map is still an unpaid operation.

## 9. What remains unpaid, without a weaker substitute

The sustained moving-center investigation now has a concrete endpoint stronger than the initial r29 gap. The source/r29 machinery gives integral smooth cancellation fourfolds and the intrinsic DK modification. Arbitrary isomorphisms would preserve the center pair. The center's canonical torsor, involution, nonzero fiber, and complement were all carried through to exact formulas. Classical finite-jet normalization then removes the apparent parameter even equivariantly. Its explicit extension across the center fails by (8.2).

A substantial unmarked-family result would still require an actual invariant of the pairs (Y,D_f), or of the full intrinsic modifications S⊂A_f, that separates specified f's despite (7.4); alternatively one could construct pair/modification isomorphisms and derive a genuinely distinct full operation. No such bridge is established here. Non-equivalence of fixed-base torsor cocycles, variation in a chosen u-fibration, a failed extending map, and existence of equivalent complements do not supply it. In particular no pairwise-nonisomorphic family at fixed thickness is asserted.

Blanc–van Santen's strongest comparison uses principal surface fibers and uniqueness of a surface ruling to force a coordinate to be preserved. Its hypotheses do not include our threefold E_f or the nonprincipal divisor D_f. Ghosh–Gupta and Ghosh–Pal's contraction and polynomial-coefficient-ring comparisons are already reflected in r29's thickness operation; they do not turn the now-normalized complement into an invariant of the omitted divisor. The primary Hamiltonian normalization has been used, not merely listed as a possible competitor.

No theorem is frozen and no author-proof nominee is submitted. The cylinder adaptation, odd-leading-term rigidity, intrinsic DK recovery, complement normal form, and pole diagnostic are retained as research reductions and payments, not separate weaker candidates. This says neither that the family is exhausted nor that all centers or all cancellation fourfolds are isomorphic. It makes no global impossibility or worldwide-priority claim.
