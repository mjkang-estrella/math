# r201 — completed feasibility derivations, not a frozen nominee

These calculations carry the strongest compatible construction in Source325 through the relevant classical operations. They are retained in full so that “there is a compatibility gap” is not substituted for doing the construction. They are not an author-proof nomination, a manuscript, or a contribution verdict. All spaces and functions below are complex. The entire upstream pin and its operative proofs are accepted as true.

## 1. The correct common starting object

Let H be any nonzero complex Hilbert space, without separability or dimension assumptions, let A be bounded on H, and set K=closure W(A). Let P(K) be the uniform closure of scalar polynomials in C(K). At matrix level m, its norm is the supremum on K of the M_m operator norm. The coefficient size m is finite and independent of the dimension of H.

The source's complete polynomial inequality gives a well-defined unital homomorphism

    u : P(K) -> B(H),       u(p)=p(A),       c=||u||cb <= 2.

To justify every part: zero supremum of a polynomial implies zero evaluation by the source inequality; the same inequality makes evaluation continuous, hence it extends uniquely. Products pass through uniform limits. At each finite matrix level, entrywise polynomial approximation and the original complete estimate give norm at most two. Since u(1)=I and H is nonzero, 1<=c<=2. Here c is the actual complete norm, not merely its upper bound.

For a function holomorphic near K, polynomial approximation on a slightly larger compact convex neighborhood and a fixed resolvent contour identify u with the ordinary holomorphic calculus. This is precisely the source's cor:hilbert passage. Rational functions whose poles lie outside K are included. Poles are never allowed on K.

Paulsen's 1984 theorem, Section 2, gives an invertible similarity making u completely contractive, with attained condition number c. Polar decomposition changes this to a positive similarity without changing its condition number or complete contractivity. After scalar normalization write it as S=H0^(1/2), where

    I <= H0 <= c^2 I,       inf spectrum(H0)=1,
    u_m(F)* (H0 tensor I_m) u_m(F) <= H0 tensor I_m
                             whenever ||F||K <= 1.                 (1)

The supremum and infimum of the spectrum of H0 need not be eigenvalues. That distinction matters in an infinite base space. This is an attained metric for the entire homomorphism. A different similarity making the homomorphism completely contractive must have condition number at least c, by conjugating each matrix-level norm inequality back. Thus the optimum is exactly c.

This conclusion is already a source/Paulsen composition. It is not unpaid merely because the source's explicit finite-dimensional metric proof is stated on one enclosing domain.

## 2. One metric for all enclosing domains, with actual densities

Let Omega be any bounded convex domain with regular real-analytic Jordan boundary such that K is contained in Omega. Fix the source's conformal coordinates f:Omega->D and G:T->boundary Omega, with their collars. Then f belongs to P(K), and

    r_Omega = max_K |f| < 1,
    D_Omega = S f(A) S^-1,
    ||D_Omega|| <= r_Omega.                                      (2)

Thus this SAME S works for every such Omega. The maximum is on K, not on a possibly nonclosed numerical range. The strict inequality in (2) uses compact containment in the open domain; merely having W(A) contained in Omega would not imply it for infinite-dimensional A if its closure touched the boundary.

The source's disk formula works in B(H), without a finite base dimension:

    Phi_D(zeta)=I+sum_(k>=1) [zeta^-k D^k + zeta^k D*^k].          (3)

The series is norm-uniform on T because ||D||<1. Alternatively rho(D)<1 would suffice, by the spectral-radius formula and a geometric bound on powers. For E_zeta=I-D/zeta,

    E_zeta* Phi_D(zeta) E_zeta = I-D*D >=0.

Consequently Phi_D is positive, norm-continuous, has mass I, and has analytic moments D^k. With psi=f o G and the positive angular Jacobian j from the source,

    Lambda_Omega(t)=j(t) Phi_(D_Omega)(psi(t))                    (4)

is positive, norm-continuous, and mass I. It represents v[SAS^-1] for every finite m and every M_m-valued v holomorphic on a neighborhood of closure Omega. The change of variables and scalar composition are exactly those in source prop:density; their norm-convergent series and operator integrals do not need finite-dimensional H. The same S and Lambda_Omega are used for all v and all m.

One can retain a useful coercivity statement for this common metric. The scalar Poisson kernel is between (1-r)/(1+r) and (1+r)/(1-r) when its center has modulus at most r. Equivalently the operator Poisson formula for a contraction of norm at most r gives

    (1-r)/(1+r) I <= Phi_D(zeta) <= (1+r)/(1-r) I.                (5)

For completeness, one way to prove (5) is to apply a unital positive disk-calculus extension for D/r to the scalar function P(rw,zeta); its Fourier series gives precisely (3). Such an extension follows directly from the tT limit construction in Section 3 below. For r=0 the assertion is Phi=I. Multiplication by the positive j gives the corresponding bounds on Lambda. The constants depend on domain separation r and the boundary parametrization, not on H or m.

This also extends to an arbitrary auxiliary Hilbert space E and norm-holomorphic B(E)-valued v near closure Omega: the integral of Lambda tensor v is a norm integral. The map b -> [t -> (Lambda(t)^(1/2) tensor I_E)b] is an isometry into L2(T;H tensor E), and multiplication by I_H tensor v(G(t)) gives the common compression. Norm-continuity supplies strong measurability of each vector-valued integrand even when H and E are nonseparable. No claim about arbitrary nonmeasurable operator-valued boundary data is made.

There is an exact simultaneous optimization statement here. If an invertible R makes every admissible outer-domain calculus completely contractive, then for each matrix polynomial P one may shrink such domains to K and obtain

    ||P[RAR^-1]|| <= max_K ||P||.

So R makes u completely contractive and condition(R)>=c. The S above attains c for the simultaneous family. It need not minimize the condition number for each outer domain separately. For a large disk the individual minimum can be one, even when c>1; these are different optimization problems.

## 3. The actual boundary K and consistency between domains

There is a common positive operator-valued measure on the actual boundary, although a continuous density on that boundary need not exist. Here is a construction, not just an invocation of a limiting measure.

Assume first that K has interior. Its boundary is a Jordan curve because K is compact convex with interior. Let f0:int K->D be conformal, extended homeomorphically to K, and let phi=f0^-1. The function f0 belongs to P(K): fix z0 in int K, replace f0(z) by f0(z0+t(z-z0)) for t<1, approximate this neighborhood-holomorphic function by polynomials on K, and then let t increase to one using uniform continuity. Thus T0=(S u(f0) S^-1) is a contraction, possibly with spectral radius one.

For 0<t<1, formula (3) for tT0 defines a unital completely positive map Psi_t:C(T)->B(H). On a trigonometric polynomial its value converges in operator norm as t increases to one, since each moment tends to T0^k or T0*^k. Uniform contractivity then gives norm convergence on EACH continuous test function by trigonometric approximation. The limit Psi is unital completely positive: at every fixed matrix size its positivity follows by passing to the norm limit. This argument does not assert norm convergence of the densities.

For a function g in P(K), h=g o phi belongs to the disk algebra. Polynomial approximation of h and the identity g=h o f0 imply

    S u(g) S^-1 = Psi(h|T).

Transporting Psi by phi gives a unital completely positive map on C(boundary K), equivalently a positive operator-valued boundary measure mu_K, representing the entire calculus and all its finite matrix levels. This is the explicit single-variable form of the classical Arveson/Naimark operation. It uses no sequence exhausting H.

The extension is unique. Any continuous function on boundary K becomes a continuous function on T under phi. Trigonometric approximation writes it as a uniform limit of combinations of f0^k and conjugate(f0)^k. A positive map representing the analytic calculus must represent the conjugates by adjoints, so it is fixed on this dense set. If K is a segment or point, rotate and translate so that A is self-adjoint (polarization of the vanishing imaginary quadratic form). The spectral theorem supplies the same conclusion with condition one; polynomials are dense in C(K). In all cases the common boundary measure is determined by the analytic calculus and positivity.

For an outer Omega, let B_Omega send a continuous boundary function b to its harmonic extension, restricted to boundary K. This is a positive unital map. For analytic v it preserves v, so

    Psi_Omega = Psi_K o B_Omega                                (6)

represents the same similar-operator calculus. Uniqueness on boundary Omega identifies (6) with the explicit density (4). In the interior conformal parameter its density is concretely

    zeta -> Psi_K( z -> P(f(z),zeta) ),                         (7)

where z lies on boundary K. Since |f(z)|<=r_Omega<1, the scalar kernel in (7) is norm-continuous and bounded above and below by the constants in (5). Its Fourier coefficients recover (3), proving both the formula and the asserted bounds.

If closure Omega1 is contained in Omega2, harmonic uniqueness on Omega1 gives the composition rule for the two harmonic-extension maps. Therefore their positive representations are consistent under harmonic sweeping from the inner to the outer boundary. This compatibility is actually proved; it is not obtained by choosing unrelated optimizing source metrics on each domain.

The actual-boundary measure can have atoms, and uniform bounds on the circle-parameter outer densities can fail. An explicit finite-dimensional example is A=(2N) direct-sum [1], where N=[[0,1],[0,0]]. Then K=Dbar and one optimal common metric is H0=diag(1,4,1). For Omega_R=R D with R>1, the transformed disk image is (N/R) direct-sum [1/R]. Its scalar boundary-density block at zeta=1 equals (R+1)/(R-1), which diverges as R decreases to one. The limiting boundary measure has the scalar summand's atom at 1. This example keeps a nondegenerate limiting K and a fixed circle parametrization; a scalar singleton K alone would not establish that parametrized blowup.

## 4. A metric clipping calculation

Suppose I<=H0<=c^2 I and X*H0 X<=r^2 H0, where 0<=r<=1. Define

    J=max(I,r^2 H0)                                           (8)

by applying the scalar function t -> max(1,r^2 t) to the SINGLE self-adjoint operator H0. This is not a proposed maximum in the Loewner order of noncommuting operators. Since H0>=I,

    r^2 H0 <= J <= H0,
    X*J X <= X*H0 X <= r^2 H0 <= J.                           (9)

Also I<=J<=max(1,c^2 r^2) I. Thus J^(1/2) makes X contractive with condition number at most max(1,cr).

Crucially, (8) is independent of X. It works for every X obeying the same r-bound in H0. At coefficient level m, functional calculus gives

    max(I_(H tensor C^m),r^2(H0 tensor I_m))=J tensor I_m.       (10)

This is the compatibility needed for a complete, rather than scalar, conclusion. An affine convex combination with I also gives an improvement, but (8) is stronger and reaches max(1,cr).

## 5. The strongest joint construction from one underlying operator

Fix any finite d>=1 and scalar functions g1,...,gd holomorphic near K, with

    max_(z in K) max_j |gj(z)| <= r < 1.                       (11)

Put Tj=gj(A). They commute because they are functions of this ONE A. Define the joint evaluation of F, holomorphic near the closed polydisk, by

    F[T1,...,Td] = u_m(F(g1,...,gd)).                          (12)

For polynomials this is the usual sum of commuting products T^alpha tensor B_alpha. Taylor approximation on a slightly larger polydisk identifies (12) with its ordinary joint analytic evaluation. No calculus for an unrelated commuting tuple is smuggled into (12).

The metric J from (8), formed using the same H0 and r, makes the homomorphism (12) completely contractive. In particular, for EVERY finite m and such F,

    ||F[T1,...,Td]|| <= max(1,cr) max_(Dbar^d)||F||
                       <= max(1,2r) max_(Dbar^d)||F||.        (13)

Here is the noncommuting-coefficient compatibility argument. It is essential; knowing only that all Tj become contractions would not prove (13).

Normalize ||F||<=1. First suppose C=F(0) has norm <1. Let M_C be the standard Potapov--Mobius map of the matrix ball,

    M_C(Z)=(I-CC*)^(-1/2)(Z+C)(I+C*Z)^(-1)(I-C*C)^(1/2).

Its inverse is M_-C. Let G=M_-C o F. Then G(0)=0 and ||G||<=1 on the polydisk. All inverses are defined on a neighborhood of the closed polydisk, since ||C||<1. For w with max_j|w_j|<=r, the disk Schwarz lemma applied to scalar matrix elements of lambda -> G(lambda w/r) gives ||G(w)||<=r (the case r=0 is immediate). Consequently

    X=u_m(G(g1,...,gd))

satisfies X*H0_m X<=r^2 H0_m by (1), where H0_m=H0 tensor I_m. Equations (9)--(10) imply that Y=J_m^(1/2) X J_m^(-1/2) is a contraction.

The matrices C, I-CC*, and I-C*C act in the coefficient factor and commute with J_m. Ordered multiplicativity of u_m and evaluation of inverses therefore give

    J_m^(1/2) F[T] J_m^(-1/2)=M_(I_H tensor C)(Y).

No factors C and X were commuted. The exact identity

    I-M_C(Y)*M_C(Y)
      = D_C (I+Y*C)^(-1) (I-Y*Y) (I+C*Y)^(-1) D_C >=0,
    D_C=(I-C*C)^(1/2),

proves contractivity. This is also the B=I case of Hartz--de Vries, Lemma 3.1; their actual ordered calculation has been read. If ||F(0)||=1, replace F by tF, t<1, and pass to the norm limit. This proves (13) at the full stated scope.

The same metric works for any collection of gj satisfying (11), because it is independent of d and of the chosen tests; the claim above only requires finite subcollections. This is simultaneous similarity with a proved common-calculus hypothesis, not a conclusion from the individual numerical ranges of several unrelated operators.

The uniform constant in (13) cannot be reduced as a function of r. For 0<r<1 take

    N = [[0,1],[0,0]],    A=2r N,    K=r Dbar,    g1(z)=z.

The test F(w)=w has evaluation norm 2r, and the constant function I has norm one. The source gives c=2 on K. Hence the worst possible constant is exactly max(1,2r). At r=0 only the constant test is needed. This is the source's classical nilpotent sharpness example, scaled; it is not a new example.

## 6. Joint positive representations: what is attained and what costs slack

At the sharp constant there is a positive torus MEASURE common to every joint test and coefficient size. Indeed, after the similarity in Section 5 the evaluation homomorphism of the polydisk algebra is completely contractive. Arveson's Theorem 1.2.2, whose proof was read, extends it to a unital completely positive map Psi:C(T^d)->B(H). This supplies the common measure and, by Naimark/Stinespring, a common normal torus dilation. One such extension is chosen once. In several variables it need not be unique; analytic moments do not specify all mixed Fourier moments.

The optimal joint similarity condition is attained, not merely bounded above: apply Paulsen to this joint homomorphism. Alternatively its feasible metrics form the intersection, over ALL matrix polynomial tests F of norm <=1, of the weak-operator-closed constraints

    F[T]* (H tensor I_m) F[T] <= H tensor I_m,
    I<=H<=tau I.

On bounded operator intervals weak-operator compactness holds even without separability. A net approaching the infimum therefore attains it. No eigenvector at an endpoint is needed. This is again a classical compactness/Paulsen operation.

A common continuous torus density can be constructed with an arbitrarily small condition-number relaxation. Choose r<s<1, apply Section 5 to gj/s, and let

    J_s=max(I,(r/s)^2 H0),
    Ej=J_s^(1/2) (Tj/s) J_s^(-1/2).

Their joint calculus is completely contractive, so fix a positive extension Psi_s on C(T^d). With normalized product circle measure sigma_d define

    Lambda_s(zeta)=Psi_s(omega -> product_(j=1..d) P_s(zeta_j conjugate(omega_j))),
    P_s(eta)=(1-s^2)/|1-s eta|^2.                             (14)

This is norm-continuous, positive, and mass I. Its analytic moment alpha is s^|alpha| E^alpha, exactly the evaluation of the transformed T tuple. Polynomial approximation therefore proves the representation for every F in Section 5 and every finite m, with ONE Lambda_s. Positivity of Psi_s gives the explicit operator bounds

    ((1-s)/(1+s))^d I <= Lambda_s(zeta)
                         <= ((1+s)/(1-s))^d I.                (15)

The condition number is at most max(1,cr/s), tending to max(1,cr) as s increases to one. The bounds depend on d and s, not on H or m. One must not take s=1 in (14)--(15) and assert a continuous density: the density bounds degenerate. For r=0 the zero tuple has density I and similarity I directly.

## 7. An exact failure at the apparently natural density endpoint

Even with a finite base, analytic functions, and strict spectral separation from the torus, the sharp similarity need not permit ANY positive density absolutely continuous with respect to full product Haar measure.

Fix 1/2<=r<1. On C^2 put A=2r N as above and choose d=2, g1(z)=g2(z)=z. The sharp joint condition is 2r. A feasible similarity attaining this condition yields the duplicated tuple (D,D), with D=R A R^-1 a contraction. Since

    2r=||A|| <= condition(R)||D||=2r ||D||,

one has ||D||=1. As the base is finite, choose a unit vector x with ||Dx||=1. Its spectrum is still {0}.

Suppose a positive integrable density Lambda on T^2, of mass I, represented every polynomial of (D,D). The isometric compression built from Lambda^(1/2) would represent the scalar polynomial

    F(z1,z2)=(z1+z2)/2.

Its evaluation is D. Equality of the norm at x in the two contraction inequalities forces

    integral_(T^2) (1-|F(zeta)|^2) <Lambda(zeta)x,x> d sigma_2 = 0.   (16)

The integrand is nonnegative. On T^2, |F|=1 only on the diagonal zeta1=zeta2, a product-Haar null set. Equation (16) therefore implies <Lambda x,x>=0 almost everywhere. This contradicts its integral being ||x||^2=1. Thus not even a merely integrable positive Haar density exists at ANY optimal similarity for this tuple.

A singular common measure does exist: for D=N, use the one-circle source density

    Phi_N(zeta) = [[1,zeta^-1],[zeta,1]]

and push it to the diagonal (zeta,zeta). It represents all joint polynomials and all coefficient sizes because F(D,D) is the one-variable evaluation of z -> F(z,z). This reconciles the obstruction with Sections 5--6: a torus measure is attainable; a full-dimensional continuous torus density may require slack. The obstruction is not a failure of the source's one-circle density theorem.

## 8. A domain-specific quantitative consequence and its limits

For one admissible outer domain Omega let f:Omega->D and define

    r_* = min_(a in D) max_(z in K) |(f(z)-a)/(1-conjugate(a) f(z))|.  (17)

The minimum is attained. The objective is continuous in a; because f(K) is compactly inside D, it tends uniformly to one as |a| tends to one, whereas at a=0 it is strictly below one. Thus minimizing a lie in a compact subdisk. A singleton K gives r_*=0 and A scalar.

Apply (8) to h(A), where h is the minimizing disk automorphism composed with f. It is contractive in the clipped metric, and the inverse disk automorphism preserves contractivity. Hence Omega is a complete max(1,c r_*)-spectral set for A, with a single similarity and a single source-form density common to all coefficient levels and neighborhood-holomorphic tests. In particular its bound is strictly below two whenever K is strictly inside Omega. Its individual optimum is attained by Paulsen (or the weak-operator metric argument), with value no larger than this bound.

For Omega=D and K=r Dbar, (17) equals r. To see the lower bound, choose the point -r a/|a| if a is nonzero; its pseudohyperbolic distance from a is (r+|a|)/(1+r|a|)>=r. The choice a=0 achieves r. Thus the nilpotent example also proves sharpness of this uniform quantitative consequence.

The clipped density can lose coercivity even though the spectrum is strictly inside. With H0=diag(1,4), A=2rN and r>=1/2, (8) gives J=diag(1,4r^2) and D=N. The density Phi_N has rank one at every boundary point. This is consistent with the source, which assumes spectral radius below one but allows norm one. It is not consistent with an unjustified claim that an optimizing density is uniformly positive definite.

## 9. Why these calculations do not solve unrelated joint problems

Two independent operators A1=2rN and A2=2rN* with r>1/2 each have numerical range r Dbar, strictly inside D. Their product has spectral radius 4r^2>1. A common similarity making both contractions would make the product a contraction, which is impossible.

Commutativity alone does not supply the dimension-independent bound in Section 5 either. On (C^2) tensor d let Aj be 2rN on factor j and the identity on the others. The Aj commute and each has numerical range r Dbar. But

    ||A1 ... Ad||=(2r)^d,

so any common contractive similarity has condition at least (2r)^d. Tensoring the two-dimensional similarities attains this lower bound. For r>1/2 and d>1 it exceeds max(1,2r). This is a direct obstruction to deleting the single-underlying-calculus hypothesis, not an assertion about the best general multivariable theorem.

Unbounded operators, arbitrary commuting tuples, and unrelated families are outside the deductions. No boundary density is transported between different operators merely because their individual numerical ranges coincide.

## 10. Research disposition of the construction

The strongest completed construction is: one attained metric for P(K); compatible common boundary representations for all outer domains; a complete joint pullback calculus with exact uniform factor max(1,2r); and a common continuous torus density with arbitrary condition slack, together with an exact obstruction at the sharp density endpoint.

The actual operations are Source325's complete calculus and common representation, Paulsen's attained similarity, one-variable Schwarz applied to matrix elements, spectral functional calculus of one metric, the classical ordered Potapov transform, and Arveson plus product Poisson smoothing. The endpoint obstruction is equality in a positive compression for a classical nilpotent example. After this strongest reduction, no separate nonroutine mathematical operation has been isolated for a substantial nomination. The mathematics above is retained, but it is not frozen or relabelled as a new substantial theorem.

There is no unresolved algebraic step hidden inside the displayed joint construction. The stronger exact-continuous-density target is false in the full stated class, by Section 7. Obtaining continuous densities at optimality under additional hypotheses would require a genuinely different target and further primary/history work; no such target is frozen here. Absence of a nominee is not an exhaustion claim, a favorable novelty judgment, or a count change.
