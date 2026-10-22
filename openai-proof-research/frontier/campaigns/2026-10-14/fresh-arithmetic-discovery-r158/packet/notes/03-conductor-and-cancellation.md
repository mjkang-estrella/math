# Conductor descent, strongest local payment, and the operation still unpaid

These are durable prefreeze derivations. No vanishing statement or author theorem is asserted.

## Explicit finite conductor, without a false integral decomposition

Set A=Z[Theta] in its semisimple rational algebra and O=product_d Z[zeta_d]. Although Theta has finite odd order, A need not be O. It is nevertheless possible to bound the exact gluing modulus without finding a basis of the enormous Milnor lattice.

For each occurring d, let e_d be the rational projector to the primitive-d eigenspaces. Fourier inversion in Q[C_m] gives

    e_d = (1/m) sum_{k=0}^{m-1} c_d(k) Theta^k,
    c_d(k)=sum_{a mod d, gcd(a,d)=1} zeta_d^{-ak} in Z.

Thus m e_d is in A. Multiplying by powers of Theta shows m times every standard generator of O_d is in A, and consequently

    m O subset A,     m barLambda subset Lambda subset barLambda,
    barLambda=O Lambda.

This is an inclusion, not a claim that m is the minimal conductor. For l outside {3,5,7,11,13}, A_l=O_l and Lambda_l=barLambda_l. At the five remaining primes put c_l=v_l(m), so c_3=12 and c_5=c_7=c_11=c_13=1. The actual gluing is specified by the finite subgroup

    C_l=Lambda_l/(l^{c_l} barLambda_l)
          subset barLambda_l/(l^{c_l} barLambda_l).

Let barK_l be the equivariant isometry stabilizer of barLambda_l. Since equivariant maps commute with O, K_l is a subgroup of barK_l. Moreover

    K_l = {u in barK_l : u(C_l)=C_l}.

Indeed Lambda_l is exactly the inverse image of C_l. This equality pays the passage from full lattice to a finite residue problem. It does not assert that every automorphism of the finite hermitian module lifts: the finite group to use is the actual reduction image of barK_l.

## Relative unramifiedness pays all maximal-order local determinant groups

Every final index d is divisible by 11*13. The CM quadratic extension E_d/F_d is unramified at every finite place. To see this, fix a rational prime l. In Q(zeta_d)/Q the inertia group at l fixes every prime-to-l root of unity. At least one of zeta_11,zeta_13 is of odd prime order different from l; complex conjugation acts nontrivially on it. Therefore conjugation is not in inertia. The relative inertia subgroup for E_d/F_d is the intersection with {1,conjugation}, and is trivial. The local quadratic algebra is accordingly unramified or split, including above two. This argument concerns the relative CM extension, not the possibly highly ramified cyclotomic extension over Q.

Kirschmer Theorem 3.7 therefore applies in its nonexceptional case on every maximal-order component. Importantly, it applies to arbitrary O-lattices, not only maximal lattices. Hence

    det barK_l = product_{d,v|l} {u in O_{E_d,v}^*: u conjugate(u)=1} =: U_l.

There is no unpaid dyadic norm-surjectivity or ramified-even-rank exception in this saturated problem. Calling the remaining difficulty merely 'local hermitian classification' would miss this payment.

A useful stronger consequence follows directly from the quasi-reflection proof, rather than from an assumed lifting theorem. In an unramified/split local component, scale and norm ideals coincide. Choose a norm generator x in the lattice. For delta of norm one,

    tau_{x,delta}(y)=y+(delta-1) h(y,x)/h(x,x) x

preserves the lattice and has determinant delta. If delta=1 modulo l^{c_l}O, the displayed quotient is integral and tau is the identity modulo l^{c_l} on barLambda_l. Thus it fixes C_l. Applying this independently on each rational component gives

    U_l(c_l):={delta in U_l:delta=1 mod l^{c_l}O} subset det K_l.

For l not dividing m, det K_l=U_l. At bad l the quotient U_l/det K_l is finite and factors through norm-one units of the finite ring O_l/l^{c_l}O_l. Its actual subgroup is determined by determinants of the reduction image preserving C_l. This supplies a finite, exact interface with explicitly bounded moduli; no enormous matrix was constructed or claimed to have been computed.

## What the strongest combined reduction now says

Write U=product_l U_l, Q_full=T(A_f)/(T(Q)det K), and Q_sat=T(A_f)/(T(Q)U). There is an exact sequence at the middle and right

    U/det K  -->  Q_full  -->  Q_sat  -->  1.

The first arrow need not be injective: global norm-one elements can identify residue classes. Its domain is finite, supported at the five primes above. Kirschmer Section 4 identifies Q_sat by norm-one ideal classes (equivalently the specified class-group quotient), so this is an actual arithmetic class obstruction rather than an unspecified failure of approximation. The source's integral operator-module isomorphism proves that the image of our particular chi in Q_sat is killed by two, as derived in note 02. Consequently 2chi lies in the image of the finite conductor determinant quotient. Neither chi=0 nor 2chi=0 in Q_full has been shown.

This is substantially narrower than leaving an arbitrary ideal class or an arbitrary local determinant group unresolved. It also makes clear why treating the full unitary group as simply connected would incorrectly close the argument: its norm-one determinant torus is precisely what Q_full records. Strong approximation has already paid everything in the kernel.

For clarity, even a principal ideal I=alpha O with I conjugate(I)=O need not be presented here as generated by a norm-one element. alpha conjugate(alpha) is only known to be a totally positive unit, and no global unit norm equation was solved. Squaring is different: alpha/conjugate(alpha) has norm one and generates I^2. That is why the proved residual bound is two and not one.

## A concrete integral-gluing calculation

The need to preserve C_l is visible in a three-dimensional calculation; it is not evidence against the source or against the desired improvement. Let Lambda=Z_3^3, let T cyclically permute the three standard basis vectors, and use the ordinary dot product. Its rational decomposition is Q_3 plus Q_3(zeta_3). The rational trivial-character projector is P=(1/3)J, where J is the all-ones matrix. Then

    U=2P-I=(2/3)J-I,
    U^t U=I, U T=T U, U^2=I.

U acts by +1 on the trivial component and -1 on the cyclotomic component, so it preserves the O-saturation, and its nontrivial component is a norm-one scalar. But its entries include 2/3, hence U does not preserve Lambda. Under evaluation at 1 and zeta_3 the integral group ring image has the residue constraint a=b modulo (1-zeta_3), with a reduced modulo 3. The pair (+1,-1) violates it. This example has an eigenvalue-one factor and is not a model of every final source component; its sole role is to demonstrate explicitly the invalidity of 'componentwise integral implies integral on the original lattice.' Original i110's nonintegral projector has the same limited instructional role.

## Why B's stronger marked cancellation has not supplied the missing map

B's lemmas `lem:arith-local-splitting` and `lem:arith-discrepancy` solve a more specific compatibility problem. Its two marked classes b_j have tau(b_j)=1, normalized norm -1/4, coprime denominators n_j, and a known cross pairing. Those facts give actual integral local splittings of the mod-four lattice. The reflection in v0-v1 exchanges them; on each relevant isotypic component the two conjugate involutions have isometric minus spaces. Their determinant/spinor contributions cancel. Strong approximation then patches maps already in the appropriate kernel.

For A's once-squared lattice, the available operator-module isomorphism, local isometries, rational isometry, and integral reversers do not themselves supply two such marked splittings. In particular, no degree-four transfer pair, lens residue tau, or complementary pair of boundary vectors has been constructed on Lambda. Replacing its five-prime conductor data by B's mod-four condition would change the lattice and would not be an application of B.

A small algebraic calculation distinguishes a reverser from B's matched involutions. Over a CM field E/F, put h(x,y)=x conjugate(y), T(x)=zeta x, C(x)=conjugate(x), and R(x)=z x with z conjugate(z)=1. Then C reverses T and preserves the underlying F-bilinear trace form. But

    R^{-1} C R C : x -> z^{-2}x,

whose E-determinant is generally not one. For example z=zeta_3 gives z^{-2}=zeta_3, not one. Conjugation interchanges the T-eigenspaces; it is not a commuting involution with a matched minus space in each of them. This does not disprove the possibility of a different correction. It identifies the missing compatibility in the proposed direct transplant.

By contrast, A's second tensor square makes the determinant product t_gamma^{m_eta}t_eta^{-m_gamma} over all ordered pairs; swapping gamma,eta cancels every term, including collisions. That source operation is fully paid and remains the available closed construction. Using it would restore the source result, not produce a distinct nominee.

## Exact unpaid operation and disposition

To close the proposed uniform improvement one must construct, for every admissible relation in note 02, a rational determinant correction t in T(Q) and local integral lattice automorphisms k_l preserving C_l such that

    det(R^{-1}D_l)=t det(k_l) for every l.

Equivalently one must prove the specific class chi vanishes in Q_full, including its possible saturated two-torsion and the actual conductor residue class. An alternative sufficient construction would give two complementary marked splittings on these same lattices and prove the matched-minus-space cancellation, not merely name it. Neither operation has been constructed. No class is proved nonzero, no counterexample to the improvement is claimed, and no impossibility/exhaustion statement is made.

The finite source certificate does not compute chi. Computing an arbitrary ideal-class group would also not by itself compute the actual C_l stabilizers or the source comparison class. The retained reduction describes exactly what those computations would have to supply, but such future computations are not treated as completed proof.

Disposition: PREFREEZE/no nominee. There is no frozen theorem, author proof, conditional nominee, renamed old target, or weaker restricted replacement.
