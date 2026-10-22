# Once-squared feasibility construction and exact adelic reduction

Status: PREFREEZE calculations, no theorem frozen. The proposed operation is to replace A's second tensor square by a determinant correction on its actual lattice, uniformly for the source's integer-relation construction. A merely conditional version is not a nominee.

## Full feasibility scope

For every finitely supported integer family (e_b) on 0<b<3^11/2, 3 not dividing b, satisfying the two exact products in note 01 and E=sum e_b>0, use A's specified chain-and-tail procedure, its balancing 4E squares, its two common cubes, and its fifth/seventh-power preparation. No arbitrary isolated germs, nonisolated germs, different multiplicity pairs, or freely varying deformations enter this scope. Form

    g_j = q_j(X) + q_j(Y) + u_1^3+...+u_6^3 + v^11+w^13.

The desired full conclusion would be an ambient equivalence and topological right equivalence of g_1,g_2. This is an exploratory specification of what must close, not frozen theorem bytes. We do not assert that conclusion.

Everything before integral isometry can be carried out. N'=2s+8=2s0+12 is divisible by four. The least degrees remain 2 and 3. The Hessian ranks are 8E and zero. The separated-gradient proof gives isolatedness. N'>2, so the repeated-factor argument gives reducedness. Common real coefficients remain available. There is no perturbation of coefficients or passage to nonreduced schemes.

The first tensor square of (L_j,T_j,B_j), followed by U and V, has all the local and rational equivariant isometries supplied by A. The symmetric twist of its actual Seifert form agrees with this tensor description up to a common convention sign, since all the grouped numbers of variables are even. The same recovery S=B Theta^{-r} works. A's six-cube signature calculation applies to any preceding nondegenerate equivariant factor, not specifically to the fourth tensor power: in every nonzero tensor-eigenvalue summand a nonzero diagonal entry multiplied by the positive and negative cube entries gives both signs. Each component has dimension at least 21.

The monodromy Theta has order dividing

    m=3^12*5*7*11*13=2659862205.

Every eigenvalue contains primitive 11th- and 13th-root parts; the preceding factors have order dividing 3^12*5*7, so neither can cancel. Thus every cyclotomic index d occurring is divisible by 143, and neither +1 nor -1 occurs. The proof that det(1-Theta)=1, Milnor connectivity, the simple-knot conditions, and the even-variable sign convention all remain within the source's actual arguments. N' divisible by four is already even, which is what those displayed algebraic/topological operations use. The original divisible-by-eight conclusion is not being silently rewritten: a new integral isometry would still have to be proved before applying those operations to g_j.

For the supplied relation, s0 is the integer recorded by the explicit verifier. The exact proposed N'=2s0+12 is recorded in calculation-values.json. This arithmetic is only a feasibility dimension, not an example claimed to satisfy the missing topological conclusion.

## Exact determinant obstruction on the full lattice

Write Lambda for the integral lattice of g_1 and Lambda_2 for that of g_2, with their symmetric forms and common rational monodromy algebra. Choose a rational equivariant isometry R:Lambda_Q->(Lambda_2)_Q and integral local equivariant isometries D_l. Let

    H=product_d Res_{F_d/Q} U(h_d),
    G=product_d Res_{F_d/Q} SU(h_d),
    T=product_d Res_{F_d/Q} U(1,E_d/F_d),

where E_d=Q(zeta_d), F_d=E_d^+, and h_d is the nondegenerate hermitian form obtained from the symmetric invariant pairing. Products run only over actually occurring rational cyclotomic components. Let K_l=Stab_H(Q_l)(Lambda_l); these are the full actual integral lattice stabilizers. Let K=product_l K_l and a=(R^{-1}D_l)_l in H(A_f). For almost all primes R itself is integral, so D_l can be chosen equal to R there. Consequently a is a legitimate finite adele.

An integral equivariant isometry exists exactly when H(Q) intersects aK. Necessity follows by comparing it with every D_l. Conversely any h in that intersection makes Rh carry Lambda_l onto (Lambda_2)_l for every l, hence carries the global free Z-lattices onto one another.

The determinant sequence H->T is onto on rational points: diagonalize a hermitian space over its CM field, choose a nonisotropic rational line, and multiply that line by any scalar of norm one. Its determinant is the prescribed scalar. This is a rational construction; it does not assert integrality of the line or of that map. The analogous local assertion is also valid.

Put

    chi(Lambda,R,D)=[det a] in T(A_f)/(T(Q) det K).

This class vanishes if and only if the desired integral isometry exists. Here is sufficiency with the order of multiplication explicit. If det a=t det k with t in T(Q), k in K, choose h in H(Q) with det h=t. Then b=h^{-1}ak^{-1} belongs to G(A_f). The open set b(K intersect G(A_f)) meets G(Q) by the applicable strong approximation theorem: each h_d has rank at least 21, is indefinite at a real place, and SU is simply connected and absolutely almost simple over F_d. Choose g in this intersection. Then hg belongs to aK, as required. Necessity is immediate by taking determinants. This uses strong approximation only after the determinant has been killed.

Changing R multiplies det a by a rational determinant. Changing D_l multiplies it by det K_l. Thus chi is independent of the choices. This identifies the exact interface; it does not show the class vanishes. The reduction itself is standard arithmetic of indefinite hermitian lattices and is supporting work, not a claimed substantial new theorem.

## Source module isomorphism removes an unrestricted class-group gap

A also supplies an integral monodromy-module isomorphism before any form isometry. Tensoring it twice and with the common U,V gives an isomorphism of the actual Z[Theta]-modules Lambda and Lambda_2. It is essential to use this extra payment rather than treating the two lattices as an arbitrary genus pair.

Let O=product_d O_{E_d} and barLambda=O Lambda. Put barLambda_2=O Lambda_2. The module isomorphism extends to an O-module isomorphism of these saturations. After identifying rational spaces by R, their determinant ideals therefore have the same ideal class on every cyclotomic component. If I_d is the fractional ideal with local generators det(a_l)_d, this means I_d is principal, say I_d=alpha_d O_{E_d}. Since det(a_l) has norm one, I_d*conjugate(I_d)=O. Hence alpha_d*conjugate(alpha_d) is a unit of F_d.

The rational scalar t_d=alpha_d/conjugate(alpha_d) has norm one and principal ideal I_d^2. Consequently (det a)_d^2/t_d is a unit at every finite place. Thus the image of chi in the saturated-lattice determinant quotient has order dividing two. This is a proved tightening of the reduction; it does not assume a unit of F_d is the norm of a global unit of E_d. Making that latter assumption would erase precisely the possible residual class without justification.

Equivalently, the remaining saturated special-genus class belongs to the kernel of the natural principal-ideal-class test. That kernel is killed by two by the displayed alpha/conjugate(alpha) calculation. No computation of its actual value for the supplied relation, or uniform vanishing for all relations, has been obtained here.
