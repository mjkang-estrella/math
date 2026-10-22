# Integral block balance and the finite gluing calculation

PREFREEZE derivations. No candidate theorem was frozen. The first reduction is a direct extension of a source induction and is not offered as a substantial result. The finite enumeration is a worked instance of primary overlattice methods, also not a nominee.

## 1. Starting the block induction at a cubic

Let X and Y be smooth complex cubic fourfolds with h31=1, rank T=21, and End_Hdg(T_Q)=Q. Put d=|disc T_X|, and suppose d exceeds the source's ineffective d0 and is greater than two. For this calculation assume a birational map f:X --> Y. Both endpoints are smooth Picard-one Fano fourfolds, hence the Mori spaces over points required by sf:vanishing. All varieties in a smooth weak factorization are rationally connected.

Because G_X is a unital Q-subalgebra of End_Hdg(T_X,Q)=Q, G_X=Q. Initialize the whole-block induction with the one block T_X, instead of with the empty lattice at P4. At a surface blowup the integral direct sum and product algebra in gw:blowup add a block. At a surface blowdown the removed identity is a primitive central idempotent of the existing Q^m. It therefore removes one whole block. Intersecting that rational summand with the ambient integral lattice recovers exactly its saturated integral lattice and form. No cancellation of only part of an isomorphic block is permitted. This argument is word-for-word the primitive-idempotent step of gw:blocks with a different initial state.

Fix the integral Hodge-isometry class tau of T_X. Let m_tau(i) count blocks of class tau at the i-th stage. By source gw:hodge, every nonzero block has nonzero (3,1) part, so the final h31(Y)=1 forces precisely one nonzero final block. Consequently

    m_tau(0)=1,
    m_tau(final)=1 if T_Y is integrally Hodge-isometric to T_X, and 0 otherwise.

Let S_tau be the collection of Picard-one K3 surfaces whose shifted transcendental lattice is tau. Every center adding or removing tau is birational to a member of S_tau by gw:k3-center; conversely every center tested by S_tau has this whole shifted lattice. These surfaces all have degree d and trivial automorphisms. Projective-bundle invariance and the sign convention give

    c_(S_tau)(f) = m_tau(final)-1.

The source vanishing theorem gives c_(S_tau)(f)=0. Thus the calculation forces T_Y to be integrally Hodge-isometric to T_X, and in particular the two discriminants are equal. If S_tau were empty, a tau block could not be removed, which gives the same conclusion directly. For admissible cubics the untwisted K3 association already makes this empty case irrelevant.

This is an isometry-class conclusion. It does NOT show that a particular cohomological correspondence f_* is the resulting isometry. The initial block can be removed and a different block of the same class can be added. Even scalar algebras have no memory of an absent block. It does NOT assert equality of full cubic primitive Hodge lattices or isomorphism of X and Y. In the very general admissible situation, the strongest primary partner criterion identifies the remaining alternatives as Fourier--Mukai partners. That criterion and this direct source composition are paid reductions, not a new full-scope construction.

## 2. What must be added to a transcendental lattice

Use the cup-product sign convention of the cubic, so that its primitive lattice Lambda has signature (20,2) and discriminant three. Write A=H4(X,Z) intersect H22(X), and N=A intersect (h^2)^perp. In the generic rank-two case, the elementary labelled Gram matrices are

    d=2 mod 6: A has matrix [[3,1],[1,(d+1)/3]],
    d=0 mod 6: A has matrix diag(3,d/3).

For the first matrix, v=3 sigma-h^2 is perpendicular to h^2 and has square 3d, so N=<3d>. For the second matrix, N=<d/3>. A primitive lattice Lambda containing N orthogonally-sum T is specified by an isotropic subgroup

    H <= D(N) orthogonal-sum D(T),  q_N+q_T on H equals zero,

whose projections to both discriminant groups are injective. The latter condition is exactly the primitivity of both summands. The discriminant group of the overlattice is H^perp/H. Since det Lambda=3,

    |H|^2 = det(N) det(T)/3,
    |H|=d when d=2 mod 6,
    |H|=d/3 when d=0 mod 6.

Two such embeddings with a fixed Hodge structure on T are equivalent only under the actual O(N) x O_Hdg(T) action. In rank one O(N)={+1,-1}; when End_Hdg(T_Q)=Q, its integral Hodge isometries are likewise {+1,-1}. Given isometries phi:N_X -> N_Y and psi:T_X -> T_Y, the elementary extension criterion is exactly

    (bar(phi) direct-sum bar(psi))(H_X) = H_Y.                 (G)

Necessity follows by reducing an extending isometry modulo N+T. Sufficiency follows because the integral overlattice is the inverse image of H under (N+T)^* -> D(N+T). This is a finite, identifiable interface. Merely matching determinants, signatures and T leaves (G) undecided.

The full H4 lattice is odd, and its distinguished h^2 has square three. One must not apply even discriminant-quadratic-form formulas to that odd lattice without the appropriate refinement. Working in the even primitive lattice above avoids this error. To obtain full cubic cohomology one must also account for adjoining the distinguished h^2 in its prescribed position. The primary period/Torelli argument addresses this in the partner enumeration; the source whole-block algebra does not.

## 3. An explicit finite quadratic-module computation

Take d=182=2*7*13. This is an arithmetic example only. There is NO assertion that 182 exceeds d0, and no assertion here that a specific cubic of discriminant 182 is irrational. A degree-d Picard-one K3 has primitive transcendental discriminant form -1/d; after the cubic sign shift it is +1/d. Set

    D(N)=Z/(3d), q_N(a)=a^2/(3d) mod 2Z,
    D(T)=Z/d,    q_T(b)=b^2/d mod 2Z.

For a unit u mod d define H_u=< (3,u) >. It has order d, and each projection is injective. Isotropy is equivalent to

    (3+u^2)/d in 2Z, or u^2=-3 mod 2d.

The four solutions mod d are 19,33,149,163. The independent sign actions on N and T replace u by -u; hence there are two orbits,

    {19,163},  {33,149}.

There is no sign action taking one orbit to the other. Both give the same T and the same determinant of the final primitive lattice. Explicitly,

    H_u^perp = { (a,b) : a+u*b=0 mod d }.

It has order 3d. The element z=(d,0) lies in H_u^perp, has order three, and is not in H_u, because d is prime to three whereas the first coordinate of every element of H_u is divisible by three. Thus

    H_u^perp/H_u = <z>,   q(z)=d/3=2/3 mod 2Z.

This is the cubic discriminant form, independently of u. The bounded exact-integer calculation in ../finite_calculation.py verifies the orders, isotropy, projection injectivity, three cosets, and sign orbits. Its JSON output records the calculation, not a mathematical gate. The same facts were derived above without relying on finite enumeration.

The primary Fan--Lai realization argument goes beyond finite modules: the indefinite primitive lattice is the required one, and the rank-one algebraic part has no excluded root or long-root period. Their Proposition 2.6 gives two actual Fourier--Mukai partners for a very general cubic in this divisor. That result is already primary literature. We do not claim that these partners are nonbirational.

There is no dependence on the small numerical example for the structural issue. For

    d=2*7^a*13^b, a,b>=1,

admissibility holds and these d are unbounded. At each odd prime power, -3 has two distinct roots, and they lift uniquely; modulo four there are two. Chinese remaindering gives eight roots modulo 2d, hence four modulo d and two sign orbits. The root existence at 7 and 13 follows already from 19^2=-3 mod 7 and 19^2=-3 mod 13, with nonzero derivative; higher exponents follow by the elementary linear correction step. Thus sufficiently large members of this sequence lie above the source's existential threshold and still have two gluing orbits. This is only a compatibility check with the paid headline and primary partner enumeration. It provides neither an effective exponent nor a new irrationality statement.

## 4. Why the full blowup lattice does not yet close (G)

For a surface blowup one has the orthogonal integral cohomological decomposition

    H4(Bl_Z M,Z)/tors = H4(M,Z)/tors orthogonal-sum H2(Z,Z)/tors(-1).

It retains more than T: the algebraic part, its finite discriminant gluing to T, and the exceptional summand are all present. The source operator algebra canonically splits the rational T blocks, but does not assert an equally canonical decomposition of all algebraic classes into pieces attached to those blocks. Taking a rational projector image on T does not choose a primitive polarization in the K3 summand or a cubic class of square three in the residual algebraic lattice.

Along a weak factorization, each local integral isometry could be represented by matrices U_i. On the algebraic lattices one would have to enforce integral equations

    U_i^t Q_(i+1) U_i = Q_i direct-sum Q_(center),
    the corresponding finite discriminant gluing compatibility,
    and the endpoint conditions on the distinguished cubic h^2 classes.

For the reverse step use the inverse isometry. Point and curve centers contribute only diagonal Hodge classes, but these are still allowed algebraic lattice directions in these equations. Hence omitting them is unjustified when seeking (G). The source supplies the equations on the T summands, not a solution with the required endpoint algebraic markings.

One may stabilize these local cohomology isometries and telescope along the zigzag to an isometry after adjoining the center contributions on opposite sides. This uses only the given weak factorization; it does not assume a common resolution by smooth blowup towers on both sides, which would be an additional factorization assertion. Such stable transport still does not give cancellation preserving the endpoint distinguished h^2 and the finite subgroup H. The concrete missing step is a geometric, integrally marked cancellation/transport law implying (G), or an alternative operation that distinguishes the gluing while respecting every local link. The next note tests the source's strongest available singleton constraints against this interface.
