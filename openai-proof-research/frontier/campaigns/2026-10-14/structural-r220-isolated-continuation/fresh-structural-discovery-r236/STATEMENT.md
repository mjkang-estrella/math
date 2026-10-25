# Frozen research statement S236 — prescribed critical harmonic filtration

Frozen after the operative source, selected primary and guarded original-history reading recorded in the accompanying records, and before writing the full author proof. This statement and its proof scope are immutable. It is not an assigned correctness or contribution grade.

Let m=2s-1 with integer s>=4. Let 0<a_*<1<q_* satisfy

    a_*^2 < min_{1<=q<=q_*} q^(1/m) min{q, 1-2(q-1)/(m-1)}.             (S1)

Write g_0 for the unit round metric on S^m and fix an orthogonal complex structure J_0 on R^(m+1). Let V_l be the real round spherical harmonics of degree l, with the round L2 inner product, dimension

    N_l = binom(l+m,m)-binom(l+m-2,m),

where the second binomial is zero for l<2. On V_l the operator -D_(J_0)^2 is self-adjoint, with its actual real multiplicities. Fix an orthonormal eigenbasis e_(l,1),...,e_(l,N_l), and denote its eigenvalues by nu_(l,i). Thus nu_(l,i)=(2b-l)^2 for the corresponding Hopf-charge component, with conjugate complex components combined into their real dimension.

Define positive numbers d_(l,i) for l>=1 by

    d_(l,i)^2+(m-1)d_(l,i)
      = a_*^(-2) q_*^(1/m) [l(l+m-1)+(q_*^(-1)-1)nu_(l,i)].          (S2)

For EACH l>=2 prescribe an arbitrary partition P_l of {1,...,N_l} into nonempty sets, with a cyclic ordering on each set. No uniform bound on the number or lengths of the cycles, their variation with l, or any associated finite-control constants is imposed. For C in P_l set

    mu_C = |C|^(-1) sum_(i in C) d_(l,i).

All the l=1 roots coincide; call their value d_1.

There exists ONE complete smooth Riemannian metric g on R^(m+1), Euclidean in a neighborhood of the origin o, with Ric_g>=0 and normalized asymptotic volume ratio

    lim_(R->infinity) Vol_g(B_g(o,R))/(omega_(m+1)R^(m+1)) = a_*^m,

having nonisometric tangent cones at infinity, including the round-link cone with link a_*^2 g_0 and the Berger-link cone with link

    a_*^2 q_*^(-1/m) [g_0+(q_*-1)eta_(J_0)^2].

There exist spaces E_1 and E_(l,C) of real smooth GLOBAL harmonic functions, of dimensions m+1 and |C| respectively, such that for EVERY real d>=0 the entire pointwise polynomial-growth space has the exact direct-sum description

    H_d(M,g) = R 1
       direct-sum [E_1 if d_1<=d]
       direct-sum bigoplus_{l>=2, C in P_l, mu_C<=d} E_(l,C).        (S3)

Here H_d consists of all real harmonic u with |u(x)|<=A_u(1+dist_g(o,x))^d for a finite constant A_u. The right side is a finite sum for every d. This convention is unchanged by choosing a different fixed basepoint.

More precisely, each nonzero u in E_(l,C) has exact sphere growth exponent

    lim_(R->infinity) log ||u||_(L-infinity(partial B_g(o,R)))/log R
       = mu_C,                                                    (S4)

and, for some c_l>0, C_u<infinity and R_u<infinity,

    ||u||_(L-infinity(partial B_g(o,R)))
       <= C_u R^(mu_C) exp[-c_l(log R)^(15/16)]   for R>=R_u.       (S5)

The analogous assertions hold for nonzero u in E_1 with exponent d_1. In particular every stated critical exponent is INCLUDED, with the exact O(R^mu) endpoint and no logarithmic loss. For an arbitrary nonconstant element of the finite direct sum, its exact exponent is the maximum of its present cycle exponents (including d_1).

Proof scope: execute one countable but locally finite metric construction; simultaneous exact full-period transfer on each finite active block with no degree-uniform inverse hypothesis; regularity at the center; all interfaces and all-radius estimates; all-order smooth local geometry, Ricci sign, completeness and volume asymptotics; cone limits; and exclusion of every remaining angular mode for an arbitrary polynomial-growth harmonic function. The countable construction may depend on the entire prescribed sequence of partitions. It is not a claim of uniform perturbation stability, arbitrary real jump locations, a three-dimensional result, or a formalized theorem.

Nonvacuity requirement included in the proof scope: verify compatible parameters and two prescribed partitions which yield distinct full growth filtrations. Use m=7, a_*^2=9/10, q_*=101/100 and pair one charge-zero and one charge-square-four real V_2 vector, versus leaving both singleton, with all other partitions identical.
