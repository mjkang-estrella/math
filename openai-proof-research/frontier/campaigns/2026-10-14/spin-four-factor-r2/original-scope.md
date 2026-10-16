# Frozen scope Q4 — four-factor type-D saturation

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT.
Third-party sources remain private with their own rights.

Frozen before sustained proof work in this round. For every integer n >= 2,
let G = Spin(2n,C), with D_2 = A_1 x A_1. Write P_+(D_n) for dominant
integral weights, Q(D_n) for the root lattice, and V(lambda) for the
irreducible complex G-representation of highest weight lambda.

**Q4.** For every lambda_1,lambda_2,lambda_3,lambda_4 in P_+(D_n)
with lambda_1+lambda_2+lambda_3+lambda_4 in Q(D_n), and every positive
integer N,

 (V(N lambda_1) tensor V(N lambda_2) tensor V(N lambda_3)
   tensor V(N lambda_4))^G != 0
 if and only if
 (V(lambda_1) tensor V(lambda_2) tensor V(lambda_3)
   tensor V(lambda_4))^G != 0.

All ranks, zero and singular weights, integral and half-integral spin
weights, both spin nodes, all dilation factors and all chamber-boundary
configurations are included. No ordinary-weight, stable-rank, generic,
fixed-N, specified-diagonal, or root-lattice-diagonal assumption can be
added to report success. Neither factor two/four nor the three-factor
input is a solution. No multiplicity-one or polynomiality claim is made.

Stipulated input: family 204 at openai/math revision
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, thm:main, the exact THREE-factor
saturation theorem, and its actual real-schedule, integral-schedule and
column interfaces where explicitly used. Source truth is stipulated.
Established tensor decompositions and primary antecedents must be credited.

The unpaid operation selected here is simultaneous integral choice of the
intermediate highest weight in two coupled triangle problems. Separate
triple saturation only applies after that intermediate weight is integral
and has both necessary central congruences. Dilation gives a rational
intermediate weight; dividing it is not a proof of integrality. Sam's
arbitrary-factor factor-four theorem and Hong--Shen folding are antecedents,
not scale-one type-D gluing. A complete new integral gluing proof, or an
actual representation-theoretic counterexample to the full statement,
is required. If neither is obtained, retain Q4 UNRESOLVED unchanged.

This is an author research target, not an independent PASS, contribution
nomination, manuscript, formalization or count change. Campaign remains 4/10.
