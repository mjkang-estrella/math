# Checkpoint 2: an actual torsion tower, and its exact rank boundary

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

The following example is credited to the discussion immediately after Chiodo, arXiv:1107.1489v3, Proposition 3.10. It is NOT an original counterexample or a solution of TFS. The normal-form calculation below checks the operational point without a finite search.

Let

                   P=<x,y,z | x^2=1, y^3=1, xy=z^6>.

Write A=C_2*C_3=<x,y|x^2,y^3>. The word xy has infinite order: its positive powers are reduced words of length 2k, and the inverse powers are likewise nontrivial. Hence

                P = A *_{<xy>=<z^6>} <z>

is a free product with amalgamation along an infinite cyclic subgroup, with both edge maps injective. Normal form embeds both vertex groups. In particular z has infinite order in P.

A finite-order element of an amalgam is conjugate into a vertex group. For completeness, conjugate a word to cyclically reduced normal form. If its amalgam length is at least two, all positive powers retain positive length, so it cannot have finite order. Words of length zero or one lie in a vertex group up to conjugacy. In A the same free-product argument places every finite-order element in a conjugate of C_2 or C_3; <z> has no torsion. Consequently

T_1(P)=<<x,y>>_P,
P/T_1(P)=<z|z^6>=C_6,
T_2(P)=P.

The displayed C_6 is exactly cyclic of order six: sending x,y to 1 and z to a generator of C_6 is a surjection, and those are all remaining relations. Thus removing all original torsion creates new torsion represented by the previously infinite-order z.

For any torsion-free G, the three equations over G with these words but no nonidentity coefficients have exponent matrix

                 [2 0  0]
                 [0 3  0]
                 [1 1 -6],       determinant -36.

Their universal group is U=G*P. Finite-order elements of this free product are conjugate into P, because G is torsion free. Hence

U/T_1(U)=G*C_6,       U/T_2(U)=G.

This is a genuine nonsingular system within TFS's scope, and it has the torsion-free solution x=y=z=1 in G. It refutes both the claim that its universal group is automatically torsion free and the claim that one torsion-removal step must suffice. It does NOT refute TFS or coefficient preservation at all stages.

There is also a concrete warning about omitting the rank hypothesis. Regard the embedded infinite cyclic subgroup C=<z> of P as the coefficient group and x,y as the two unknowns. The same three equations now have exponent rows (2,0),(0,3),(1,1). The rank is 2 with 3 equations, so the system is NOT nonsingular. It is solvable in P, preserving C. In every torsion-free solution, x^2=y^3=1 forces x=y=1, whence z^6=1 and then z=1. Thus it has NO torsion-free solution preserving C. This is an actual failure of arbitrary coefficient-injective de-torsion, located precisely outside TFS. No singular counterexample is offered as the frozen target's counterexample.

As a consistency check on that boundary, add a third unknown u and replace xy=z^6 by xy=z^6 u^k, k!=0. The three rows now have determinant -6k and are independent. This particular system has a torsion-free solution: set x=y=1 and adjoin a k-th root of z^{-6}. If z!=1, amalgamate G with an infinite cyclic root group over the two infinite cyclic subgroups; normal form preserves G and torsion-freeness. If z=1 choose u=1. This elementary repair pays this family only, not general nonsingular systems.
