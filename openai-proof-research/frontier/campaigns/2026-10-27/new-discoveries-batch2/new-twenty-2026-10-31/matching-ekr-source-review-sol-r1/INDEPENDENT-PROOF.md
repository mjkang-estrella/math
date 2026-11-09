# Independent ordinary proof for328748

This is a hand proof, not a program output, enumeration, imported author deduction, or formal certificate.

For an integer n>=54 let V=Fin n x Fin2. Put a_i=(i,0), b_i=(i,1), and E_i={a_i,b_i}, an UNORDERED two-element subset of V. The complete simple graph on V has as edges all two-element subsets. A perfect matching is a set of these edges such that every vertex belongs to exactly one edge. Thus no orientation, multiedges, repeated edges, or partial matching is being counted.

Let E={E_i:i in Fin n}. These n edges are disjoint and cover V. For i nonzero and epsilon in {0,1}, define cross-edge sets
 C_i^0={{a_0,a_i},{b_0,b_i}},
 C_i^1={{a_0,b_i},{b_0,a_i}},
and M_i^epsilon=(E minus {E_0,E_i}) union C_i^epsilon.
Both cross-edge sets partition exactly the four distinct vertices a_0,b_0,a_i,b_i; their two edges are distinct and are not base edges, since their first coordinates differ. All remaining base edges use other first coordinates. It follows directly that every M_i^epsilon is a genuine perfect matching with n edges. E also is such a matching.

Let F_n={E} union {M_i^epsilon:i!=0,epsilon in {0,1}}. In M_i^epsilon the missing base indices are exactly {0,i}. Consequently E differs from every switch, and equal switches must have equal i. For fixed i the unique edge containing a_0 has partner a_i for epsilon0 and b_i for epsilon1, which are different vertices. Hence these switches differ as unordered edge sets. This proves injectivity and disjointness without enumeration. There are n-1 allowed i and two choices for epsilon, so |F_n|=1+2(n-1)=2n-1. In particular F_54 has 1+2*53=107 members, comprising the base and106 switches.

All intersection cases follow as exact edge-set identities:
(1) E intersect M_i^epsilon = E minus {E_0,E_i}, cardinal n-2.
(2) M_i^0 intersect M_i^1 = E minus {E_0,E_i}, cardinal n-2: their cross edges have different partners at each central vertex, so none coincide even as unordered pairs.
(3) If i!=j, M_i^epsilon intersect M_j^delta = E minus {E_0,E_i,E_j}, cardinal n-3. No cross edge is any base edge. A cross edge for i has first-coordinate support {0,i}, while one for j has support {0,j}; these differ, precluding equality even with endpoints reversed. Base edge E_i is missing in the first switch and E_j in the second. These facts prove both inclusions in the asserted identity.
(4) Each member intersect itself is itself, cardinal n. Reversing the order of a pair changes no intersection. Thus the list covers every ordered pair, including selfpairs.

At n=54 the three distinct-pair cases are52,52,51; selfpairs give54. Each is strictly greater than50. With t=50 the printed bound is (2(54-50)-1)!!=7!!=7*5*3*1=105, whereas107>105. Relabel V bijectively with [108], for example a_i to2i+1 and b_i to2i+2. A vertex bijection induces an injective map on unordered edges and preserves membership, intersections and family cardinality, hence gives an actual family of perfect matchings of K108 as required by the literal statement.

More generally choose t=n-4. Then the minimum intersection n-3 exceeds t, selfpairs satisfy n>t, and the printed right side stays7!!=105. For every n>=54, |F_n|=2n-1>=107>105. Here t>=50 and t<n, so no issue at an undefined negative double factorial or zero parameter is used. The elementary identity 2n-1=107+2(n-54) justifies the inequality. This is one family, not additional outcomes. As n increases t also increases; it does not produce counterexamples at arbitrarily large n for any fixed t.

No fixed base edge lies in every member of F_n: E_0 is removed by every switch, and E_i (i!=0) by its i-switch. Any common edge would belong to E, so there are no common edges at all. Noncanonicity is therefore genuine, although cardinality violation alone already refutes the bound. There is no ordinary mathematical GAP in this construction.
