# Complete ordinary refutation, with negative eligibility recommendation

Let G=P_7 square P_7 be the Cartesian product of two paths on seven vertices. It has 49 vertices and 84 edges. Write a(G) for its number of acyclic orientations. Then

    a(G) = 0 (mod 4),

contradicting the universal congruence in Mühlherr–Poullot arXiv:2609.02249v2, Conjecture 1(1). This refutes the conjunction Conjecture 1 as printed. It does not prove or disprove its separate non-Hamiltonicity conclusion, or resolve the other graph families. This is a complete ordinary mathematical refutation, NOT a proposed creditable discovery: see the complete classical bridge below.

## Classical reduction

For every finite graph H, its chromatic polynomial C_H(X) has integer coefficients (for example, expand inclusion–exclusion over edges). Thus C_H(-1)=C_H(3) modulo 4. Stanley's Corollary 1.3 gives a(H)=(-1)^|V(H)| C_H(-1). The actual author-hosted 2006 reprint of the 1973 paper, including Theorem 1.2 and its proof, was read. Consequently it suffices to show C_G(3) divisible by 4. An independently reproduced exact row recurrence gives C_G(3)=41869995708. The following much smaller certificate avoids reliance on that large computation.

## Reflection reduction to a 4 by 4 grid

Let Q(w,h) be the set of proper colorings of P_w square P_h by {0,1,2}, modulo global color permutations, where w,h>=2. Each color orbit has size six: an edge uses two distinct colors, and a permutation fixing a coloring fixes those two colors and hence the third. Therefore |Q(w,h)|=C_(P_w square P_h)(3)/6.

For odd w=2k-1, reflect in the middle column. This is an involution on Q(w,h), so |Q(w,h)| has the same parity as its number of fixed orbits. If a color orbit is fixed, a representative c satisfies c(reflect(v))=pi(c(v)) for a color permutation pi. The middle column is fixed pointwise and contains an edge, so pi fixes two distinct colors. Hence pi is the identity. Fixed color orbits are exactly the genuinely reflection-invariant colorings modulo colors. Restriction to the first k columns bijects these with Q(k,h): extend by reflection, and every edge crossing the middle column is paired with an existing edge. Restriction and extension commute with color permutations. We have proved

    |Q(2k-1,h)| = |Q(k,h)| (mod 2), h>=2.

Apply first with (w,h)=(7,7), then after transposition with (7,4). It follows that |Q(7,7)| and |Q(4,4)| have equal parity.

## Explicit finite certificate for the smaller count

Every proper four-vertex row is uniquely a color permutation of one of

    r1=0101, r2=0102, r3=0120, r4=0121.

Each orbit has six elements. Let M_ij count proper rows of type j that are componentwise different from the fixed row r_i. Explicitly, with S3 the six permutations of three colors,

    M_ij = sum_(pi in S3) product_(l=1..4) [r_i(l) != pi(r_j(l))].

The complete integer table is

       3 2 1 2
    M= 2 2 1 2
       1 1 2 1
       2 2 1 2.

This is a finite certificate with each entry the displayed sum of six zero-one products; it can be checked directly, rather than an unproved numerical approximation. For a fixed top row of type i let v_h(i) count valid completions to h rows. Row restriction/extension proves v_1=(1,1,1,1) and v_(h+1)=M v_h, because global color permutations biject the completions for any two rows of the same type. Multiplication gives

    v_2=(8,7,5,7), v_3=(57,49,32,49),
    v_4=(399,342,219,342).

Thus C_(P4 square P4)(3)=6*(399+342+219+342)=7812, and |Q(4,4)|=1302 is even. The reflection lemma gives |Q(7,7)| even, so C_G(3)=6|Q(7,7)| is divisible by 12, hence by 4. Stanley's identity now proves a(G)=0 modulo 4. Both source parameters seven are odd and at least three. QED.

The same reflection proof produces a(G_j)=0 modulo 4 for square grids of side 3*2^j+1, j>=1, by repeated folding to side four. This is not a separate discovery or new generic tool.

## Complete subsumption bridge / strongest objection

The current OEIS A182406 and its linked grid-coloring table already publish C_G(3)=41869995708, with the exact graph and color interpretation. The entry is attributed to Alois P. Heinz, April 27, 2012; the currently visible bytes are not a certified snapshot of that date. Combining this SAME-OBJECT known count, Stanley's literal Corollary 1.3, and integer-polynomial evaluation modulo four yields the entire refutation immediately. No missing endpoint, extra regularity hypothesis, or unproved bridge remains in this reduction. Therefore the lane recommends EXCLUDE as a routine classical/counting corollary under the user's rule, irrespective of whether anyone explicitly printed this conjecture's refutation. The folding proof above provides an independently verified small certificate but does not remove this objection. No Lean investment or claimed new method.
