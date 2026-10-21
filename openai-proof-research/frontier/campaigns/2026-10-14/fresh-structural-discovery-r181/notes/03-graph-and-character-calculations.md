# Exact graph and character calculations

All calculations are prefreeze. They develop the same Source321 data, not a second family or a proposed count. The code and noncommutative matrix data are private local derivations, not formal support for a nominee.

## 1. A graph of finite groups, with all injections specified

The source group G is the fundamental group of a graph with two vertices and two edges. Its vertex groups are

    V1=<a1,x1 | a1^15=x1^2=1, x1 a1 x1^-1=a1^4>, |V1|=30,
    V2=<a2,x2 | a2^26=x2^3=1, x2 a2 x2^-1=a2^3>, |V2|=78.

These are the semidirect products C15⋊_4 C2 and C26⋊_3 C3: 4²=1 mod15 and 3³=1 mod26, with the displayed actions of exact orders two and three. The first edge is C2, embedded as x1 in V1 and a2^13 in V2. Choose it as maximal tree edge. The second is C3, embedded as a1^5 in V1 and x2 in V2; its stable-letter relation is s x2 s^-1=a1^5. All edge maps are injective.

Here is the presentation comparison, rather than an inference from the title. In the original presentation of G, a2^26=x1²=1 and a1^15=s x2³ s^-1=1. Thus all graph-of-groups relators hold. Conversely the graph-of-groups presentation includes all four original relators and both x1²,x2³. The presentations therefore define the same marked group. Reduced amalgam/HNN normal forms show that the finite vertices embed; the associated coset graph is a tree. One way to see the latter is to reduce a hypothetical non-backtracking circuit to a reduced alternating vertex/stable-letter word: it cannot represent the identity by the normal form. Thus the specified graph is a genuine graph of groups, not a noninjective diagram.

The rational virtual Euler characteristic is

    1/30+1/78-1/2-1/3 = -307/390.                              (3.1)

This does not equal χ(X)=0: X is not asserted aspherical. In particular cd_Z(G)=2 is not inferred from its D(2) complex.

## 2. The character kernel is an explicit free product

Let θ:G→Q=C3×C2 send a1↦(1,0), a2↦(0,1), x1↦(0,1), x2↦(2,0), s↦0. It is the finite part of the abelianization G_ab=Z⊕C3⊕C2. The source faithful sixth-root character has kernel H=kerθ.

Both vertex images in Q are all of Q. The two vertex stabilizers in the H-quotient of the tree are respectively <a1³>=C5 and <a2²>=C13. The C2 edge has three lifts, indexed by Q/θ(C2), and the C3 edge has two lifts, indexed by Q/θ(C3). Their stabilizers in H are all trivial. Consequently the quotient graph has two vertices and five edges. Collapsing, for example, the C2 edge with trivial coset index gives

    H ≅ C5 * C13 * F4.                                        (3.2)

This also proves χ(H)=1/5+1/13-5=-307/65=6χ(G). The four free generators are the four nontree oriented edges of this quotient graph. Changing paths to the vertices changes this marking by the usual conjugations; the Schreier specification below fixes one concrete cellular marking independently.

## 3. The full scalar Fox family, not just the source character

Every rank-one complex character of G is determined by α³=1, β²=1 and z≠0, with values

    (x1,a1,x2,a2,s)=(β,α,α²,β,z).

Define S_m(t)=Σ_{j=0}^{m-1}t^j. In the source row convention the boundary is

    D(α,β,z) =
    [1-α, β-S4(α), 0, 0, 0]
    [0, 0, 1-β, α²-S3(β), 0]
    [1, 0, 0, -S13(β), 0]
    [0, -S5(α), z, 0, 1-α²].                                 (3.3)

Multiplication by (β-1,α-1,α²-1,β-1,z-1)^t gives zero. The source relative contraction identifies H2(X;L) with ker D^t. For EVERY z∈C*, not just generic z, the rank and second Betti number are:

- α=1, β=1: rank 4, b2=0. The first-four-column determinant is -6z.
- α=1, β=-1: rank 3, b2=1. The first three rows in columns x1,a1,x2 have determinant -10; the fourth row is a combination of rows one and two.
- α≠1, β=1: rank 3, b2=1. The third row is in the span of the first two, and rows 1,2,4 have a nonzero constant minor in columns x1,a1,a2.
- α≠1, β=-1: rank 4, b2=0. The columns x1,a1,x2,s have determinant -4(1-α²).

The exact polynomial calculation is in private/character-calculation.json. It uses integer pairs in Z[ω] and polynomials in z. All four-minors vanish identically in the rank-three cases; the recorded nonzero monomial minors rule out exceptional nonzero z. The first implementation attempted SymPy, which was unavailable; no package was installed. The replacement is elementary exact arithmetic. These calculations are diagnostics supporting the displayed derivation, not mathematical gates.

By finite-character decomposition of C[Q], the cover X_H has b2=3 and b1=4. The three b2 contributions are the pure nontrivial C2 character and the two pure nontrivial C3 characters. The two faithful mixed characters contribute zero; the trivial character contributes b1=1 and b2=0. Thus passing to the source character kernel does NOT preserve the source's vanishing twisted second homology by a blanket finite-cover argument. The source lemma concerns infinite cyclic covers of a TWO-dimensional complex; X is three-dimensional and this is a different operation.

## 4. All finite-dimensional complex coefficient tests on this cover

Let V be any finite-dimensional right complex H-module of dimension d. Let da and db be the dimensions of its C5 and C13 coinvariants, and d0 its H-coinvariant dimension. Over C the finite vertex groups have zero positive homology (averaging gives a contracting homotopy on their positive-degree resolutions). The tree resolution therefore computes H1(H;V) from

    0 → H1(H;V) → V^5 → V_C5⊕V_C13 → V_H → 0.

It follows that

    dim H1(H;V)=5d-da-db+d0.

The lifted split third boundary gives H_i(X_H;V)=0 for i>2. Its Euler characteristic is zero and its degree-one homology is group homology. Therefore

    dim H2(X_H;V)=5d-da-db ≥ 3d.                               (3.4)

No unitarity assumption is needed for (3.4); restriction to each finite vertex group is semisimple. In particular NO nonzero finite-dimensional complex local system on X_H has vanishing H2. Merely enlarging the source character to a finite-dimensional representation will not give a vanishing-based tower obstruction on this particular cover.

Consider the fully specified finite two-complex

    Y = M5 ∨ M13 ∨ (∨^4 S1) ∨ (∨^3 S2),
    Mn = S1 ∪_{degree n} D2.

It has π1=H and χ=0. On the two Moore cells the norm operators have ranks da,db, while the three extra sphere boundaries vanish. Thus dim H2(Y;V)=5d-da-db, exactly (3.4); H0 and H1 also match by π1. This establishes agreement of ALL these complex homology dimensions, not an integral chain equivalence, a marking-preserving homotopy equivalence, or a finite 2-model for X_H. Note 04 specifies the remaining integral comparison without discarding these constraints.
