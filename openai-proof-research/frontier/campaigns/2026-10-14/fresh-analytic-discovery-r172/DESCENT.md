# r172: permutation descent, coinduction, and the relative obstruction

PREFREEZE feasibility work. No novel full theorem is frozen or nominated here. The calculation tests one exact strengthening of the paid comparison/compression construction. It does not alter Source302 or any old target.

## 1. The operation that would actually be needed

The source labels every cube slot globally. Elliott–Niu's ordinary diagonal AH application labels every eigenmap occurrence globally and transports its frame by a global bundle identification. Suppose instead that ordering the slots requires a finite principal permutation cover π:Ytilde→Y with group G. Let ρ:G→S_n act by permutation of the n whole t-dimensional slots and let f:Ytilde→C(t,n) satisfy

    f(gy)=ρ_g f(y).

Reading the source theorem on Ytilde gives a compression on Ytilde^u. It does NOT give the equivariance equation necessary for descent to the associated cube bundle over Y^u. That equation is

    G_u(g1 y1,...,gu yu)=(ρ_g1,...,ρ_gu)G_u(y1,...,yu)       (D1)

for all independent (g1,...,gu)∈G^u. The independent group matters: Ytilde^u→Y^u has deck group G^u. Equivariance only for the diagonal G is insufficient. A later family of eigenmaps may have smaller actual monodromy, but that must be proved for that family; it cannot be assumed in this general operation.

The desired output retains the SAME un actual slots, at least aun/8 of them on the boundary at every point, and every original boundary vector fixed. The available assumption, so far, is the source's one continuous strict-rank embedding on the entire sparse torus locus UPSTAIRS. It does not include an equivariant trivialization or a quotient-relative nullhomotopy.

## 2. What averaging and regular coinduction really achieve

For a fixed finite group acting on an input Z and on a convex cube target through slot permutations, let H:Z→C^N be a continuous non-equivariant compression whose original map f is equivariant. The average

    H_av(z)=|G|^(-1) Σ_g ρ_g H(g^(-1)z)

is equivariant. Each summand fixes an original boundary slot exactly, so their average fixes it too. But the set of vectors with at least s boundary slots is not convex. Opposite boundary vectors average to an interior point. Thus the boundary COUNT, the entire cover saving, can disappear. No claim about a specific source-produced map follows merely from this elementary observation; Sections3–4 give an actual obstruction to the universal assertion.

There is a correct stronger construction retaining the count in a larger output. Define

    H_ind(z)_g=ρ_g H(g^(-1)z),
    (k·v)_g=ρ_k v_(k^(-1)g).

Then

    H_ind(kz)_g=ρ_g H(g^(-1)kz)
               =ρ_k H_ind(z)_(k^(-1)g).

Each g-block is a compression of the same original input f(z), since ρ_g f(g^(-1)z)=f(z). Every original boundary vector is fixed in every duplicate, and at least the same fraction of the enlarged |G|N output is on its boundary. This is a complete regular coinduction construction, in the same spirit as the actual CoInd/Res operation in Mathew, Section4.1. It is paid and is not nominated.

For (D1), this construction introduces |G|^u copies of a length-un output. Those copies are not additional original eigenmap occurrences. Repeating a cover gives α∨α=α, whereas treating all the new outputs as independent factors costs their product dimensions. If the original palette has baseline C and saving s, the naive induced target has bound |G|^u(C-s), not C-s. A phase selector would be needed to choose a single compatible original-slot output. Such a selector is precisely extra descent data. Averaging the reconstructed vertex weights instead uses the union of their supports and need not retain any of the missing colors. Intersecting the supports can leave no vertex at all.

A join construction retains all phases continuously, but again adds dimensions and can replace the guaranteed boundary fraction by none on a chosen phase. The actual source uses joins only on quantitatively sparse bad macro intervals; a general ordering cover provides no such sparse mask. Ordinary finite-cover transfer does not supply that mask. None of these constructions proves that descent itself is impossible under stronger hypotheses.

## 3. A strict-rank test with a fixed-point obstruction

Fix the actual companion data p=1, t=3, n=2, a=1/32. Let C=[-1,1]^3 and set

    Y=C,             f(y)=(y,y)∈C².

Since floor(an)=0, the sparse set is {0}. The torus test locus is the source's embedded L≅T², and E_f=λ⊕λ, where λ⊂L×C² has first Chern number1. This rank-two bundle embeds in a trivial rank-three bundle, STRICTLY below twice its rank.

Here is a full topological justification of that embedding. Put F=λ⊕λ⊕λ^(-2). Its determinant is trivial. A complex bundle of rank at least2 over a finite two-dimensional CW complex has a unit section: construct it over vertices, extend over edges by connectedness of S^(2r-1), and over two-cells because π1(S^(2r-1))=0. Split off that section using a Hermitian metric. Apply the same argument to the rank-two complement. Thus F is the sum of two trivial lines and its determinant line, and is trivial. The inclusion of its first two summands followed by a trivialization embeds E_f in C³. This is an elementary bundle construction, not a new classification input. The line-tensor/Chern and bundle conventions agree with HatcherVB Proposition3.10 and the source's torus bundle.

Let C2 act trivially on Y and swap the two output slots. If a source compression on Y^u were equivariant for the simultaneous pair swap, its two output slots in each block would coincide. Write that common value as H_b(y1,...,yu). A positive boundary fraction implies at least one block is on its boundary, so

    H:C^u→∂(C^u).

If y_b∈∂C then H_b=y_b, by the original-slot preservation clause. On ∂(C^u), the straight-line homotopy from id to H retains at least one unchanged boundary block, hence stays in ∂(C^u). Thus the boundary restriction has degree1. It also extends to C^u with image in its boundary, so has degree0, a contradiction. This holds for every u≥1.

The source theorem remains fully applicable: it gives a NON-equivariant compression of these data. Only the proposed extra equivariance fails. This example alone would not address free ordering covers, so we next remove its fixed-point feature.

## 4. A free double cover: obstruction in every independent product power

Use the same p,t,n,a,L,λ. Now put

    Ytilde=S³×C,
    ε·(s,y)=(-s,y),
    Y=RP³×C,
    f(s,y)=(y,y).

This action is free. Let ε swap the two target slots. Then f is equivariant. The full torus locus is S³×L, and its bundle is the pullback of λ⊕λ. The rank-three embedding from Section3 pulls back to one continuous embedding on this entire locus. Thus the source's strict rank condition K=3<4 is met, with no patchwise or pointwise weakening.

Assume for the feasibility test that, for some u≥1, a map

    G:(S³×C)^u→C^(2u)

satisfies all three conditions:

1. it is equivariant for the INDEPENDENT deck group (C2)^u, whose b-th generator changes the sign of s_b and swaps only the two output slots in block b;
2. at every point it has at least (a/8)2u=u/128 boundary slots;
3. if y_b∈∂C, both corresponding output slots equal y_b.

The count in2 is integral and strictly positive, so G never equals the zero vector. We now derive a contradiction for every u; no limiting argument is used.

Set B=(RP³)^u and let γ_b be the pullback of its b-th tautological real line bundle. The real representation which swaps two copies of R³ splits, by average and difference, as three trivial lines plus three sign lines. The associated output vector bundle is therefore

    V⊕W over B,
    V=B×R^(3u),
    W=⊕_(b=1)^u γ_b^(⊕3).

The input quotient is B×C^u, which is the cube disk bundle D(V). The original diagonal map is the inclusion i(v)=(v,0), up to an irrelevant nonzero scalar in the invariant coordinate. Equivariance of G makes it a continuous fiber map g:D(V)→V⊕W. Its image avoids the zero section.

On the boundary S(V)=B×∂(C^u), at least one y_b is on ∂C. In that block both output slots of G equal y_b, exactly as in f. Therefore the straight-line homotopy

    H_t=(1-t)i+t g

avoids the zero section on S(V): one whole boundary block remains the same nonzero vector for every t. We consequently have a homotopy of maps of pairs

    (D(V),S(V))→(V⊕W,(V⊕W)\0).

All following cohomology uses F2; orientation issues are thereby retained, not ignored. Let U_(V⊕W) be the rank-6u Thom class. Since g avoids zero on ALL D(V),

    g*U_(V⊕W)=0.

By the pair homotopy, i*U_(V⊕W)=0 as well. But the product formula for Thom classes and the zero-section definition of the mod-two Euler class give

    i*U_(V⊕W)=U_V ∪ e_2(W).                                  (D2)

Write x_b=w1(γ_b). Hatcher's actual projective-space cup-product calculation and the field Künneth formula give

    H*(B;F2)=F2[x1,...,xu]/(x1^4,...,xu^4),
    e_2(W)=w_(3u)(W)=∏_(b=1)^u x_b^3 ≠0.

Multiplication by U_V is the Thom isomorphism

    H^(3u)(B;F2) → H^(6u)(D(V),S(V);F2).

Thus (D2) is nonzero, a contradiction. The source's compression exists upstairs, but it cannot meet this exact independent-product descent requirement for any u.

The primary operations used here were read before this derivation was written: HatcherVB's relative Thom product proof and Euler-class definition; HatcherAT's full proof of Theorem3.19 for projective-space cup products and Theorem4D.10 for mod-two Thom classes, with the relative Thom isomorphism. For this particular V, its Thom isomorphism is also the elementary relative cross-product isomorphism for B×(D^(3u),S^(3u-1)). Formula(D2) follows by pulling the product of the two Thom classes along v↦(v,0): the W factor becomes its zero-section Euler class.

## 5. What this does and does not settle

The calculation refutes the universal implication “source strict-rank embedding on a finite ordering cover implies compression descending through every independent product ordering, with the same slots and exact original boundary agreement.” It does so even for a free double cover, finite-dimensional compact inputs, p=1,n=2, and a single global rank-three embedding upstairs.

It does NOT assert that the embedding descends to a trivial rank-three target over the quotient torus locus. In fact this distinction is visible already in Chern classes. The descended rank-two source is λ⊗(1⊕γ_C) over L×RP³. Put x=c1(λ), z=c1(γ_C), so x²=z²=0 and xz is a nonzero2-torsion class in H⁴(L×RP³;Z). Here z is the integral Bockstein of the nonzero degree-one mod-two class of RP³: the Bockstein is an isomorphism onto H²(RP³;Z)=Z/2, so z is nonzero. The integral Künneth injection sends the generator of H²(L;Z) tensored with z to xz, so xz is nonzero. Then c1(E)=2x+z and c2(E)=xz. A line complement in C³ would have c1=-(2x+z), giving

    c2(E⊕F)=xz-(2x+z)²=-3xz=xz≠0.

Thus this example does not falsify a theorem with an additional compatible downstairs embedding. The primary source theorem requires an ordinary trivial target on an ordinary ordered locus; it does not identify either of these equivariant or twisted notions with that datum.

Nor does the calculation disprove an equality for locally diagonal AH algebras, generalized diagonal maps, or nonminimal dynamics. No inductive system with a failed radius equality has been constructed. Independent monodromy is the precise test used here; a special system can have less monodromy, global orderings, extra trivializations, or controlled negligible ordering regions. Those possibilities remain open in this round.

Pullback kills the displayed obstruction because the tautological lines become trivial on (S³)^u. This explains why upstairs nullhomotopies do not detect it. Transfer cannot recover it: pullback followed by transfer multiplies by 2^u, which annihilates mod-two cohomology. Mathew's actual coinduction/Tate discussion likewise distinguishes underlying vanishing from vanishing in a category with group action; ordinary MU-nullity is not a supplied equivariant nullhomotopy. No assertion of genuine equivariant MU nilpotence is made.

A valid further operation would have to retain quotient-relative or twisted Thom information and obtain a compatible compression on the ACTUAL occurrence bundle, with a strict rank margin and a saving in the original palette. Alternatively it would need a proven allocation of ordering changes to a quantitatively negligible exceptional region. Merely assuming a suitable equivariant compression restates the unpaid step. The free-cover example is an elementary obstruction diagnostic, not a substantial theorem nominee. Regular coinduction closes the enlarged-output construction but does not close the unchanged-slot descent problem.
