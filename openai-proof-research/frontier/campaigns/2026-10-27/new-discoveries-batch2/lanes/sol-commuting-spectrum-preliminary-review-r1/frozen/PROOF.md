# Full mathematical source outcome; novelty and acceptance on HOLD

Target: Juráš–Ursul, J. Algebra Comb. Discrete Appl. 9(1) (2022), 9–15, p12, equation (2): does Sc(R)=Sc(G_nil^(2))? Here R is the class of ALL finite rings (not assumed associative or unital in that paper), and G_nil^(2) is ALL finite nilpotent groups of class at most two. This is Buckley–MacHale Conjecture 15(b), not their different Conjecture 15(a) about all nilpotent groups. The inspected published body explicitly leaves (2) unanswered and proves it only for odd orders. Mendelsohn 2301.02041v2 p2 still lists the class-two equality as open. Those are dated source facts, not a claim of current worldwide openness.

We prove the missing inclusion with ASSOCIATIVE finite rings whose triple products vanish. No condition on prime, exponent, or oddness is used. This is a complete mathematical argument, not a formal certificate or novelty clearance.

## Lemma: triangular realization

Let A and B be finite abelian groups, written additively, and let b:A×A→B be biadditive and alternating, meaning b(a,a)=0. Then there exists a finite associative ring R and a surjection of additive groups π:R→A such that

    xy−yx = (0,b(πx,πy))

under a specified embedding of B into the annihilator of R. Consequently Pr(R)=|{(a,c):b(a,c)=0}|/|A|².

First proof (cyclic decomposition, economical size). Choose A=⊕_{i=1}^r Z/n_i with generators e_i. Put b_ij=b(e_i,e_j) for i<j. Biadditivity gives n_i b_ij=n_j b_ij=0. Thus

    f(a,c)=Σ_{i<j} a_i c_j b_ij

is independent of all choices of integer representatives and is biadditive. Alternation implies b(e_j,e_i)=−b_ij and zero diagonal, so f(a,c)−f(c,a)=b(a,c). On A⊕B define

    (a,u)(c,v)=(0,f(a,c)).

Distributivity follows from biadditivity; both ways of associating every triple product equal zero, so multiplication is associative. The additive group is abelian. The commutator is exactly (0,b(a,c)). Each a has |B| lifts, giving the probability formula. The zero or one-factor case has empty sum and is included.

Second proof (free finite cover; no finite-abelian classification). Choose an enumeration a_1,...,a_s of A, let N=|A|, and F=(Z/N)^s. Define p:F→A by p(x)=Σ_i x_i a_i. Lagrange's theorem gives Na_i=0, so this is well defined; p is surjective because every a_i is a basis image. Define

    f(x,y)=Σ_{i<j} x_i y_j b(a_i,a_j).

Again N annihilates each b(a_i,a_j), so f is well defined and biadditive, and f(x,y)−f(y,x)=b(p(x),p(y)). The same multiplication on F⊕B is associative with zero triple products. Every fiber of p has |ker p| elements: translating ker p by any preimage is a bijection onto that fiber. Therefore every ordered pair in A² has exactly |ker p|²|B|² lifts to R². Dividing by |R|² gives the identical probability formula. If A is trivial, N=1 and F is trivial; the construction still applies. This route trades size for an explicit presentation and avoids an invariant-factor decomposition. The two arguments share the triangular polarization, but their well-definedness/surjection bridges are different; they are not two unrelated novelty claims.

## Application to groups

Let G be ANY finite group with [G,G]⊆Z(G). Put A=G/Z(G), B=Z(G), writing the abelian group B additively with zero the group identity. For a=gZ(G),c=hZ(G), set b(a,c)=[g,h]=g⁻¹h⁻¹gh. Multiplying either lift by a central element leaves this unchanged. Centrality of all commutators gives [gg',h]=[g,h][g',h] and [g,hh']=[g,h][g,h']; hence b is biadditive. Also [g,g]=1, so it is alternating. Finally b(a,c)=0 if and only if g and h commute. Each coset has |Z(G)| elements, so

    Pr(G)=|{(a,c)∈A²:b(a,c)=0}|/|A|²=Pr(R).

The first construction has |R|=|G|; the second need not. The source question requires equality of values, not a group/ring isomorphism or prescribed order. Thus Sc(G_nil^(2))⊆Sc(R).

For completeness, the reverse inclusion does not require assuming a published theorem. For ANY finite possibly nonassociative ring S, define T=S⊕S additively, with (a,u)(c,v)=(0,ac). It is distributive and all triple products vanish. Consequently x∘y=x+y+xy is an associative group law with identity 0 and inverse −x+x². Direct expansion gives the group commutator x⁻¹∘y⁻¹∘x∘y=xy−yx, which lies in 0⊕S and is central. Moreover x∘y=y∘x exactly when xy=yx. The commutator of (a,u),(c,v) vanishes exactly when ac=ca in S, so Pr(T,∘)=Pr(S). This is precisely the classical construction already credited in Juráš–Ursul Lemma1.1, Lemma3.1 and Theorem2.1. Hence the two spectra are equal in the full literal source scope. No conclusion about all higher-class nilpotent groups is asserted.

## Failed route retained

Using the antisymmetric ring product b itself gives ring commutator 2b. It works for odd-order B but fails at characteristic two. For A=C2²,B=C2 and b((x,y),(u,v))=xv−yu, b is nonzero yet the antisymmetric product is commutative, so its commuting probability is 1 rather than 5/8. This is an exact algebraic obstruction to division-by-two, not an approximate numerical failure. The successful triangular product f uses b as its skew part without requiring 2 to be invertible.

## Formal scope and eligibility limits

A literal future endpoint would quantify over finite G with central commutators and produce a finite nonunital associative ring R with equality of the exact rational commuting-pair counts divided by squared cardinalities; the reverse inclusion then supplies the source equality of sets of rationals. The free-cover proof needs quotient G/Z(G), commutator biadditivity, finite ZMod powers, a triangular finite sum, fiber-cardinality counting, and the radical adjoint group. These are explicit proved mathematical bridges here; no Lean implementation or assertion that existing library lemmas discharge them has been made. In particular, no certificate/allowed-axiom claim is offered.

The central objection is prior-art/substantiveness: triangular polarization of alternating bicharacters and the commutator-bimap viewpoint are classical. The source's odd-order argument uses the product b and therefore does not by itself contain this even-order construction, but an older ring/group isoclinism theorem could subsume it immediately. Buckley 2015 *Distributive algebras, isoclinism, and invariant probabilities* and Mal'cev's correspondence paper have NOT been body-cleared here. A 403 on the author directory was preserved and not retried. No current public proof-registry head was cleared through the denied GitHub routes. Thus this file certifies a full mathematical derivation only. Recommend HOLD for independent source/subsumption review; credit requested: ZERO.
