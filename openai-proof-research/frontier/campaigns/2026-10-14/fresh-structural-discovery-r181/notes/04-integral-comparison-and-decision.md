# Carrying the integral comparison to an explicit remaining operation

This notebook remains PREFREEZE. The calculations specify a feasibility test, not a frozen theorem or a conditional nominee. The proposed operation being tested is relative geometric cancellation with a prescribed integral chain type, after the source's algebraic splitting has already been performed. A mere cover, wedge, stable classification, or equality of complex Betti numbers would not meet the discovery brief.

## 1. A finite noncommutative matrix, with no unspecified Fox inputs

Put S=ZH for H=kerθ as in note 03. Let F5 be free on x1,a1,x2,a2,s. For q=(i,j) in {0,1,2}×{0,1}, take t_q=a1^i a2^j. Write q+g for its θ-image after traversing g. Define

    h(q,g)=t_q g t_(q+g)^-1.

The six words t_q form a prefix-closed Schreier transversal. Exactly five of the thirty h(q,g) freely reduce to 1: the two a1 edges along 1,a1,a1² and the three a2 edges from a1^i to a1^i a2. Delete precisely those tree edges. The other twenty-five h(q,g), in lexicographic (i,j,g) order with g=(x1,a1,x2,a2,s), form the fixed Schreier basis.

For a relator w and start vertex q, rewrite a positive letter g as h(q,g), advancing q; rewrite a negative letter g^-1 as h(q-g,g)^-1, retreating q. This specifies the words w_q exactly. Apply it to r1,r2,r3,r4,u and every q. The thirty resulting relators present H, since they are the Reidemeister–Schreier presentation of the balanced presentation J. The first four types alone present the preimage of kerθ in P, not H: their coefficients below are evaluated in the FULL thirty-relator quotient. Omitting the six u_q from the coefficient-group presentation would be a serious error.

For any rewritten word w=h_(j1)^ε1...h_(jm)^εm, its Fox derivative has, for each letter occurrence, coefficient prefix(w,k-1) when εk=+1 and -prefix(w,k) when εk=-1 in the row for h_(jk). This produces all entries as finite integral sums of explicitly recorded free words. The file private/schreier-six.json contains the twenty-five generator words, all thirty relators, and every sparse Fox entry. Its twenty-four columns from the r_i,q give

    A6: S24 --D6--> S25 --d1--> S,      d1(h)=h-1.             (4.1)

These are the chains of the H-cover of B after tree collapse, identified with the algebraic contraction of X_H by the lifted plus splitting. It is exact in degree one, augments to Z, and has H2=π2(X_H). No 3-boundary matrix needs to be guessed to define (4.1).

The generating code checks the fundamental Fox identity for ALL thirty relators in the FREE group ring, before imposing relations: Σ ∂w/∂h·(h-1)=w-1. After quotienting by the thirty words it gives d1D6=0. This is a finite algebraic diagnostic. It does not test a homotopy classification or certify cancellation.

## 2. The exact proposed endpoint and the actual remaining map

Mark the H of Y=M5∨M13∨4S1∨3S2 using the quotient graph in note 03. Let a generate C5, b generate C13, and c1,...,c4 be the four oriented nontree edges. Its chain complex is

    C(Y): S5 --D_Y--> S6 --d_Y--> S,
    d_Y=(a-1,b-1,c1-1,...,c4-1),
    D_Y(e1)=N5(a)e_a, D_Y(e2)=N13(b)e_b,
    D_Y(e3)=D_Y(e4)=D_Y(e5)=0,                                (4.2)

where N_m(v)=1+v+...+v^(m-1). Its π2 is

    S⊗_(ZC5) I_C5  ⊕  S⊗_(ZC13) I_C13  ⊕  S3.              (4.3)

Adding nineteen elementary (2,1) pairs to (4.2) gives ranks (24,25,1), exactly (4.1). Thus a concrete sufficient algebraic operation is an augmentation-preserving S-chain equivalence between D6 and D_Y⊕I19, with an actual comparison of the lower generator maps. A based chain isomorphism would be stronger and particularly usable, but is not necessary. No such chain equivalence or isomorphism is constructed here.

Nor is it enough to identify just the module in (4.3): the full extension/chain type and its realization by the marking must be retained. If an augmentation-preserving chain comparison is supplied with the lower map realized on one-skeleta, cellular approximation and Hurewicz give the familiar geometric realization step: discrepancies on two-cells are universal-cover two-cycles and can be corrected by spherical maps. A resulting π1-isomorphism and universal-cover chain equivalence give a homotopy equivalence by the homological Whitehead theorem. The missing input here is the UNSTABILIZED integral comparison, not that final Whitehead criterion.

The canonical group presentation of H is not automatically related to the covering presentation J_H by homotopy-preserving two-dimensional moves. J_H has χ=6; the minimal displayed Moore/free-circle presentation has χ=-3. Deleting nine redundant group relators can change the two-type. Even a proof that both presentations define H leaves exactly this spherical/extension information to control. No Tietze move is silently treated as a simple homotopy move.

## 3. Pay the strongest actual stabilization explicitly

A late primary read, made after notes 01–03 and before this calculation, is Mannan, Homotopy types of truncated projective resolutions, arXiv:2308.11871v2 (21 December 2023), a repository version of the 2007 HHA paper. The entire six-page text was read, including the inductively constructed inverse block matrices; the publisher URL returned 403. This is not a newly discovered 2023 improvement. Its proof, not just Schanuel's module equality, is what is used here.

Apply that theorem to P=A6 and Q=C(Y). The recursion is T0=P0, S0=Q0, Ti=S_(i-1)⊕Pi, Si=T_(i-1)⊕Qi. The ranks are

    (rank T0,rank S0)=(1,1),
    (rank T1,rank S1)=(26,7),
    (rank T2,rank S2)=(31,31).

Consequently there IS an augmentation-preserving chain homotopy equivalence

    A6 ⊕ S31[2]  ≃  C(Y) ⊕ S31[2].                          (4.4)

This is more than an unexplained stable-class assertion. In the primary proof the added adjacent-degree identity complexes lead to C2 and D2. Projectivity gives lift maps fi,gi compatible with the prior degrees. At every degree the matrices

    hi=[fi, 1-fi gi; 1,-gi],   ki=[gi,1-gi fi;1,-fi]

are inverse by direct multiplication, without assuming fi or gi invertible. They give the chain isomorphism of the expanded complexes. The precise extra degree-two summands in this application both have rank 31. None of these matrices supplies a projection-compatible deletion of those 31 summands, so (4.4) cannot be relabelled as (4.1)≃(4.2).

There is also a direct geometric stable comparison already paid by the source and Hambleton: restriction of the one-cell plus model gives six 3-cells, and X1_H∨6S² is simple-homotopy equivalent to J_H. This uses actual spherical attachments and elementary shears. It does not identify J_H with Y∨6S². Both useful stable operations have been carried through; neither is discarded just because an earlier naive move would fail.

Hambleton's improved cancellation theorem does not complete (4.4): H is infinite, not finite. Its noetherian alternative also has no missing routine hypothesis to check here. H contains the free subgroup <c1,c2>. The elements v_i=c1^i c2 c1^-i, i≥0, are part of the standard free basis of the kernel of <c1,c2>→Z. The subgroups K_n=<v_0,...,v_n> strictly increase. In S, the left ideals generated by k-1, k∈K_n, strictly increase too: their quotient permutation modules have basis the right cosets H/K_n, and v_(n+1)-1 survives in the n-th quotient. Hence S is not left noetherian. This rules out this particular application of Proposition 2.7; it is not a general noncancellation theorem.

## 4. Carry the strongest vanishing-based tower extension too

The Laurent-minor proof works for a finite-rank complex local system as well: the cyclic-cover chain groups are finite free over C[z,z^-1], and injectivity of the specialized second boundary gives a nonzero full-column minor. For a UNITARY system V, there is a direct extension of the source tower argument. On each finite image A_i, split off the invariant subspace of V; its orthogonal complement remains a sub-local-system with H2=0, has H0=0, and still has nontrivial pullback monodromy if the original pullback did. It has positive rank d_i. Euler characteristic gives d_i χ(A_i)=-dim H1(A_i;V_i)≤0. Thus b1(A_i;Q)>0. The map from F with b1(F;Q)=0 lifts to a cyclic cover, the minor argument preserves H2=0, and its image again has strictly more simplices on the fixed triangulation of F. Removing any newly invariant summand does not remove all nontrivial pullback monodromy. The same bounded simplex-count contradiction follows.

This is a routine extension of the source proof, recorded to avoid mistaking rank one for an unexplored obstacle. It requires the invariant complement; it is not asserted for arbitrary nonsemisimple representations by the same argument. More importantly, (3.4) shows that every nonzero finite-dimensional complex system on X_H has b2≥3d. Thus even this stronger unitary tower cannot be activated on this cover by selecting a clever representation. This proves a precise limitation of this test, not absence of other obstructions or of a two-model.

The rational projectors N5(a)/5 and N13(b)/13 explain why the complex dimensions agree so easily. Their denominators are unavailable over S. Their use cannot replace the integral maps in §2. No prime-by-prime lifting, cancellation at 5 and 13, or coherent geometric localization has been produced.

## 5. Compatibility with r180 and the final prefreeze boundary

Source321's finite two-dimensional tower and plus construction do not operate on the four-dimensional chamber core equivalences of r180. Those spaces have different π1 and middle-module data; r180's s-cobordism or reflection transfer supplies no chain equivalence (4.1)→(4.2), and the matrix calculation supplies no recognition of r180's chambers under arbitrary homeomorphisms. The full I07/I97 targets and all r180 paid reductions remain intact. A failure of this integral comparison would not refute any old marked realization theorem; its success would not solve the old relative involution problem.

What is retained is a concrete integrated reduction: one-cell plus construction; actual one-sphere stabilization map; exact normal/module generator gap; graph-of-groups and six-cover calculation; all-character boundary ranks; all finite-dimensional coefficient comparison; the complete finite Schreier/Fox input; and the explicit 31-summand stable chain equivalence. The unpaid operation in the tested endpoint is the augmentation/marking-compatible UNSTABILIZED integral chain comparison in §2 and its resulting geometric realization. It is not closed by Betti numbers, free chain modules, projective stability, the finite-group theorem, or the unitary tower. No claim that this comparison is impossible or necessary for every future discovery is made.

No distinct fully closed nonroutine theorem emerged. No exact theorem is frozen and no author-proof nominee is submitted. Decision: PREFREEZE / no nominee. Immediate source consequences, covers and stabilization counts are not offered as a weaker substitute for the requested substantial acceptance. There is no exhaustion claim, worldwide-priority claim, mathematical self-grade, acceptance, count, or downstream formal/manuscript/release work.
