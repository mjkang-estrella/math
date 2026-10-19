# Automorphism data in the numerical weight theorem

This is prefreeze feasibility work. No target was frozen, no full arbitrary-automorphism theorem was proved, and no result is nominated. The restricted deductions below are comparisons with compatible existing operations, not replacements for the full question. Pinned source202 and its operative statements are stipulated true.

The question investigated was: for every prime p, finite group G, p-block b over an algebraically closed characteristic-p field, and finite A≤Aut(G) stabilizing b, is there an A-equivariant bijection between IBr(b) and the G-conjugacy classes W(b) of b-weights? No character-triple isomorphism, canonical choice, effective bound, or coefficient-Galois action was silently included. No restriction on A was intended for the full question. This is a feasibility question, not a frozen candidate.

The targeted history/alias searches and actual r25/r87 and I104/I108/I110 comparisons preceded this extended note. The two semidirect-product calculations below preceded any freeze (none occurred). Malle's actual Proposition6.2, Martínez–Rizo–Rossi's actual extension/DGN interfaces, and Bartel–Dokchitser's actual Brauer relation were read before writing the note. Thus the elementary relation is explicitly a primary antecedent.

## What the source already pays

The source main theorem gives l(H,c)=|W_H(c)| for every finite H and block c, hence for sums of blocks. This includes H=G⋊A; it is important to try these groups rather than treating source202 as one isolated equality for G.

The actual `group.tex`, `lem:normalizer-projection`, identifies block assignment using coefficient projection and the Brauer map. The central detecting element has prescribed 0/1 residue scalars and p-singular support. `lem:trace-limit` retains the ordinary-character counts through p-power limits, and `lem:tuple-trace` supplies the exact single denominator |H|. `lem:pcore-cancellation` toggles chains by O_p(J), while `prop:group-reduction` retains all generated subgroups and all puncture-class multisets. The source geometric theorem is uniform over these multisets. None of these stronger operations was discarded in favor of a headline-only comparison.

The entire `cor:functorial-awc` and proof are also already paid. The source imports the full cancellation of all nontrivial simple-functor components; its remaining coefficient is the numerical count. Its functor category is over an algebraically closed field of characteristic zero. Equality there is not an asserted isomorphism respecting an additional automorphism action on the block labels.

## Prime-order automorphisms: the compatible reduction closes

Let A=C_p stabilize b, set Γ=G⋊A, and write

    x=|IBr(b)|,     f=|IBr(b)^A|,
    y=|W(b)|,      g=|W(b)^A|.

Regard b as a central idempotent of kΓ; it is a sum of Γ-blocks. Let L be the number of Γ-simple modules selected by it and V the number of selected Γ-weights.

Modular Clifford theory gives

    L = f + (x-f)/p.                                           (1)

An invariant simple G-module has a unique extension over a p-group quotient. In the index-p situation this can also be seen directly: choose an intertwiner T for the automorphism, scale it so that T^p=1 using algebraic closedness and Schur's lemma, and observe that the only pth root of unity in k is1. A noninvariant orbit has p distinct constituents and induces one simple Γ-module. The selection by b is preserved.

On weights, Malle's Proposition6.2 gives a bijection from invariant G-weight classes to Γ-weight classes (Q,ψ) with Q not contained in G. Its proof is the Dade–Glauberman–Nagao correspondence, including its converse and block compatibility. Thus these classes contribute exactly g.

The Γ-weights with Q≤G correspond to the noninvariant G-weight orbits. Here is the other half of the count, so it is not hidden in the word “Clifford.” Fix Q up to Γ-conjugacy and put H=N_Γ(Q), N=N_G(Q). If H=N, its G-conjugacy class of subgroups has p conjugates and one Γ-class accounts for that orbit. Otherwise H/N has order p. An ordinary defect-zero character θ of N/Q whose H-orbit has p elements induces an irreducible character of H/Q of degree pθ(1), hence of defect zero. Conversely, a defect-zero character of H/Q cannot lie over an H-invariant θ: extensions over a cyclic quotient have degree θ(1), whose p-part is at most |N/Q|_p, short of |H/Q|_p. Clifford theory therefore forces an orbit of size p and a defect-zero constituent. These two cases account for all weights with Q≤G and produce one per noninvariant G-weight orbit.

Selection by b agrees on both sides. For Q≤G, the coefficient restriction of b to H is its restriction to N, since b is supported in G; the local character tests agree under restriction/induction. For Q outside G this is the block compatibility in Proposition6.2. Consequently

    V = g + (y-g)/p.                                           (2)

The stipulated numerical theorem, first for (G,b) and then for the sum of Γ-blocks selected by b, gives x=y and L=V. Subtracting (1) and (2) yields (p−1)(f−g)=0. Thus f=g. An A-set for A=C_p is determined by its number of fixed points and its total size, so an A-equivariant bijection exists in this restricted case.

This calculation is entirely supplied by universal numerical AWC, modular Clifford theory, the complete primary DGN weight correspondence, and two scalar equations. No new compatibility operation has been identified in it. It is not nominated. Malle's printed Corollary6.3 contains factors2 while its statement uses a prime p; this note uses the independently derived orbit factors p and does not import that displayed arithmetic unchanged.

## Every cyclic prime-to-p automorphism group: another paid comparison

Let A=C_m, p∤m, and retain a stable b. For either the Brauer-label set X or the weight-label set Y, let d_z be the order of the stabilizer of a label z. In Γ=G⋊A, the contribution of its A-orbit is d_z.

For simple modules this is ordinary modular Clifford theory with cyclic prime-to-p inertia quotient. A stable irreducible extends over the cyclic quotient: an intertwiner can be scaled to satisfy the cyclic relation; tensoring by its d_z linear characters produces all d_z extensions. For local ordinary defect-zero characters the same construction applies. Every p-subgroup of Γ lies in G; normalizer quotients differ by a prime-to-p cyclic group. Degree p-parts therefore remain exactly the defect-zero p-parts through extension and induction. The coefficient-projection block test again retains the chosen b. No DGN step with an enlarged p-subgroup is required in this case.

It follows for the selected simple/weight count that

    m L_X = sum_(z in X) d_z^2
          = sum_(e|m) J_2(e) |X^(C_e)|,                       (3)

and the identical expression holds for Y. Here J_2(e)=e² product_(q|e)(1−q^(-2)); the equality follows from d²=sum_(e|d)J_2(e). Applying numerical AWC to G⋊C_e for every e|m, and inducting on e, determines each fixed count: the coefficient of the new count is J_2(e)>0. A cyclic set is determined by these fixed counts, by divisor Möbius inversion. Thus this whole tame-cyclic comparison is also supplied by a compatible classical reduction. The Jordan-totient coefficient is derived here as bookkeeping, not claimed new.

No mixed-order cyclic or arbitrary p-group theorem is claimed merely by extrapolating (1) or (3). Iterated DGN/Clifford transport is a possible stronger compiler; any such use must retain the quotient action through each step. The archive does not assert that the prime-order comparison is the strongest theorem in the literature.

## Why orbit tests alone leave a noncyclic operation

Even granting equality of every subgroup orbit count, a general finite A-set need not be recovered. This is the classical Burnside-to-representation-ring kernel, not a new counterexample. For A=C_ℓ×C_ℓ, with ℓ any prime, consider

    X = A/{1} disjoint-union ℓ copies of A/A,
    Y = disjoint-union_(L≤A, |L|=ℓ) A/L.

Both sets have ℓ²+ℓ elements. A nonidentity a lies in exactly one line L, so |X^a|=ℓ=|Y^a|. At the identity the counts also agree. Hence their permutation characters agree. For EVERY H≤A,

    |H\X| = (1/|H|) sum_(h in H) |X^h|
           = (1/|H|) sum_(h in H) |Y^h| = |H\Y|.

But |X^A|=ℓ and |Y^A|=0. Bartel–Dokchitser, published Example2.4, gives exactly the virtual relation [A/{1}]−sum_L[A/L]+ℓ[A/A].

This also defeats two stronger-looking numerical repairs. For every finite A-set T, the permutation character of X×T equals that of Y×T, so all subgroup orbit counts of these products agree. The same holds for X^n and Y^n for every finite n, since fixed-point counts multiply. Thus adding independent auxiliary label sets or taking tensor/cartesian moments does not recover the missing simultaneous stabilizer mark. The relation is an abstract diagnostic only: neither X nor Y has been realized as the actual two label sets of any group block, and no counterexample to equivariant AWC is asserted.

An actual A-equivariant bijection would follow from equality |IBr(b)^H|=|W(b)^H| for ALL H≤A, via the injective table of marks. Counts fixed by each individual element provide only the cyclic rows. The missing operation is simultaneous noncyclic fixed-label comparison, or an actual compatible bijection that bypasses those counts.

## Stronger primary and source alternatives checked

Martínez–Rizo–Rossi's published TheoremC reduces their ConjectureB to its stronger inductive conditions on simple covers. Their ConjectureB includes an automorphism-equivariant bijection AND block isomorphisms of modular character triples. Proposition7.5 and Lemma7.4 use these data to compare extensions and then use DGN to obtain Navarro's invariant-count formula. The proof explicitly begins with the supplied equivariant bijection. Its premise is not numerical AWC for all groups, so the pinned source does not automatically activate it. The inspected proofs were Lemma7.2, Lemma7.4 and Proposition7.5, together with the exact main statements; the long simple-group reduction and Theorem5.6 proof were not freshly reconstructed.

The source functorial consequence and I110's complete nontrivial local-point toggle are stronger than scalar slogans. The toggle commutes with the data it transports and cancels every nontrivial local-point stratum. At P=1 its insertion rule has no eligible index; the surviving projective/simple labels are exactly the unresolved component. Adding an auxiliary central p-group creates the paired copy of the same residual labels, as actual I110 explains, rather than an independent vanishing. Nothing in that inspection supplies an A-equivariant zero object in the required label category.

I also considered using a semidirect-product marked cover to impose an automorphism on a handle. The source tuple theorem counts unrestricted handles with prescribed puncture-class multisets. It does not state divisibility for an arbitrary subset selected by quotient-handle monodromy. A finite prime-to-p quotient marking might be rigidified after an extension of bounded p-part, but the arithmetic descent and exact reduced-section comparison for that selected family were not constructed. For a whole noncyclic subgroup, even a single automorphism trace would still leave simultaneous marks. No tagged-cover theorem is claimed. The coefficient-Galois power-handle obstruction in I108 is a different contract; it is not an impossibility proof for genuine automorphism semidirect products.

The full arbitrary-A question is therefore unresolved in this round. There is no frozen target to replace, no restricted nominee, and no contribution or correctness gate. The mathematical value of this screen is the explicit compatible cyclic reduction and the precise distinction between orbit data and simultaneous stabilizers, with both existing operations credited.

Primary proof locations: G. Malle, author version dated October8,2013, *On the inductive Alperin–McKay and Alperin weight conjecture for groups with abelian Sylow subgroups*, Proposition6.2 and its complete proof, Remark6.1 and Corollary6.3 comparison; J. Miquel Martínez, Noelia Rizo and Damiano Rossi, *Algebra & Number Theory*20(2026),333ff., DOI10.2140/ant.2026.20.333, the sections identified above; Alex Bartel and Tim Dokchitser, *JEMS*17(2015),2473–2512, DOI10.4171/JEMS/563, §2, Remark2.1 and Examples2.2–2.4. Exact successful URLs, bytes and SHA256 are public/primary-register.json. Direct primary bodies: [Malle author PDF](https://agag-malle.math.rptu.de/~malle/download/indAMAWC.pdf), [Martínez–Rizo–Rossi published PDF](https://msp.org/ant/2026/20-2/ant-v20-n2-p04-p.pdf), [Bartel–Dokchitser published PDF](https://ems.press/content/serial-article-files/32073?nt=1). These are external primary results, not stipulated upstream truth.
