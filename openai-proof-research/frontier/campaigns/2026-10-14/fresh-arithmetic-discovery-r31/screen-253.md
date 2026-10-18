# Family 253: small-slot finiteness screen

Status: closed before target freeze, no nominee. The proposed direction was higher finiteness for the source's fixed finite-track alternating polygon group. No all-degree theorem was proved or frozen. The two elementary obstructions below delimit one attempted geometric bridge; neither is an obstruction to type F_infinity itself.

## Source and prior operation

Use the source's O=Z[tau], tau=(1+sqrt(5))/2, permitted polygon cuts, area measure, and fixed finite track space mX of area m. All F_m maps, hence all A_m maps, preserve area. Every nonempty clopen polygon has positive area. The source proves comparison for strictly unequal areas, a small-support extension lemma, and simplicity; its final finite-presentation proof uses a finite central cover and low-degree homology. Its corner-module/Koszul argument gives coefficient homology finiteness in every degree. None of these statements alone is a finite projective resolution over Z[A_m].

The complete structural r28 screen had already identified the dimension bound for unit-area slots and had mentioned small-polygon compression. This round does not relabel that observation as a new theorem. The concrete operation tested here was to replace those slots by squares of side tau^(-b), then normalize every resulting complement to a known full-track group. The following calculation prevents that normalization in general.

## 1. Finite vertex orbits versus disjoint-slot dimension

Let a group preserve a finite measure M. Consider a simplicial or semisimplicial slot complex whose vertices have positive-measure supports, with disjoint supports at each simplex, and suppose that the group action preserves these supports and their measures. If the vertices have only finitely many group orbits, their areas belong to a finite positive set. Put delta equal to its minimum. Every p-simplex then satisfies (p+1)delta <= M. Thus its dimension is at most floor(M/delta)-1.

This applies also when the allowed slots have different shapes and sizes. In particular, slots of areas tau^(-2b), with unbounded b, belong to infinitely many orbits under A_m or F_m. A uniform homothety by tau^(-b) respects the arithmetic cut parameters, but changes area; it is not a member of either group.

This does NOT prohibit a filtration with finite orbit sets at each stage and increasing dimension. Brown's criterion permits such filtrations. It also does not say that bounded dimension itself precludes contractibility. It only rules out simultaneously obtaining arbitrarily large disjoint simplices and a finite set of vertex orbits by this construction.

## 2. Exact complement normalization obstruction

Let b>=1 and let U_b be a square of side tau^(-b) inside one track. For a tuple of k disjoint translated copies, the unused region has area

    A = m - k tau^(-2b).

If this region were piecewise-translation equidecomposable with ell copies of U_b, area would give ell=m tau^(2b)-k. The identity

    tau^(2b) = F_(2b) tau + F_(2b-1)

and F_(2b)>0 show that ell is not an integer for any positive integer m. This is an obstruction even before considering any finer scissors invariant.

There is a stronger obstruction to choosing a different uniform unit scale. Write conjugation in Q(sqrt(5)) as a bar; bar(tau)=-tau^(-1). Then

    bar(A)=m-k tau^(2b),
    Norm(A)=(m-k tau^(-2b))(m-k tau^(2b)).

Whenever k tau^(-2b)<m<k tau^(2b), this norm is negative. A homothety by tau^a multiplies area by tau^(2a), of norm 1. A positive integer number ell of unit tracks has norm ell^2>0. Consequently no combination of piecewise translations and a single uniform unit homothety can convert this complement into an integer number of unit tracks. The same statement covers any sequence of uniform such homotheties and translations, since its total area multiplier is again tau^(2a).

For every positive integer m, k=1 and all sufficiently large b satisfy both strict inequalities. The example therefore occurs in the very small-slot regime needed to raise connectivity. The scalar homothety preserves the four permitted directions and O-valued levels because tau is a unit, so the obstruction is not an artifact of choosing an arithmetically forbidden scaling.

This does NOT rule out an abstract isomorphism between stabilizer groups, a different piecewise nonuniform similarity construction, or any other proof of higher finiteness. Such operations have not been constructed here. In the full group, the pointwise slot stabilizer is the full group on the unused region; in A_m it is the intersection of that full group with A_m. One may not identify it with the alternating group of the unused region without a separate argument.

## 3. Primary comparison and precise unpaid obligations

Xin Li's actual Theorems 5.13–5.14, Remark 5.16, Theorem 5.18 and Corollary 5.20 already supply all-degree homology invariance under adding pieces and passing to nonempty reductions for minimal ample groupoids with comparison and no isolated units. The proof uses arbitrarily many small equivalent pieces together with a residual piece, then stability and comparison. Thus the presence of a residual piece does not obstruct ordinary homology localization. The source's stated hypotheses place its groupoid in this setting. No new homology localization operation is claimed here. Li does not in these statements supply the stabilizer finiteness needed for the proposed F_infinity construction.

Brown's Theorem 2.2 assumes an n-good complex: acyclicity below n and FP_(n-p) stabilizers for p-cells, plus a filtration with finite n-skeleta modulo the group. Its condition is essential triviality of the reduced homology systems, stronger than a zero direct limit. Remark (2) allows equivariant continuous bonding maps rather than inclusions. Corollary 3.3 gives a useful sufficient criterion using a contractible complex, finitely presented FP_infinity stabilizers, finite-orbit stages, and increasing relative connectivity. These hypotheses are not established for the proposed slot system.

The missing construction is therefore specific: produce a compatible equivariant system of complexes for one fixed A_m, with finite orbit sets through each requested dimension, prove the required uniform vanishing/relative connectivity, and establish the appropriate FP_(n-p) stabilizer properties for punctured polygon regions. Source comparison and the area estimate do not supply the latter. Distinct scales also have distinct domains; no bonding maps have been defined. A unit square cannot be tiled by finitely many squares all of side tau^(-b), since the requisite count tau^(2b) is irrational. Introducing residual pieces is possible, but introduces the stabilizer problem above rather than resolving it.

The source's higher coefficient homology and Li's homology equivalences cannot be substituted for these module-resolution or cell-finiteness conditions. No theorem asserts impossibility of satisfying them. This round stops because no concrete closure mechanism was found, not because the broader direction has been disproved.

## Attribution and scope

Source: An Infinite Finitely Presented Simple Amenable Group, pinned fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; actual labels include lem:comparison, lem:extension and lem:hom-coefficient-finiteness. Primary bodies: Xin Li, arXiv:2209.08087v2, https://arxiv.org/html/2209.08087v2 ; Kenneth S. Brown, Finiteness properties of groups, J. Pure Appl. Algebra 44 (1987), 45–75, https://pi.math.cornell.edu/~kbrown/scan/1987.0044.0045.pdf . Szymik–Wahl was located but not read beyond the returned opening; no proof attribution rests on it.

The elementary area arguments are route diagnostics, not a substantial theorem candidate. There is no acceptance, count change, literature novelty claim, or narrowed substitute. Original exposition by Myeongjin Kang, no affiliation; CC BY 4.0. Third-party bodies remain private.
