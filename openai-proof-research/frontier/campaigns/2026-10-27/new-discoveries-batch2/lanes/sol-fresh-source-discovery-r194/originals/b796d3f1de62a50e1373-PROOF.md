# Complete ordinary answer to Question 6.1(5); NOT nominated for discovery credit

Status: ordinary proof supplied; recommended credit 0 because the construction is a routine wreath-product application. No independent eligibility review, Lean certificate, acceptance, or novelty PASS. This file records a complete existential result, not finite evidence for a universal assertion.

## Exact source and hypotheses

McCulloch–Lee Tae Young, *Finite groups with many elements of the same order*, arXiv:2602.19340v2 (31 March 2026), Question 6.1(5), printed p29, asks whether there exist a positive integer k and r in (0,1) for which infinitely many finite nonsoluble monolithic groups G have rho_k(G)>=r, and asks the same for rho*_k(G). Definition 2.1 p3 sets rho_k to the fraction of elements with order DIVIDING k and rho*_k to the fraction with order EXACTLY k. Monolithic means unique minimal normal subgroup; pp5 and29 impose no bound on the number of simple factors. We satisfy even the stronger contextual restriction that the quotient by the socle is soluble. Current abstract page lists v2 as latest; the author's current page calls the paper submitted. No journal body located or journal publication assumed.

## Statement

For every integer m>=4, let H=(C2)^m, acting regularly by translation on itself, and let

G_m = A5^H semidirect H = A5 wr H.

These are finite nonsoluble monolithic groups, pairwise nonisomorphic as m varies. Their socles are A5^H, their socle quotients are elementary abelian, every element has order dividing60, and more than half their elements have order exactly60. Thus both existential questions have the fixed witnesses k=60 and r=1/2.

## Elementary base facts

The alternating group T=A5 has order60. Its order distribution is 1,15,20,24 elements of orders1,2,3,5 respectively. This follows by counting identity, double transpositions (5 choices of fixed point and3 pairings), 3-cycles (10 supports and2 orientations), and5-cycles (4!). In particular its exponent is30 and its center is trivial.

For completeness simplicity needs no classification theorem. The nonidentity conjugacy classes have sizes15,20,12,12: centralizers within A5 have orders4,3,5 respectively, with the24 five-cycles giving two classes. A normal subgroup is a union of classes including identity. None of the proper sums 1 plus a nonempty submultiset of {15,20,12,12} divides60. Lagrange's theorem therefore leaves only the trivial subgroup and T. T is nonabelian, hence is nonsoluble: its nontrivial derived subgroup equals T by simplicity. Its trivial center also follows from nonabelian simplicity. The independent checker enumerates all60 even permutations and conjugacy classes as a separate diagnostic, not as a replacement for these counts.

## Monolithic property

Write N=T^H. It is a minimal nontrivial normal subgroup of G_m. Indeed, if M is a nontrivial G_m-normal subgroup contained in N, choose f in M with f(x) nonidentity at a coordinate x. Since T has trivial center, some element of the coordinate copy T_x has nontrivial commutator with f. That commutator is supported only at x and lies in M. Hence M intersect T_x is a nontrivial normal subgroup of T_x, so equals T_x. Translation transitivity and normality of M give every coordinate factor, hence M=N.

The centralizer C_G(N) is trivial. An element with nonzero H-component moves some coordinate factor to a different coordinate factor and cannot centralize N. An element of N centralizes N only if each coordinate lies in Z(T)=1.

For any nontrivial normal subgroup K of G, the commutator [K,N] is contained in K intersect N. If that intersection were trivial, K would centralize N, a contradiction. The intersection is a nontrivial G-normal subgroup of N, hence equals N by the preceding paragraph. Thus every nontrivial normal subgroup contains N; N is the unique minimal normal subgroup. Its nonsolubility implies nonsolubility of G. The quotient is H, which is abelian. Finally |G_m|=60^(2^m)*2^m is strictly increasing, so these give infinitely many isomorphism classes.

## Uniform exact-order argument

Put t=2^m. Multiplication in G is

(f,h)(g,j) = (x -> f(x)g(x+h), h+j).

For h=0, every element has order dividing30. For h nonzero, translation by h partitions H into s=t/2 pairs {x,x+h}. The square of (f,h) has coordinates f(x)f(x+h); the partner coordinate is f(x+h)f(x), a conjugate and therefore of the same order. If L is the least common multiple of the orders of these s pair-products, then ord((f,h)^2)=L. Since the H-image has order2, ord(f,h) is even and equals2L. In particular every such order divides60.

For uniform f, the s pair-products are independent uniform elements of T: each prescribed product has exactly60 ordered factorizations, and distinct pairs use disjoint coordinates. Therefore L=30 precisely when among these products there is at least one element of each order2,3,5. The union bound gives

P(L=30) >= 1 - (3/4)^s - (2/3)^s - (3/5)^s.

There are t-1 nonzero H-components among t. Consequently

rho*_60(G_m) >= (1-1/t) [1-(3/4)^(t/2)-(2/3)^(t/2)-(3/5)^(t/2)].

For m>=4, t>=16 and s>=8. Each of the three error terms is at most (3/4)^8=6561/65536<1/9 (since59049<65536). The bracket is greater than2/3, and 1-1/t>=15/16. The displayed bound is thus greater than5/8>1/2. Also rho_60(G_m)=1. Both required existential conclusions follow with r=1/2. No asymptotic numerical inference is used.

## Strongest eligibility objection and prior-art limits

This is a routine application of a regular wreath product with nonabelian simple base and an exponent-two top group. The exact-order part repeats the elementary independent-product/lcm union-bound mechanism already proved in the source's Lemma2.2; Example2.8 already uses A5 wreath C2, and Corollary2.7 explains the monolithic reduction. No new structural ingredient beyond these familiar facts appears. Under this campaign's explicit ban on routine corollaries, recommend NO discovery nomination, even though the literal existential question is answered. Root alone adjudicates credit.

Bounded searches for the exact question/title plus wreath, monolithic and60 did not locate an explicit prior statement of this exact family answering Question6.1(5). That is not novelty evidence and does not overcome the routine objection. No claim that the source already contains this full conclusion, or that a specific older publication states it, is made. Questions6.1(1)-(4), fixed arbitrary k, optimal ratios and general epsilon_k classification remain untouched.

Falsifiers: a hidden bound on monolith multiplicity, an additional requirement of almost simplicity, failure of translation transitivity, a nontrivial centralizer of N, confusion between dividing/exact order, or dependence among disjoint pair-products would invalidate the answer. The actual printed question contains neither of the first two restrictions, and the proof addresses the latter four directly. This is not an affine/abelian-socle loophole: the socle is nonabelian and the quotient soluble.

## Independent exact checks and literal Lean feasibility inventory

`bash run-checks.sh` verifies all60 even permutations, conjugacy sizes, the Lagrange subset-sum check, all3600 pair-products in the nontrivial coset of A5 wr C2, exact rational lcm distributions through16 pair-products, and the m4 lower bound. It separately reconstructs two public finite-structure counterexamples. Hard512MiB address-space,25CPU/35alarm/40wall seconds, BLAS1. No full huge wreath group is enumerated.

Actual Lean inventory: ZERO local modules, ZERO declarations, ZERO compiled endpoints, ZERO claimed formal PASS. No Lean job run. A literal desired conclusion would quantify over the explicit types `G m = (H m -> alternatingGroup (Fin 5)) semidirect H m`, where `H m = Fin m -> Multiplicative (ZMod 2)`, equipped with the translation automorphism; the notation here specifies objects, not checked mathlib API names. Necessary unproved formal bridges are: the semidirect action and finite cardinality; A5 simplicity/nonsolubility; minimal-normal and centralizer arguments; the square/order/lcm formula; a product-count equivalence; finite union bound and exact rational threshold; the final existential source predicate and pairwise distinct orders. None is hidden behind an axiom or supplied abstract assumption. No declaration-name/API availability claim or endpoint closure is made. If ever independently deemed eligible, use only Lean4.34.1/mathlibd13f23b723b8a846827a245b89c10fc7d3f11612, strictstd3 and the user's forbidden-token/resource policy. Routine eligibility failure makes formal investment unjustified now.
