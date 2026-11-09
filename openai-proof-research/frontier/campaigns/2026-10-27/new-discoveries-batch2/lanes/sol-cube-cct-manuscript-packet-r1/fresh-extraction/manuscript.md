# A six-point obstruction to common-cover transitivity of the cube

Research manuscript | 30 October 2026 | Unpublished

## Abstract

The action of all real linear automorphisms of the centered five-dimensional cube on the Boolean algebra of its 32 vertices is not common cover transitive. We give two five-point sets covered by one six-point set, an explicit linear cube symmetry transporting the two deletions, and a pair-sum fiber invariant excluding every transport in the six-point set's stabilizer. This answers Question 6.6 of Hemminger, Landesman and Yao negatively. A Lean certificate proves precisely the dimension-five statement for the full real linear group. Priority remains subject to the bounded literature and registry limitations recorded below.

## 1. The action and the source question

Put C = {-1,1}^5 in R^5 and let G consist of all invertible real linear maps B with B(C) = C. The Boolean algebra P(C) is ordered by inclusion. Its cover relation U <. T means U is a subset of T and T contains exactly one point outside U. Thus this is the Boolean algebra on 32 ground elements, not on the five coordinate positions or the ten signed coordinate directions.

An action on a poset is common cover transitive (CCT) if, whenever U <. T and W <. T and W belongs to the orbit of U, some element of the setwise stabilizer of T sends U to W. This is Definition 1.4 of [1]. Its Question 6.6 asks whether the real linear automorphisms of the centered n-cube induce a CCT action on the Boolean algebra on its 2^n vertices.

**Theorem 1.** The action of G on P(C) is not CCT. Consequently the universal assertion in published Question 6.6 of [1] has a negative answer.

The proof uses the entire group G. In particular, it does not infer failure for G merely from failure for a subgroup of signed coordinate permutations. A linear equivalence preserving C also preserves its convex hull; conversely a linear automorphism of that solid cube permutes its extreme points. The formulation above therefore matches the published cube action.

Theorem 1.5 of [1] gives CCT as a sufficient condition for Peckness of an edge poset. Our theorem does not refute the Peckness conjecture, Conjecture 1.3 of [1]. We make no claim of a smallest witness or any classification in dimensions below five. The main theorem and the formal certificate are restricted to dimension five; this already settles the universal question.

The source appeared online on 6 October 2016 and in Order 34 (2017), 441-463, DOI 10.1007/s11083-016-9408-x. Its first page records receipt on 18 March 2015 and acceptance on 1 September 2016. The inherited arXiv metadata records v1 on 19 January 2015 and v2 on 10 December 2017; the v2 date is not the first-publication date.

---PAGE---

## 2. An invariant for the full linear group

Encode an integer v between 0 and 31 by its five binary digits b_i(v), with bit 0 least significant, and write p(v)_i = (-1)^{b_i(v)}. This gives a bijection from {0,...,31} to C. We identify point sets with their integer labels.

For x,y in C define the ordered pair-sum fiber size

    w(x,y) = |{(u,v) in C x C : u + v = x + y}|.

The fiber ranges over all 32 x 32 ordered pairs of cube vertices, not merely pairs in the witness. If B belongs to G, the bijection (u,v) -> (Bu,Bv) takes the fiber at x+y onto the fiber at Bx+By. Additivity gives one implication; injectivity of B gives the reverse. Hence w(Bx,By) = w(x,y) for every B in the full group G.

For a finite T contained in C define s_T(x) = sum over y in T of w(x,y). If B(T)=T, permutation of that finite sum yields s_T(Bx)=s_T(x). Therefore a point of T whose score occurs only once must be fixed by every element of its full setwise stabilizer.

For independently checking the finite table, w(x,y) = 2^{d(x,y)}, where d is the number of coordinates in which x and y differ. Indeed, if x_i=y_i, the coordinate sum is 2 or -2 and forces u_i=v_i=x_i. If x_i differs from y_i, the sum is zero and there are precisely two ordered choices (u_i,v_i). Multiplication over the five independent coordinates proves the formula. The formal certificate instead checks each displayed fiber directly and does not assume this general formula or a classification of cube symmetries.

## 3. The two deletions

Take Z={2,9,10,13,19,20}, X=Z minus {9}, and Y=Z minus {2}. Each deletion has five points, so X <. Z and Y <. Z. The real linear map

    A(x_0,x_1,x_2,x_3,x_4) = (-x_0,x_4,x_3,x_1,x_2)

preserves C and has inverse (-x_0,x_3,x_4,x_2,x_1). In binary labels it permutes bit positions by 0->0, 1->3, 2->4, 3->2, 4->1 and then flips bit 0. Its values on X are

    2 -> 9,   10 -> 13,   13 -> 20,   19 -> 10,   20 -> 19.

Consequently A(X)=Y, verifying the full-group orbit hypothesis. Negating a coordinate is linear in the centered real model; the binary labels serve only as an encoding.

---PAGE---

## 4. Excluding every stabilizer transport

In the indicated row and column order the complete 36-entry fiber table and its row sums are:

| x / y | 2 | 9 | 10 | 13 | 19 | 20 | score |
|---|---|---|---|---|---|---|---|
| 2 | 1 | 8 | 2 | 16 | 4 | 8 | 39 |
| 9 | 8 | 1 | 4 | 2 | 8 | 16 | 39 |
| 10 | 2 | 4 | 1 | 8 | 8 | 16 | 39 |
| 13 | 16 | 2 | 8 | 1 | 16 | 8 | 51 |
| 19 | 4 | 8 | 8 | 16 | 1 | 8 | 45 |
| 20 | 8 | 16 | 16 | 8 | 8 | 1 | 57 |

The score 51 occurs only at vertex 13. Suppose B belongs to G, B(Z)=Z and B(X)=Y. Score invariance forces B(p(13))=p(13). Since B is a bijection and respects both set images, it sends Z minus X to Z minus Y, so B(p(9))=p(2). Pair-sum invariance would then give

    2 = w(9,13) = w(B(9),B(13)) = w(2,13) = 16,

a contradiction. This proves Theorem 1. All six scores need not be distinct; only the uniqueness of the score at 13 is used. The table consists of exact finite cardinalities, not numerical approximations. No orbit enumeration or assertion that the stabilizer is trivial enters the proof.

## 5. Formal scope and correspondence

The immutable Lean sources are Finite.lean, Cube.lean and Endpoint.lean. Their closed endpoint is Cube.literal_question66_false : Not Cube.LiteralQuestion66AtFive. Its statement quantifies all finite vertex sets U,W,T, actual mathlib covers U <. T and W <. T, a real linear cube-preserving transport U to W, and the required stabilizing real linear transport. There are no residual symmetry, distance, extension or stabilizer assumptions.

Finite.lean defines integer coordinate sums, the complete ordered fibers and their scores, verifies the 36 counts with kernel decision procedures, and proves the finite-set obstruction. Cube.lean identifies the integer sum relation with real vector equality, proves its invariance under any realizing real linear equivalence, and transports the fiber cardinality by a product bijection. Endpoint.lean proves that the binary encoding exhausts all sign vectors, constructs both directions of the finite-permutation/full-real-linear interface, supplies A and the two cover proofs using Finset.erase_covBy, and concludes the literal negation.

Audit.lean enumerates the actual environment by module origin and prints full types, safety tags and transitive axiom closures. A fresh strict extracted replay verifies all 134 actual declarations, including generated/private declarations: 92 from Finite, 10 from Cube and 32 from Endpoint. All are safe, no partial definitions occur, and the only axioms are propext, Classical.choice and Quot.sound. The certificate formally proves dimension five only. No uniform higher-dimensional formal claim is made.

---PAGE---

## 6. Classical relations and bounded priority

The source's Proposition 4.20(2) produces a non-CCT left-regular action for every finite group that is not elementary abelian of exponent two. That theorem uses the group itself as the ground set: 3840 points for the five-cube symmetry group, rather than 32 cube vertices. It therefore does not directly settle the specified action. Enlarging a group can introduce missing stabilizer transports, so subgroup failure alone is insufficient.

Pseudosimilar vertices and broken-orbit constructions are classical. In Kocay [2], the inspected partial-permutation framework and Construction 4.5 build graphs using cosets and a Cayley/graphical-regular-representation component. These bodies supply relevant mechanisms but no immediate five-cube realization with the required ambient stabilizer obstruction. We do not claim the generic mechanism as new.

Pebody [3] studies reconstruction from decks under translations of the binary cube. Its introduction and initial construction proofs concern the regular translation action, rather than the full linear cube group, and compare decks of two sets rather than two one-point deletions of a fixed union. Gross and Grupel [4] use the full cube isomorphism group; the inspected Proposition 3.7 and its proof transfer nonisomorphic perfect codes to nonisomorphic supports, while their indistinguishability concerns random-walk scenery distributions. Those conclusions do not themselves supply the deletion transport required here. These are comparisons of inspected local bodies, not paper-wide absence claims. The frozen reviews record additional inspected graph and configuration sources and exact coverage.

No complete classical-to-target subsumption bridge was found in this bounded evidence. Nevertheless, current public proof-registry heads/bodies and comprehensive citing coverage remain unestablished. The Kimble-Schwenk-Stockmeyer 1981 Wiley body returned 403; the Godsil-Kocay 1982 original was not obtained. These gaps remain parked. No denied GitHub, ScienceDirect or Google challenge route was retried, and no new network retrieval was performed for this manuscript. Preparation of this packet does not clear the novelty hold, establish worldwide priority, or constitute acceptance or discovery credit.

## References

[1] D. Hemminger, A. Landesman and Z. Yao, Peckness of Edge Posets, Order 34 (2017), 441-463. DOI: 10.1007/s11083-016-9408-x. Published online 6 October 2016. Published Definition 1.4, Theorem 1.5, Proposition 4.20 and Question 6.6 inspected.

[2] W. L. Kocay, Graphs, groups and pseudo-similar vertices, J. Austral. Math. Soc. (Series A) 37 (1984), 181-189. DOI: 10.1017/S1446788700022023. Partial permutations and Construction 4.5 inspected.

[3] L. Pebody, Set Reconstruction on the Hypercube, Discrete Analysis 2017:17, 10 pp. DOI: 10.19086/da.2108; arXiv:1607.05675v2. Definitions and initial construction bodies inspected; no complete Fourier-chain audit claimed.

[4] R. Gross and U. Grupel, Indistinguishable Sceneries on the Boolean Hypercube, arXiv:1701.07667v1 (26 January 2017). Full-cube isomorphism definition and Proposition 3.7 with local proof inspected.

Prepared with OpenAI Codex. No human authorship or additional credit is assigned by this packet. Source bytes, access receipts, full formal audit, reconstruction instructions and bounded limitations accompany the manuscript.
