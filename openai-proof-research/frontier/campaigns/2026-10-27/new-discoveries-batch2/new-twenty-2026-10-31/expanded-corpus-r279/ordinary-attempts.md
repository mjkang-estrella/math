# Ordinary attempts and stopping gaps

These are unsuccessful discovery notes, not new results or execution assignments. No solver, enumeration, numerical experiment, or Lean run was performed. All three routes were assessed against the full literal question.

## 374489: puncturing and inclusion

The source is arXiv:2604.27868v1, Conjecture 7.4 and Theorem 7.5, pp. 44–48. A row puncture is injective on a distance-d code when d > 1: a word supported on the deleted row would have rank at most one. Thus its dimension remains n(n-d). The desired square MRD supercode has dimension (n-1)(n-d+1), a difference of d-1. This identifies the genuine task as adding d-1 directions while keeping every nonzero word of rank at least d-1, rather than merely recovering lost dimension.

First approach: start from a rectangular Gabidulin code, project the output modulo a one-dimensional subspace, and try to identify the image with a nested square Gabidulin code. Projection lowers rank by at most one, but does not supply the requisite common extension-field structure of degree n-1. Rank preservation alone does not establish containment. Choosing an arbitrary complementary space fails because mixed sums can have small rank. No uniform algebraic construction emerged.

Second approach: dualize the containment. The punctured code's Delsarte dual would have to contain a distance-dimension-compatible square MRD subspace. This is a real semantic condition, not a dimension count. The October 2026 paper arXiv:2610.17570 solves (4,3) by semifield orthogonality; its introduction and conclusion explicitly report failure in general. Prajapati arXiv:2608.08478v1, Theorem 1, Lemmas 2–4, Proposition 5 and Corollary 6, explicitly identify the failed instance as (5,3,F₂). I read the reduction and the computational elimination statement, including the printed spread bases, four surviving kernel representatives and eleven-generator lower-bound code. I did not execute or independently certify Proposition 5 or its auxiliary repository. This is a prior public proof claim excluding new discovery credit, not this lane's certified refutation.

The published diagram E = (5,5,5,5,1,1) has distance-three bound 12 and claimed optimum 11. Its transpose has column heights (6,4,4,4,4), matching the differently ordered notation in the October paper. The source equivalence already supplies the reduction. Repackaging that obstruction, or formalizing it, would not be a new solution.

## 404651: shuffle factors

The primary report has two relevant passages: PDF p. 15, the literal question, and p. 33, the subsequent progress report. The latter already proves the Tutte reformulation and excludes a particular extreme-window construction. It reports acyclicity through k = 5. Small k cannot receive new credit.

First approach: match positions into k increasing pairs or k decreasing pairs in each consecutive block of length 2k. Such a matching is exactly a perfect matching in the complement of the inversion graph or in the inversion graph, respectively. Neither graph must have a perfect matching: the permutation 1432 gives an isolated vertex plus a triangle on one side, and a star on the other. Thus a one-window theorem is false even at k = 2.

Second approach: use overlapping windows to force descent of an obstruction statistic. By Tutte, a bad window contains, after deleting l positions, l+2 odd blocks in a direct sum; the complementary condition gives an analogous skew sum. The intended statistic would combine the two odd-block deficits. Sliding a window can replace an extreme entry with an interior entry, changing both decompositions; no monotonicity or bounded potential was established. The source's Proposition 2 already handles the case that every window begins or ends in an extreme, so repeating that argument would only reproduce published progress.

Third approach: exploit cycles in the finite factor graph. A cycle forbidding length-2k shuffles would defeat the stronger p = 2 assertion, but would not by itself defeat the literal question, which allows a factor of length pk for any p >= 2. One would still need an infinite family avoiding every such length and pattern. Conversely, proving acyclicity for all k would suffice, but is exactly the source's existing open mechanism. No new acyclicity proof, realizable all-length avoiding family, or certificate plan beyond generic encoding was obtained. Park.

## 375790: all extremal graphs for PED sets

Source arXiv:2607.03894v1, §2.2 and Conjecture 5.3. A PED set P has each edge outside P adjacent to exactly one edge of P; edges inside P have no such restriction. Counting only induced matchings is therefore incorrect. The source encodes P by black/yellow/white vertex labels and proves multiplicativity over components. Its Theorem 3.12 already separates every triangle in an extremal graph into a whole component. Its proof uses contraction, deletion and comparison injections; I read its statement and several cases, not all of the long proof.

First approach: repeat triangle replacement on a four-cycle. A triangle admits only the all-black pattern or the choice of a single white vertex. A C4 admits the all-black pattern and four edge choices (five PED sets in all). Once attachments are allowed, yellow vertices can receive their unique nonwhite neighbor outside the cycle. Restriction to the cycle is therefore not a closed five-state object, so the triangle injection does not automatically extend. The source explicitly identifies this obstacle after Conjecture 5.3.

Second approach: reduce to a bound on connected triangle-free components. For the proposed products, a triangle contributes 4 and a four-cycle 5. The cycle recurrence from source Theorem 5.2 gives counts 4,5,6,10,15,21 for C3 through C8; these do not beat the proposed disjoint products. These values follow symbolically from the displayed initial values and recurrence; no enumeration was run. Even proving the source's connected-cycle conjecture 5.1 would then need an equality-sensitive integer product optimization. Conjecture 5.1 is itself unproved in the general connected case, so it cannot serve as an input.

Third approach: encode PED sets by their white independent set W. The remaining vertices and their degrees in G-W force the yellow/black labels. Validity further requires every neighbor of W to have exactly one neighbor outside W. This is more restrictive than independence, but the simple independent-set bound is exponentially too large (2^n versus the desired scale near 4^(n/3)). A branching argument must charge these forced yellow neighborhoods and retain equality cases, including isolated vertices and edges. No such recurrence was proved for arbitrary triangle-free connected graphs. A fixed graph exceeding the proposed product would refute the conjecture only after proving that every graph in the printed class at its order has smaller count; no such witness was produced. Park without a generic solver request.

## Other scope barriers

335299 has the exact formal-series identity F(z²) = F(z)(1/(1-z) + z^r/(1-z^m)), with F=C-D. Derivation: equality of distinct unordered representation functions says C²-C(z²)=D²-D(z²), and the covering/intersection conditions determine C+D. This identity determines coefficients once the constant sign is fixed, but forcing all coefficients into {-1,0,1}, with zeros exactly on r+mN, for every degree is the unresolved classification. The source's Theorem 6 is conditional on another conjecture. A finite prefix does not solve it.

400235: cyclic-group addition tables fail a naive mixing route on subgroups. For d=2 and subgroup H of order h, H×H×H has h² ones but expected h³/n; when h is proportional to n this discrepancy has order n², larger than sqrt(h³) of order n^(3/2). This only rejects that construction and does not refute existence of other arrays.

403683: source Theorem 5 preserves odd girth, which does not prohibit shorter even cycles. It does not imply the same-girth Conjecture 4; the source specifically leaves C5 interesting. 365880: passing to the r-clique hypergraph and applying an ordinary Ramsey bound does not ensure an induced copy of a noncomplete F in the host graph.

353260: monotonicity of chi(G_[1,b]) in b does not imply the integer-valued function has no jumps. An upper coloring at one b and a lower finite graph at another b leave exactly the equality issue in the question. 355457: the source supplies an unspecified distance constant; replacing it by 100 is an unproved quantitative bridge. An arbitrary palette with more than five named colors gives a wording defect, not an eligible mathematical refutation.

401378: m=n admits the familiar simplicial-cone realization by a nonnegative matrix (with the matrix indices oriented to the ray graph convention). That parameter case is not a classification for all m,n. A quantified real feasibility encoding of cones and faces just restates realizability and is excluded as a generic encoding.

397840: choosing a Dirichlet eigenfunction at lambda=lambda_j gives zero, not a negative value. Choosing the first eigenfunction for lambda>lambda_1 fails the lambda-harmonic equation. The indefinite spectral quadratic form being negative somewhere in L² does not ensure it is negative on H(lambda). No analytic full route survives.
