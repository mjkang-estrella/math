# 370420: ordinary argument, excluded as a routine source-ingredient bridge

This is not a discovery candidate and is not a Lean endpoint. The connected case already appears in Khan–Panigrahi–Panda (2024), whose primary HTML and proofs are retained as `sources/unicyclic-springer.html`. The following short elimination of disconnected competitors uses their coefficient identity, the source's corona expansion, and elementary permanent facts. It is precisely the kind of short augmentation of a published result excluded by TASK.txt.

Write P_L and P_Q for per(xI-L) and per(xI-Q). Suppose a finite simple graph H has both polynomials equal to those of C_n corona K_1, n >= 6. The degree and first three coefficients give order 2n, size 2n, sum of squared degrees 10n, and 6t(H) + sum d(v)^3 = 28n. The target constant term is nonzero (the degree-diagonal term of per(Q) is positive), so H has no isolated vertices. Thus

    6t(H) + sum_v (d(v)-1)(d(v)-3)^2 = 0.

Every summand is nonnegative. Hence H is triangle-free and all degrees are 1 or 3. The order and size imply exactly n vertices of each degree.

At x=1 the target permanent is 1: every pendant row has just its neighbor's column available, so all pendant edges must occur as transpositions. If two leaves of H shared a neighbor, its permanent at 1 would vanish, since both corresponding rows would be forced into the same column. Thus the n leaves have distinct neighbors among the n degree-3 vertices. Removing leaves leaves a simple 2-regular graph. Consequently H is a disjoint union of corona cycles, all of length at least 4.

For a corona cycle with r core vertices, expansion over the pendant rows at x=2 cancels the effective diagonal on the core, leaving per(-A(C_r)) for Q and per(A(C_r)) for L. These are respectively -2 and 2 when r is odd, and both 4 when r is even: the only contributing permutations are the two oriented full cycles, and, in the even case, the two perfect matchings.

If n is odd, the target P_L(2)=2 forces precisely one component, since a components of even core order and b of odd core order give P_L(2)=4^a 2^b. If n is even, P_L=P_Q for the bipartite target. H cannot have an odd cycle: at x=4 its diagonal entries x-d(v) are strictly positive, P_L is the sum of positive permutation terms, whereas P_Q changes the sign of exactly the terms with an odd number of off-diagonal entries. An odd cycle and fixed points on its complement give such a term; therefore P_L(4)>P_Q(4) if H has an odd cycle. All core cycles are therefore even. Finally P_L(2)=4 forces exactly one component. Thus H is isomorphic to the target in either parity.

Novelty assessment: this gives an ordinary full-scope proof of the pair-polynomial reading, but its only extension of the published connected characterization is a few elementary observations using the same degree-recovery machinery and the printed corona formulas. It earns zero credit under the explicit short-augmentation/routine-bridge rule. No formalization investment is justified for campaign counting. The argument does not assert characterization by either polynomial individually for odd core order; it addresses the exact pair-polynomial statement extracted from MathDB.
