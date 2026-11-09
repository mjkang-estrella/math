# Investigation notes

No candidate is offered for acceptance. All finite calculations below are ordinary exact diagnostics, not Lean theorems.

## 359392: a short periodic-character route, with a routine-consequence objection

The source's equation (3.18) already expresses invariant harmonic dimensions as an eigenvalue average. For a canonical subgroup of SU(2), H(p,p) is the spin-p representation; its character at rotation angle theta is 1+2 sum_{j=1}^p cos(j theta). Averaging over the classical tetrahedral, octahedral and icosahedral rotation classes gives the following numerators, divided by the rotation-group orders 12, 24, 60 respectively:

- 2p+1+8 a(p)+3(-1)^p;
- 2p+1+8 a(p)+9(-1)^p+6 b(p);
- 2p+1+20 a(p)+15(-1)^p+12 c(p).

Here a has period 3 and values (1,0,-1), b has period 4 and values (1,1,-1,-1), and c has period 5 and values (2,1,0,-1,-2). Thus the dimensions increase by exactly 1 after shifting p by 6, 12, 30, respectively. Nonnegative initial periods give exactly the three exceptional zero lists in the conjecture, with no later zeros. The cyclic and dihedral cases are already treated in source Examples 7.5–7.6; the source says canonical groups and passage to them are known.

The integer arithmetic was checked through p=10000 in scripts/projective.py. This is NOT a new significant discovery claim: finishing this route appears to be a brief specialization of the source's own averaging formula plus standard SU(2) character theory. The exact representation identification and reduction for arbitrary actions have not been formalized or independently reviewed here. This is a potential routine bridge, not a claimed literature-wide known theorem, and no Lean packet was made.

## 375614: carry-corrected transversals

Definitions and the sign of the carry were recovered from source Section 6.1 and Lemma 6.1. The source verifies p=3,5 and reports unsuccessful heuristic searches at p=7. Lemma 6.4 already proves the box bound whenever there are two independent directions with derivative image size 2. The remaining regime has all such directions in one line, or none. Summing only the source's lower bounds yields 3p^2-p-1, leaving the stated positive gap. Symmetrizing u and -u does not improve that bound because image sizes agree.

The searches operate on actual representatives in (Z/p^2 Z)^2, keep one representative in each residue class, and update the exact difference-support histogram after every single-point change. Box and random seeds were used; the normalized zero representative is fixed after initialization (random seeds may have nonzero zero representative, which is harmless translation-wise). Every saved best witness was independently re-counted by constructing its difference set. The small sweep used six seeds and 9000 attempted changes at each p=3,5,7,11,13,17. Separate deeper sweeps made 300000 changes at p=7 and p=11. No support below the box was found. This is not exhaustive coverage, and the arbitrary-function conjecture remains unresolved.

A useful next search would penalize the two-small-independent-direction regime, which the source already settles, and optimize only the remaining regime. A proof needs a structural replacement for Lemma 6.4 when the size-2 directions lie in one line, with total excess at least (p-1)(p-2). No such lemma was proved.

## 361045: Cambrian image extremality

Theorem 7.8 characterizes image elements as c-sortable permutations whose descents commute and whose left inversions avoid those of c^{-1}. Its proof uses Theorems 5.10, 6.7, 7.6; it does not compare different c. A direct c-infinity sorting-word test and a second oriented-pattern implementation give identical image counts for every orientation at rank 7. Catalan sortable counts were also checked. All orientations were then covered at ranks 8 and 9, with all permutations tested. At rank 9 the search is split by the first value of the permutation, so counts must be added coordinatewise, not compared separately. The merged counts have extrema 835 and 1239, attained by the linear and alternating orientations.

The pattern implementation uses the standard type-A c-sortable 231/312 pattern criterion; its semantic bridge has only been cross-checked computationally in this lane. The source does not specify a precise maximum rank for its numerical evidence, so no claim that rank 9 is beyond its unpublished calculations is made. No uniform injection or recurrence comparison for all orientations was found. Such a comparison, including a theorem-level passage from orientation counts to the image, is the outstanding proof obligation.

## 371647: gonality-tight graphs

Definition 2.1 is gon_2=gon_1+1; graphs may have multiple edges. The source's Theorems A and B settle quasi-banana graphs, not all tight graphs. Its source discussion and Lemma 5.3 establish the analogous algebraic-curve statement, which is not an implication for arbitrary graphs.

For a connected graph with a distinguished last vertex, let A be the reduced Laplacian. Two divisors of the same degree are equivalent exactly when A^{-1} times the difference of their non-last coordinates is integral. The scripts encode this by adj(A) modulo det(A). Let C_d be the classes of all effective divisors of degree d. A degree-d effective class x has rank at least r exactly when x-C_r is contained in C_{d-r}. This tests every effective divisor of degree r, not just vertex-supported divisors. It gives exact ordinary rank tests and can be formalized, but has not been certified in Lean here.

Initial labelled sweeps: n=2 with multiplicity at most 8; n=3 at most 5; n=4 at most 3; n=5 simple. Further canonical sweeps: all 2380 connected isomorphism representatives at n=4, multiplicity at most 5; all 712 at n=5, multiplicity at most 2; all 112 connected simple graphs at n=6. Tightness was detected by searching effective degrees through 2n, a sufficient range for rank 1 and rank 2. No genus or canonical-divisor failure was found. For the 71 tight graphs with k>=3 in the further sweeps, the full predicted sequence through r=g, absence of rank-r divisors at the preceding degree, and the stated uniqueness classes were checked. Higher r is the standard Riemann–Roch range, not separately brute-forced. k=1,2 cases were not subjected to this higher-sequence pass.

The next useful space is higher-order multigraphs outside the quasi-banana class. A full result requires a structural theorem that tightness forces genus binom(k,2) and the divisor relations. Neither finite search nor the source's special-divisor hypothesis supplies this missing theorem.

## Other finite routes and source conflicts

370685: the source's rank-19 example refutes real-rootedness of a normalized inverse KL polynomial, NOT any of the four listed claims. The program computes P,Z from the palindromicity definition and Q,Y by incidence-algebra inversion on flat intervals. It tests 351 seeded binary vector matroids of sizes 7–12 and ambient ranks 3–7, with exact rational Sturm tests and integer log-concavity. No failure. This neither exceeds the source's exhaustive corank-2 evidence through 35 elements nor exhausts all matroids of these sizes. Sparse paving, nonrepresentable and large-corank examples remain open search spaces.

362660: source Proposition 5.3 handles four variables; Corollary 3.6 gives a sufficient saturated-ideal test, not a necessary positive-definite implication criterion. We tested unique-trek marginal extras on 100 seeded five-vertex and 30 six-vertex DAGs, beyond four variables. A unique trek makes the extra covariance a monomial; positive error variances leave a union of DAGs obtained by deleting one path edge. Moralized-ancestor d-separation gives exact consequences on that restricted union. The full four gaussoid rules, INCLUDING the disjunctive fourth rule, were explored by Horn closure and branching. No missing consequence was found among 374 such extras. This deliberately does not cover non-monomial determinants or arbitrary conditioning sets, where the hard issue remains.

364539: all labelled simple graphs on 2–5 vertices were tested at four exact triples with denominator 6: (1,2,3),(0,1,5),(1,1,4),(2,2,2). Edge-colour backtracking enforces the strict error, the at-most-one-odd-degree condition, and the designated first colour whenever every odd cut meets the required threshold. No failure. The special k=2 and nearly-equal regimes are already settled in the source; unequal proportions with more colours and larger graphs remain unresolved.

370825: all labelled simple graphs on 4–6 vertices were tested for all admissible k>=3. Connectivity was checked under deletion of fewer than k vertices; super-minimality was checked under each edge and vertex deletion; local vertex connectivity used separators after removing a direct edge. Degree-k fractions are reported. Finite small graphs cannot refute existential constants a_k,b_k. The source's k=3 bounds combine immediately to settle that case; the k>=4 asymptotic separation remains the actual target.

365286: 25 seeded general-position integer point sets for each order 3–10, and every endpoint pair, were checked by exact orientation predicates and Hamiltonian-path backtracking. No counterexample. Straight-line drawings form a restricted class; these tests do not enumerate arbitrary topological simple drawings or extend the source's cylindrical, strongly c-monotone and separable-drawing theorems.

357362: source Conjecture 4.2 literally fixes off-main-diagonal entries under anti-diagonal reflection. Already a=2,c=1 is impossible, since an off-diagonal entry is fixed and would have to equal 1/2. Appendix A.2 instead reports count 4 there. The literal checker confirms this conflict and counts heights 0–3 for a=2,3. This is a source-internal definition/data problem, not a discovery. No corrected definition or endpoint is silently substituted.

365498: the literal pair-core implementation and sorting-subset feasibility test were run on all UIO area sequences for partitions (3,2),(4,2),(4,3),(5,2). The attempted model yields infeasibility already at (3,2), but ALSO disagrees with the source's own displayed pair counting discussion (the complete incomparability graph makes the printed core comparison suspect). Thus this is an unresolved semantic/convention or implementation conflict, NOT a valid refutation. The code and full rows are retained to make the failure auditable. Do not count this diagnostic as mathematical coverage of the intended arbitrary-partition claim without recovering the authors' implementation/conventions.
