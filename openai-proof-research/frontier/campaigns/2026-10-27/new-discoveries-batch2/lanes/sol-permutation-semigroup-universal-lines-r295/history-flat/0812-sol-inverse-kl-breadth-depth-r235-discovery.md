# Exact claim separation and sustained ear-intersection attack

## Main lead: public resolution, not a discovery

Original Gao–Xie primary body: https://arxiv.org/pdf/2007.15349v1 (30 July 2020 preprint; JCTB151 (2021),375–392). Actual Section4, Conjecture4.2: for every matroid M, Q_M's coefficients are log-concave and have no internal zeros. Their Proposition4.3 proves uniform matroids; its explicit formula does not cover arbitrary matroids. Braden–Ferroni–Matherne–Nepal https://arxiv.org/pdf/2510.01086v2 (22 October 2026, first 1 October 2025), Conjecture1.2(c), repeats the ordinary log-concavity question. Theorem1.4 assumes M loopless and e not a coloop and subtracts a sum over F containing e with F\e not a flat, weighted by tau((M|F)/e) t^(rk F/2) Q_(M/F). Positive-term convolution induction alone does not handle this subtraction.

Actual Theorem5.3's rank19/21-element matroid is dual to a rank-two partition matroid with parallel classes (4,4,4,3,3,3). Its ascending Q coefficients are (163,1790,10323,39217,106659,215169,323646,350404,232662,71162). Exact interior determinants are (1521451,36365899,436932232,2937859608,11777939847,29350655040,47482837564,29196156796), all positive. Nonreal roots after binomial weighting do not refute this statement.

r98 already screened Xie–Zhang's stronger simple-matroid transform conjecture. It explicitly distinguished ordinary Q log-concavity. r30's additive-gap two-matroid independence polynomial is a different invariant and hypothesis. Thus these reports alone did not settle this exact target. The broader history screen bound 2477 compact reports before reading their text (history-bindings.json); the lexical screen is not semantic completeness.

Fresh exact-title arXiv search exposed **Badalov, https://arxiv.org/pdf/2609.13417v1, 11 September 2026**, actual Proposition3.3 proof, not merely abstract. Let V=F_2^10, W=span(e1,e2,e3), X=span(e4,...,e10), H=span(e4,...,e9). Represent M by the distinct nonzero columns

    (V\{0}) \ ((W\{0}) union (X\H)).

There are 1023-7-64=952 columns. The surviving basis listed in Proposition3.3 verifies rank10 and noncoloop deletions. The published proof starts with Q=(34705212702720,475418034176,609014784,89280) and for j=0,...,63 changes Q by -2^36 + ((504-j)2^28-2^36)t. It proves the quotient geometry and line counts, rather than treating an arbitrary polynomial as a matroid. Summing gives

    Q_M=30307166191616+4194859712512t+609014784t^2+89280t^3,
    Delta_2=609014784^2-4194859712512*89280=-3618068002504704.

checks.py replays this exact integer summation and determinant; it does not independently enumerate the 952-element flat lattice. This is a public in-scope refutation. Its first posted date precedes the October22 successor version; the latter's continued conjecture label is not novelty evidence. TheoremC's stronger sign-prescription proof is not needed for retirement. No new claim is made from the paper's first-index residual question, which is a restricted part of this retired family.

## Sustained survivor and literal scope

Leader–Tan, https://arxiv.org/pdf/2610.39116v1, first29 October2026, source body dated30 October2026, Sections1 and4: for every convex n-gon, does each family of triangulations whose every two members share an ear have size at most C_(n-3)? An ear at vertex i is the diagonal (i-1,i+1), indices cyclic. We use n>=5 so ears have distinct diagonals. n4 has two triangulations and the bound1 directly; n3 is trivial. All-ear intersection is the selected full scope; not arbitrary diagonal intersection (Kalai's larger question), not a fixed ear, and not the source's already-proved n-1 allowed ears case.

Original larger question body https://mathoverflow.net/questions/114646/intersecting-family-of-triangulations was fetched and read. It asks the C_(n-3) bound for common arbitrary diagonals; the 2026 authors' all-ear subquestion is explicit in their own concluding Section4. Do not attribute the all-ear formulation verbatim to the older post. Original source chronology is in the frozen HTML; source reference11 cites its November28,2024 version. A fresh arXiv exact ear-intersecting search returned this paper alone; that is a narrow status check, not clearance of all later work.

Source Theorem2 already proves the C_(n-3) bound with any one ear excluded. Theorem3 proves C_(n-3)+C_(n-5) for all-ear intersection. Actual Section3 compression proof and Section4's obstruction discussion were read. Borg–Feghali, https://arxiv.org/pdf/2008.02342v2,5 December2020, actual Theorem3 proof pp2–3, proves that an intersecting family of separated r-subsets of an n-cycle has size <=binom(n-r-1,r-1). Its shift/decomposition proof is uniform and cardinality based. It does not apply directly to the nonuniform weights here.

## All-n exact reduction

Let I_n be separated subsets of Z/nZ (no cyclic neighbors), and C_k=binom(2k,k)/(k+1). For S in I_n let w_n(S) count triangulations with exactly that ear set. Prescribing all ears in T in I_n removes |T| nonadjacent vertices, leaving a convex (n-|T|)-gon. Thus the number containing T is C_(n-|T|-2). Inclusion-exclusion proves the literal identity

    w_n(S)=sum_(T in I_n, T contains S) (-1)^(|T|-|S|) C_(n-|T|-2).

A maximal ear-intersecting triangulation family includes every triangulation of any admitted ear pattern, so the entire source target is equivalent to

    sum_(S in A) w_n(S) <= C_(n-3)

for every pairwise-intersecting A subset I_n with positive weights. This is an exact finite weighted-clique optimization for each n, not an asymptotic replacement. Summing all w gives C_(n-2); summing patterns containing a fixed vertex gives C_(n-3). checks.py independently compares these weights to recursively enumerated literal triangulations through n10 (2052 triangulations total across n5,...,10) and checks total/star identities through n13. ear_solve.py uses integer branch-and-bound with a valid weighted coloring upper bound, giving exact optima 2,5,14,42,132,429 for n5,...,10. No float solver or numerical root test enters these checks. These finite outcomes are diagnostics, not discoveries or the missing all-n theorem.

## Three mechanisms, exact failures, and remaining route

1. **Transfer the nearest actual proof.** Borg–Feghali's shift sends a set containing n to one replacing n by n-1 if n-2 is absent. It preserves separatedness and cardinality. At n6, in zero-based labels, S={2,5} has w=2 whereas its shifted image {2,4} has w=1. Therefore a singleton intersecting pattern family already loses weight under this step. Rotating the chosen endpoint does not justify a uniform weight-preserving theorem. The ordinary proof needs a weighted compensation term, not just its cardinality identities.

2. **Cyclic averaging orbit by orbit.** Since w is rotation invariant, one could try to bound the number of intersecting members in each rotation orbit O by |S||O|/n, its fixed-point star contribution. At n6 the orbit of {0,2} contains the pairwise-intersecting subfamily {{0,2},{0,4},{2,4}}, size3, while a star uses2 orbit members. Every pattern in this orbit has weight1. This refutes that proposed lemma exactly. It does not refute the full target: the global optimum is5, and the triangle family has weight3. Global compensation across orbits is essential.

3. **Fractional bounds from disjoint pattern collections.** The pentagon has five positive patterns, all weight1. Their disjointness graph is C5. Giving each pattern fractional value1/2 satisfies every inequality that a pairwise-disjoint collection has total <=1 (such collections have at most2 members). Its objective5/2 exceeds the target2. Consequently an upper certificate using only those clique constraints cannot establish the desired sharp inequality. Odd-cycle/integrality constraints are necessary already in the smallest nontrivial case. This is a rigorous LP obstruction, not a source counterexample.

The next substantive calculation is a weighted version of the shift's C/D decomposition retaining its gap-dependent inclusion-exclusion weights, with an inequality compensating the 2-to-1 loss above across other ear patterns. Alternatively, an all-n integer-stable-set certificate must include odd-cycle constraints and cross-orbit interactions. The exact objective/kernel is now specified; neither such certificate nor a uniform compensation inequality has been proved. Extending the six small optima alone will not resolve it.

## Qualification limit

No full ordinary source result, no PROOF.md, no novelty PASS. Compact report alias screening found no triangulation hit; two tempting alternatives were positively rejected as old lanes. Unavailable historical registry intervals stay parked; denied GitHub routes, ScienceDirect and challenge routes were not retried. No complete current registry tree/body comparison was possible, and no absence claim is inferred. Root may retain this survivor for mathematical work but should not start acceptance/formalization on this packet.
