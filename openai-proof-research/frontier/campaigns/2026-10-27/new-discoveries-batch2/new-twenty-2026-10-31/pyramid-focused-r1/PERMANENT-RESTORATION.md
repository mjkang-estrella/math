# MathDB321476: restored, then excluded as a routine public-theorem consequence

Zero credit; do not assign a new Lean formalization as discovery work.

Primary arXiv1104.4051v1, Section 7, Conjecture 1, equation (7.1), asks mu_1(a+b)<=mu_1(a)mu_1(b) for ALL a,b>=3. Here mu_1(n) is the maximum permanent among binary n by n matrices of row/column sum 3 containing no PROPER square submatrix of row/column sum 3. The published 2013 version retains the question as Conjecture 18, equation (92), and open problem (1). Both actual primary bodies were retrieved and the relevant passages read. The source's Lemma 5 (published Lemma 16) already handles a restricted subclass, so its golden-ratio formula is not a new result. The subsequent bound mu_1(n)<=3^(n/2) in Section 8 explicitly invokes MCI: treating it as an independent theorem to prove MCI would be circular.

The historical lane only had the literal record and held this target for restoration. No earlier accepted credit for this ID was found in the campaign ledgers. The current user permits restoring this one fallback only. A live search before construction investment located a decisive stronger public successor:

Peter Horak and Dongryul Kim, *Connected cubic graphs with the maximum number of perfect matchings*, arXiv:2006.13459v1, submitted 24 June 2020; Journal of Graph Theory 99 (2022), 671–690, DOI 10.1002/jgt.22759. Actual Sections 1–3 were inspected, not only the abstract. Theorem 3.3 is specifically the simple connected cubic BIPARTITE theorem; Theorem 1.4 is its extension to all simple connected cubic graphs. Definition 2.2 and Proposition 2.3 supply attaining graphs. The maximum for bipartite graphs with 2n vertices is

m_3=6, m_4=9, m_5=13, m_n=4 F_(n-1) for n>=6,

where F_0=0, F_1=1. Theorem 3.3 explicitly includes the small n. Remark 3.4 says its small cases were computer verified; this is a limitation of the public proof's presentation, not a new certificate or a reason to claim discovery credit for reproving it.

A second actual primary, Liu–Xue arXiv2209.13758v1, Theorems 1.4–1.5, explicitly restates the bipartite extremal result and characterizes the same extremal family spectrally. Its title in v1 is *Minimizing algebraic connectivity over cubic bipartite graphs*. The live abstract page may use the later title *Cubic bipartite graphs with minimum spectral gap*. Both are the same arXiv ID; do not infer a different theorem from the title change.

## Exact bridge to the original matrix class

Associate a binary matrix A to the simple bipartite graph with a row vertex r_i and column vertex c_j and edge r_i c_j iff A_ij=1. Row and column sums 3 mean cubic. Any proper Lambda_m^3 submatrix uses all three neighbors of each of its selected row and column vertices, so forms a union of connected components. Conversely in a connected component the counts of row and column vertices are equal, by counting its edges as 3r=3c. A proper component therefore gives a proper square Lambda_m^3 submatrix. Thus the primary's indecomposable condition is exactly connectedness in this regular setting. Finally a permutation contributing 1 to the permanent gives a perfect matching by selecting r_i c_(pi(i)), and every perfect matching gives exactly one such permutation. Therefore mu_1(n)=m_n by the public Theorem 3.3 and its attaining graphs.

## The target inequality is routine arithmetic from the public sequence

For n>=8, m_n=m_(n-1)+m_(n-2). For 3<=a,b<=7 the following table lists m_(a+b); the product m_a m_b is strictly larger in each case:

          b=3   b=4   b=5   b=6   b=7
    a=3    20    32    52    84   136
    a=4          52    84   136   220
    a=5               136   220   356
    a=6                     356   576
    a=7                           932

The factors are 6,9,13,20,32. diagnostics.py records both sides of each of these fifteen comparisons. To finish for arbitrary a,b>=3, strong-induct on a+b. If a>=8, the recurrence and induction at (a-1,b),(a-2,b) give

m_(a+b)=m_(a+b-1)+m_(a+b-2)
       <m_(a-1)m_b+m_(a-2)m_b=m_a m_b.

If b>=8 use the symmetric argument. Otherwise the table applies. These are all cases and all recurrence indices are >=8. In fact the public sequence is strictly submultiplicative on this range, which implies the requested weak inequality.

This ordinary derivation confirms exact subsumption; it is NOT offered as a new solution. A kernel-checked formalization would require a large graph-theorem certificate and would still be a formalization of public mathematics plus routine arithmetic, expressly excluded by this campaign. No small-matrix counterexample search or new permanent construction was invested after this exclusion was established. This fallback is closed for new-discovery credit; it is not merely unreviewed metadata anymore.
