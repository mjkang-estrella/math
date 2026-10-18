# A branching obstruction to Euclidean flow projection

Author-side route diagnostic by Myeongjin Kang, no affiliation; original prose CC BY 4.0. This is not a nominated result, an independent review, or a counterexample to the full T332 extension target. It supplements the frozen analytic-r39 record without modifying that record. No novelty claim is made.

The unweighted Euclidean nearest-point projection onto the finite-tree probability-flow polytope has unbounded Lipschitz constant when its input and output are measured in the tree's unit-edge weighted ell-one norm. Thus a direct replacement of path isotonic averaging by this quadratic projection does not supply the universal correction sought in T332. Other projections, corrections and direct extension constructions remain possible.

## Exact construction and proof

For an integer h>=1, attach one stem edge from root o to vertex v_0 and a complete binary tree of depth h below v_0. Edges entering level l, for 0<=l<=h, number 2^l; level0 is the stem. All edges have length1. Let C be the probability-flow polytope: every edge flow is nonnegative, the stem flow is at most1, and incoming flow minus total outgoing flow at every internal vertex is nonnegative. The resulting residuals are the vertex masses.

Let B be the matrix whose rows are the internal vertices at levels0,...,h-1. Each row has coefficient+1 on its entering edge and coefficient−1 on its two outgoing edges. Set q_e=2^(-l-1) on every edge at level l. Then Bq=0, the root mass is1/2 and every terminal leaf mass is2^(-h-1). Define lambda to be1 on every internal vertex, and set

    x=q−B^T lambda.

For every z in C,

    <x−q,z−q>=−<lambda,Bz> <=0.

Consequently ||x−z||_2^2 >= ||x−q||_2^2 + ||z−q||_2^2, so the unique Euclidean projection of x is q. This is a direct optimality proof; no differentiability or active-set assertion is needed.

Fix delta=1/4, let e_0 denote the stem coordinate vector, and put

    t=delta/(2−2^(−h)),
    r_e=t/2^l,
    q'=q+r,
    x'=x+delta e_0.

The vector q' is feasible: it transports total mass1/2+t to the terminal leaves, and t<=delta ensures positive root mass. At every internal vertex in level l set

    lambda'_l=1−t(2^(−l)−2^(−h)).

All multipliers are positive. The entering-stem coordinate gives

    (B^T(lambda'−lambda))_0=−t(1−2^(−h))=t−delta.

For an edge entering internal level l>=1 it gives

    (lambda'_l−lambda'_(l−1))=t/2^l;

for a terminal edge it gives

    −(lambda'_(h−1)−1)=t/2^h.

Thus B^T(lambda'−lambda)=r−delta e_0, and x'=q'−B^T lambda'. Also Bq'=0. The same optimality inequality proves that q' is the unique Euclidean projection of x'. Therefore the ell-one amplification is exactly

    ||q'−q||_1 / ||x'−x||_1
       = (h+1)t/delta
       = (h+1)/(2−2^(−h)),

which tends to infinity. Under the tree transport formula, the output norm is precisely W1 between the two vertex-supported probability measures. The full finite metric trees have branching but no degenerate edge lengths.

## Limits and next obligation

This rules out only the unweighted Euclidean projection for unit-edge trees (equivalently the edge-length-weighted quadratic rule on these trees). It does not rule out alternative quadratic weights, adaptive nonlinear corrections, a uniformly Lipschitz retraction, or Hilbert-domain extensions without a retraction. A compact finite-tree construction would also leave the nonproper, arbitrary complete-tree scope of T332 to address. The diagnostic is not counted toward the campaign's20 accepted results.

The accompanying exact-rational script checks the displayed feasibility, normal-cone equations and amplification for finite depths. The proof above establishes every depth; the script is a diagnostic only.
