# Sustained attempt: Swanepoel's finite central-symmetry question

Status: incomplete full source question; no discovery credit. Source: Garber–Roldán-Pensado, https://arxiv.org/pdf/1801.07238v1 (22 January 2018), printed p1 Question, pp2–3 Lemma2.3/Theorem2.5, p5 Lemma4.1. A set is in c.s.c. position when contained in the boundary of a centrally symmetric planar convex body. The question asks whether there is a fixed integer k such that every planar set X whose every k-point subset is c.s.c. is itself c.s.c. For finite-set formulations require |X|≥k, avoiding vacuous small sets. This lane addresses finite configurations only; the source also says arbitrary planar sets, so even a finite theorem would need the corresponding compactness argument and nondegeneracy treatment.

The actual source supplies a nine-point minimal obstruction (p3–4), proving k≥9, and proves the closed-curve version with k=6 (pp5–7). Neither is a full finite-set theorem. No same-question history alias was found in the verified 876-report index. The Swanepoel surname hit is an unrelated penny-graph question. Current registry clearance remains unavailable; the lawful arXiv exact-phrase query is bounded evidence only.

## Mechanism A: exact arrangement and the obstruction to ordinary Helly

For a finite noncollinear X in convex position put M_X={O: every point of X lies on the boundary of conv(X∪(2O−X))}. The source's Lemma2.3 proves M_X=intersection over triples T⊂X of M_T. Each M_T is the union of four closed convex regions cut out by its three midparallel lines (Lemma2.2). Theorem2.5 reduces the family to tallest triangles, but their number still depends on |X|.

For the square P={(±1,±1)}, Lemma4.1 gives M_P={x=0}∪{y=0}. In particular (1,0),(0,1) belong but their midpoint does not. Thus applying planar convex Helly directly to M_T is invalid. The exact Fraction implementation independently tests exposed boundary membership via convex hulls, finds the arrangement vertices, and checks the triple criterion on 169 rational centers. This is diagnostic, not an inference of a uniform theorem. Nor does a finite union of four convex sets alone have a bounded Helly number: complements of small open arcs covering a circle already warn against uncontrolled holes/branch switching.

## Mechanism B: a uniform restricted witness theorem

The following ordinary deduction is established here but is a restricted helper, **not** a solution or nomination. If a finite planar set X contains the four vertices P of a nondegenerate parallelogram and is not c.s.c., it has a non-c.s.c. subset of size at most 16. Affine invariance reduces P to the square above.

First prove that M_X restricted to either coordinate axis is a closed interval (possibly empty, a singleton, a ray, or the whole line).

Horizontal axis: let O=(t,0). If X contains a point above y=1, then t>0 makes (1,1) an interior point of the horizontal segment from (−1,1) to (2t+1,1), with points of conv(X∪(2O−X)) both above and below that segment. Hence (1,1) is strictly interior to the hull. For t<0 use (−1,1). A point below y=−1 gives the same argument with the lower edge. Thus in either case only t=0 can be admissible, so the restriction is empty or {0}.

Otherwise X lies in |y|≤1. All its points on y=±1 are automatically boundary points. If any other point p is interior to C=conv X, no center is admissible. For each remaining p with −1<p_y<1 its supporting normal cone

    N_p={n: n·p=h_C(n)}

has no nonzero normal with n_x=0. Its unit section is compact and connected, and n_x therefore has constant sign and is bounded away from zero on it. The point p stays exposed after reflection precisely when some n∈N_p satisfies

    n·p ≥ 2t n_x + h_C(−n).

For n_x>0 this is t≤max[n·p−h_C(−n)]/(2n_x); for n_x<0 it is t≥min of the same quotient. The extrema are attained. Thus each point gives a closed halfline, and intersecting them gives an interval. The same proof works for the vertical axis. Collinear points on a nonhorizontal hull edge have a normal ray and obey the same argument.

Now, for every triple T⊂X, set A_T=M_{P∪T}∩{y=0}. Every A_T is a closed interval by the preceding lemma. The source's triple criterion gives

    M_X∩{y=0}=intersection_T A_T.

If this intersection is empty, the finite one-dimensional Helly theorem supplies at most two triples T1,T2 witnessing emptiness. Retain their points and P, at most 10 points. Do the same for the vertical axis, obtaining at most two further triples. The union Y of P and these at most four triples has |Y|≤16 and M_Y empty on both axes. Since M_Y⊂M_P is contained in those axes, M_Y=empty. This proves the restricted assertion, including equality/boundary centers. No assumption that the intervals are bounded is needed because the family is finite.

This is a complete applicable classical bridge: the source's exact triangle criterion and parallelogram cross, the support-normal interval proof above, and finite interval Helly. The restricted theorem should be excluded from discovery credit as a routine restricted deduction. Generic “Helly applies” would not suffice without proving interval convexity; that missing step is supplied above.

## What is still missing

An arbitrary convex configuration need not contain a parallelogram. Adding one is unjustified: hereditary c.s.c. assumptions concern subsets of X, not supersets. Approximation by a curve does not preserve the premise either; the source's closed-curve theorem cannot simply be invoked. The exact missing universal statement is a cardinality-independent bound on minimal infeasible intersections of the triangle-center regions arising from **one common planar convex configuration**, without an anchored parallelogram. Equivalently, prove or disprove that minimal non-c.s.c. finite configurations have uniformly bounded size. This is still essentially the full finite source question, but the two-axis theorem isolates why a tempting classical bridge works in a substantial restricted case and fails to reach generality.

Decisive next calculation: construct minimal infeasible configurations with no parallelogram using the exact midparallel-line arrangement, record a center for every one-point deletion and a rigorous emptiness certificate for the full intersection; look for an unbounded construction, not just a larger isolated example. Alternatively prove a bounded branch certificate for the source's tallest-triangle arrangement. No arbitrary-size construction or universal branch lemma was obtained. No PROOF.md is warranted.

## Source comparisons retired before sustained investment

Gaussian entropic contraction: Aishwarya–Li2409.03664v3 Theorem1.5 (pp4–5) covers every dimension, every X and 1-Lipschitz T, s>0, α≥1 without moments; for 0≤α<1 it assumes E||X||²<∞. Their proof (§2–3) transports the continuity equation through Gaussian convolution, proves nonpositive divergence of the conditional velocity via monotonicity, obtains convex-integral majorization, and uses a doubled-space continuous contraction to handle arbitrary T. Thus the Gaussian Shannon subquestion of2210.12842v2 Question1 is fully public; the α<1 moment-free case is explicitly not asserted. r111 already excluded the entropy-power counterpart. Uniform-ball noise/all orders would imply geometric Kneser–Poulsen and is not claimed settled by the Gaussian theorem.

Alpan–Goncharov1612.00862v1 Problem7 forward direction is public Alpan1808.05936v2 Theorem1.3. For μ=hμ_K+μ_s and equal support capacity, Jensen and the equilibrium-potential inequality yield ||P_n||²≥exp(∫log h dμ_K)Cap(K)^(2n), uniformly in n. The actual2018 body only gives a *conditional* converse counterexample from the Cantor-measure conjecture; it must not be reported as unconditional. Separately, Alpan–Zinchenko2608.17321v1 Cor3.7 explicitly answers Problem8 for regular real compact sets: bounded Chebyshev or equilibrium-L² Widom factors iff Parreau–Widom. Its Thm3.5 proof uses Hankel/Vandermonde determinants, equilibrium quantile cells, Jensen and partition entropy to bound the Green-gap sum. These are side comparisons, not extra breadth counts.
