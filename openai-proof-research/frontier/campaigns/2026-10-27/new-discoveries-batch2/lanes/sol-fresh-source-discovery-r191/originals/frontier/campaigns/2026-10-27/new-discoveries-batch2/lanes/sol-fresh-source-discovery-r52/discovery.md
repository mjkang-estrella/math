# r52 — global unimodular-fiber Jensen, unresolved

Credit 0. No completed source proof/refutation, nomination, Lean or paper. Root owns every acceptance gate. Campaign observed 6 additional / 36 total, unchanged.

## Source and selection

One primary open-question paper screened: Jonathan Leake–Maryam Mohammadi Yekta, *Log-concavity and Approximate Counting for Totally Unimodular Polytopes*, arXiv:2609.39917v1, 30 September 2026. Current abstract history fetched 29 October 2026 15:12 UTC lists v1 only. Actual HTML Question 1.7, definitions preceding §3, and Theorem 3.1/Lemmas 3.2–3.4/proof read before diagnostics. Exact source bytes and URLs are in http.jsonl. No journal version asserted.

Literal question: for every integer unimodular M of size m by n and every probability distribution μ on Z^m with integral mean b, does

    N_M(b) >= product_a N_M(a)^(μ(a)),
    N_M(a) = #{y in Z^n_{>=0}: My=a}

hold? The source explicitly permits, but does not require, finite support. Its definition of unimodular is that every nonsingular rank(M)-square submatrix has determinant ±1. This is not merely det(M)=±1 for square M. Theorem 1.4 expressly assumes finite fibers; Question 1.7 does not restate all infinity/zero conventions. Our work stays in the substantive finite, positive-fiber regime, without proposing a wording correction or claiming that regime solves the entire literal question. A genuine counterexample there would refute the literal assertion.

For a finite rational distribution with weights k_i/K, the exact target is

    N(b)^K >= product_i N(a_i)^k_i,  sum_i k_i a_i = K b.

All m,n,K, all unimodular matrices and all such demand families are required; none are bounded by this lane's checks. The source's midpoint theorem proves only K=2 with integral midpoint. The selected question is independent of the credited/excluded campaign families. r1–51 handbacks, ledger, prior context and selective NEXT were read; context-screen.json preserves file hashes.

## Current closest bodies and eligibility limits

The latest public edition located of Scott Schubr, *Power Concavity of Low-Dimensional Unimodular Fiber Counts*, edition 4, 27 October 2026, has PDF SHA256 fefc3ad35c98e327cdabdf01b147393f561ba7d149f84c61c60f0e9304d11d9f. Actual pp1–4 and §3 pp8–10 theorem/proof bodies were extracted and read. Theorem 1.1 claims global logarithmic Jensen, even countable support, whenever the bounded central fiber's affine dimension is at most THREE. Theorem 1.4 separately treats the complete four-vertex DAG. Those scopes are prior/public, excluded from nomination; this lane does not audit that manuscript's full proof or inherit its claims as newly established results. Its rank-three normal classification and type-A3 chamber machinery do not state the arbitrary-dimension source question. The graph's vertex count is not the fiber dimension. Our K4 capacity diagnostic has dimension3 and receives no credit.

Actual Csikvári–Imolay arXiv:1905.06678v2 §5 proof of Theorem 1.11 was read. It decomposes a pair of orientations according to agreement edges and compares to the Eulerian central orientation count. This is the exact pair-count antecedent acknowledged by the source; it supplies no demonstrated arbitrary-marginal multicolor comparison here. It is not claimed globally inadequate by literature absence.

Current OpenAI matching FPRAS manuscript introduction/theorem was fetched at immutable head and read: its endpoint is a polynomial-time randomized relative counting approximation for cell-bounded contingency tables. This actual theorem does not state exact global Jensen. Its proof body was not fully audited. No blanket claim about every OpenAI paper is made.

No prior full resolution located in this bounded screen; no novelty PASS, worldwide priority or exhaustive citing-literature claim. Barvinok2007 and the source's 2026 Verma-module companion are named but not body-read here. This is a retained literature gap, not clearance.

## Route A: supporting hyperplanes and the parity obstruction

Write f(a)=log N(a) on feasible finite positive fibers. A sufficient full-domain result is: at every integral feasible b there exists a vector p such that

    f(a) <= f(b)+p dot(a-b)  for EVERY feasible integral a.       (H)

Multiplying by μ and summing proves finite-support Jensen, since the linear term vanishes. For integrable countable support it also proves the result whenever f is integrable (see the bound below). Conversely for a FIXED FINITE test set S containing b, existence of such p on S is equivalent to every distribution supported on S with mean b obeying Jensen. Indeed this is the finite linear-program dual of maximizing sum μ(a)f(a) subject to sum μ=1, sum μa=b, μ>=0. The point mass at b is feasible, so equality to f(b) is precisely the dual majorant at b. Finite-set duality is only a reduction; the all-demand supporting vector is NOT constructed.

Midpoint inequalities cannot produce (H) for arbitrary lattice functions: let

    S={(0,0),(1,2),(2,1),(1,1)};
    N=2 at the first three points, N(1,1)=1.

This S is saturated: triangle area3/2, three primitive boundary edges, hence precisely one interior lattice point by Pick, namely (1,1). All four points have different mod2 classes. Thus any two distinct support points have nonintegral midpoint; all applicable midpoint inequalities hold, including zero extension outside S (a midpoint of two support points can never be an integer outside S). But equal weights on the three vertices have mean(1,1), and 1<2. All integer line sections have at most two consecutive lattice points. This is NOT a unimodular-fiber example. It explains why an unspecified 'iterate the source theorem' is a gap rather than a proof.

Integrability is manageable, not the main obstacle. If any nonempty fiber is bounded, ker M has no nonzero nonnegative vector. On {x>=0: ||x||_1=1}, ||Mx|| has a positive minimum η, so every feasible x obeys ||x||_1 <= ||Mx||/η. Consequently

    N(a) <= (1+||a||/η)^n.

Thus log N(A) is integrable for integrable feasible A. This is the same recession/compactness mechanism explicitly used in the closest manuscript's §3, and receives no originality claim. The remaining gap is (H), not this tail bound.

## Route B: multicolor coefficient comparison, exact obstruction at dimension4

For finite box fibers define F_a(w)=sum_{My=a,0<=y<=c} w^y. A considerably stronger potential theorem is

    [w^alpha] F_b(w)^K >= [w^alpha] product_i F_(a_i)(w)
    whenever sum_i a_i=K b, for every alpha.                 (C)

It would imply the equal-weight box inequality by evaluating w=1. Rational weights are repeated demands. For a finite collection of bounded nonnegative fibers one can choose a common box containing every fiber, so (C) for every box would settle all finite rational cases. Arbitrary real finite weights follow by rational approximation in the rational polytope of weights with fixed integral barycenter: its rational points are dense, and each N(a)>0 is fixed. This still leaves the proof of (C), and infinite-support handling; neither is asserted complete.

The source's K=2 coefficient proof identifies the coefficient fiber with one centrally symmetric box section, where its integrality and Lemma3.3 apply. At K=3 the natural constraint is

    My^(1)=My^(2)=My^(3)=b,  sum_c y^(c)=alpha.

The enlarged matrix need not be TU even for a TU original matrix. Here is an ordinary exact example, not merely floating-point evidence.

Let B be a reduced oriented incidence matrix of K3,3, with every edge directed from a left vertex to a right vertex. It is 5 by9 and TU. Put

    M = [ B  0 ; I9 I9 ].

This 14 by18 matrix is TU: in any square minor expand along selected slack-column entries; remaining I-row entries can be expanded until a minor of B remains. Its demands (d,ones9) describe exactly 3 by3 arrays x with margins d and 0<=x<=1, with slack s=1-x. With all row and column sums1 the central fiber is the Birkhoff3 polytope and has affine dimension 9-5=4 and exactly6 integer points. Thus this is just beyond the public dimension<=3 scope.

For three copies and fixed total sum x^(1)+x^(2)+x^(3)=ones9, the variables form a nonnegative 3 by3 by3 array whose every axis line sums to1. Here are its three color slices, EACH divided by2:

    [2 0 0]    [0 1 1]    [0 1 1]
    [0 1 1]    [1 1 0]    [1 0 1]
    [0 1 1]    [1 0 1]    [1 1 0].

All line sums are1; there are seventeen positive entries. This point is a fractional vertex. To prove extremality, take any line-sum-zero perturbation supported on these entries. The first slice has its isolated(1,1) perturbation0, and its bottom2-square is [[t,-t],[-t,t]]. The second slice necessarily has form

    [0 b -b; b -b 0; -b 0 b],

and the third has form

    [0 -f f; f 0 -f; -f f 0]

by row/column zero sums. Summing colors at cell(1,2) gives f=b; at cell(2,2) gives t=b; at cell(2,3) gives t=-f. Hence b=f=t=0. Thus there is no nonzero supported perturbation. A feasible point with this property is a vertex: a nontrivial convex decomposition would have both endpoints zero at all zero entries and its difference would be such a perturbation. Since this vertex is fractional but the line-sum RHS is integral, that multicolor constraint matrix cannot be TU.

Adding the original slack variables does not change this conclusion: each is determined by s=1-x and total slack=2. This is a genuine failure of the proposed multicolor-integrality bridge applied to a legitimate dimension4 source system, NOT a source counterexample. The ordinary proof is independent of the diagnostic rank calculation.

Strongest objection to drawing any stronger conclusion: the central INTEGER coefficient in this very example is12 (the Latin squares of order3). It is in fact the maximum among all color-marginal coefficients with that edge total, as the small exact diagnostic confirms. Fractional vertices do NOT refute central coefficient maximality, let alone the weaker source cardinality Jensen. A comparison argument tolerating these fractional vertices remains possible. No helper or method obstruction is nominated for credit.

## Route C: directed network finite diagnostics

check.py uses coefficient dynamic programming for complete acyclic graphs on4/5 vertices with uniform edge capacities2 and1/2/3 respectively. For the reduced directed incidence B, its table D records N(d)=#{0<=x<=c:Bx=d}. These are honest source fibers through the same slack construction M above. At each feasible d it checks prescribed triangles d+u,d+v,d-u-v, where u,v range over the elementary type-A root directions; all sums have mean d. Arithmetic is exact integers. It does not optimize over all triples or distributions, all graphs, capacities or matrices.

Four finite tables:201/291/3081/13531 feasible demands, and9912/21960/538680/3043080 feasible directed triangles, all passing N(d)^3 >= product N(endpoint). No source counterexample. This compressed DP is a deliberately bounded diagnostic on fixed networks, not expansion into all flow tuples or a proof by absence. K4 is a prior low-dimensional control, not a candidate.

multicolor.py independently enumerates3^9 edge colorings (19683), finds central/max coefficient12, verifies every line sum of the fractional array, and computes rational support-constraint rank17. These checks corroborate, but do not replace, the ordinary fractional-vertex proof.

## Registry refresh and access

Before diagnostic investment, all five heads refreshed at15:12UTC. Omega dev now b386687d1b21d80059f9b18b696db3503dbfa340; exact comparison from user baseline e1d4e12f… reports2 commits and one documentation file. Patch beginning/end read (middle not exhaustively audited): source-response normalization/conductor geometry, not this lattice-count Jensen question. Named D5(12552) and Problems(1551) complete cached scopes unchanged; inherited files' SHA256 checked. Four other heads unchanged. registry-screen.json gives exact scopes, hashes and lineage. No whole-dev semantic absence assertion. Filename matches for unrelated unimodular approximation/monomial/Fourier lemmas do not establish novelty or subsumption. Current complete OpenAI preprints scope has the matching counting-algorithm family whose actual theorem was checked above.

All direct HTTP fetches returned200; no403/429 or blocking challenge encountered. The closest archive's normal page includes a Cloudflare script, but both public HTML and its directly linked PDF were served200; no script execution, browser, alternate-access workaround, account or bypass used. Search snippets were lead discovery only; actual source bodies are archived. No direct MathDB query or inference from an open label.

## Remaining gap and strongest falsifier

There is no full proof of Question1.7 and no literal source counterexample. The promising concrete route is an all-dimensional multicolor central-marginal comparison or a supporting-affine-majorant construction for log N; neither follows from source midpoint integrality. The explicit dimension4 fractional vertex defeats the simplest TU-transfer argument. A real falsifier would be an actual unimodular M and finite positive-fiber demands/weights with N(b)^K strictly smaller than the endpoint product, certified under the original finite hypotheses. No such witness was found. More blind enumeration is not justified by the present mechanism.

No PROOF.md: complete proofs here concern auxiliary reductions/obstructions only. No Lean/paper or acceptance request. No independent review, eligibility or novelty PASS. All writes only r52; no git, children, external messages, posting, uploads, accounts or browser tabs.
