# Independent mathematical review of the compressed quantile certificate

2026-10-30 UTC. Solo, no children. **MATH PASS for the new continuous potential and new 20-bin coupling. SOURCE PASS at the confirmed accepted-manuscript scope. Substantive objection provisionally survives; novelty/investment HOLD remains.** No acceptance, count, Lean, manuscript or new novelty search. Baseline stays 9 additional / 39 total / next 40; root alone adjudicates.

The previous review's PASS for the old 200-bin witness was not used to certify these new data. `independent_exact.py` was written from the printed formulas and permutation. No candidate checker or discovery code was read, imported or run. Its full rational evidence is `exact-evidence.json`, including every polygon, every vertex slack, every source integration piece and every target integration piece. All arithmetic uses Python Fraction; no solver, float, tolerance, discretization allowance or optimality premise occurs.

## Literal marginals and source

Read the actual accepted manuscript body, regenerated locally from the frozen PDF: Chen–Liu–Liu–Wang, *Ordering and Inequalities for Mixtures on Risk Aggregation*, institutional accepted version, title date May 30, 2021, DOI 10.1111/mafi.12323. Relevant passages are aggregation sets and arbitrary dependence pp2–4, doubly stochastic matrices p5, inverse-CDF mixture p7, decreasing-density class p11, Conjecture 1/version (ii) and Example 3 pp25–26. The conjecture has no n>=3 restriction. The nearby n>=3 uniform result is a different statement. Inclusion is non-strict. No strict density decrease or smoothness is imposed. The actual accepted PDF, not its abstract, supports this review's source conclusion.

For u in [j/5,(j+1)/5], the slopes of q1 and q2 are respectively

    (1,13/10,11/5,14/5,29/10), (1/2,9/10,9/10,8/5,9/5).

Starting at zero, direct integration gives support partitions

    q1: 0,1/5,23/50,9/10,73/50,51/25;
    q2: 0,1/10,7/25,23/50,39/50,57/50.

The densities on successive image intervals are

    f1: 1,10/13,5/11,5/14,10/29;
    f2: 2,10/9,10/9,5/8,5/9.

Change of variables on each affine branch proves the pushforward identity for every Borel set, not just equality of bin masses. Every bin has mass 1/5. The displayed densities are positive, nonincreasing on their interval supports and total mass one. Right-hand internal values and the final left-limit value give a pointwise monotone representative on each support. Extension by zero outside is a density; monotonicity across the left support boundary is not required. The two repeated q2 slopes simply give an artificial subdivision, not a density defect. There are no atoms.

Each q is a continuous strictly increasing homeomorphism of its support. If X=q(U), then F(q(u))=u for 0<=u<=1 and the generalized inverse on (0,1) is q. Endpoint inverse conventions do not change laws. For r=(q1+q2)/2 the slopes are (3/4,11/10,31/20,11/5,47/20); r(1)=159/100. Hence G=r_*Leb has the literal quantile average r. The all-1/2 2-by-2 matrix is doubly stochastic and its quantile mixture is exactly (G,G). The source supports sum to [0,159/50], as do the possible target sums. With a=159/2000 these are [0,40a] and each target coordinate is in [0,20a].

## Complete global dual check

H has knots (0,4,10,20,24,38,40) and values (0,-4,2,-8,-4,-18,-16). Its successive slopes are (-1,1,-1,1,-1,1), so its constant extension is bounded continuous and 1-Lipschitz. In physical coordinates the interior knots are (159/500,159/200,159/100,477/250,3021/1000), and the terminal knot is 159/50. Removing the redundant same-slope knots from the old displayed payoff gives exactly h(x)=aH(x/a), including its signed values, not merely its Lipschitz constant.

D(t)=2-t+2(t-3)_+-2(t-7)_++2(t-17)_+ has four formulas

    2-t [0,3]; t-4 [3,7]; 10-t [7,17]; t-24 [17,20].

Endpoint values are (2,-1,3,-7,-4). There is no jump at a knot. We verify D(s)+D(t)-H(s+t)>=0 on the ENTIRE closed square [0,20]^2.

Partition the square into all 16 closed rectangles from endpoints 0,3,7,17,20. For every rectangle and every consecutive H-knot pair [k,l], intersect it with k<=s+t<=l by exact polygon clipping. These polygons cover the rectangle: every possible sum is in [0,40], which is the union of the closed H-intervals. On each nonempty polygon all three terms in the slack are affine. A nonempty compact convex polygon has its minimum at a vertex. A degenerate point or segment is equally covered by its endpoints. Thus vertex nonnegativity proves nonnegativity everywhere, including all boundary points.

No two distinct sum-break lines cross; they are parallel. Thus each vertex is a rectangle corner or one sum-break line meeting a rectangle edge. No sum-break line coincides with a horizontal or vertical rectangle edge. Intersections at a rectangle corner, shared edges, and zero-area intersections are retained, deduplicated only within the rectangle's vertex set. An independent construction of all edge/line intersections is asserted equal to the clipping vertex set for each rectangle. This also checks completeness in the coincident-intersection cases. The outer sum lines 0 and 40 can only touch the corresponding outer corners, already present. Symmetry exchanges (s,t), but is not needed for our computation: all 16 rectangles are checked.

For the ten rectangles i<=j in lexicographic order 11,12,13,14,22,23,24,33,34,44, the distinct vertex counts are exactly

    6,6,5,4,4,5,5,6,4,6,

summing to 51. Each rectangle's minimum exact slack is zero. Every individual slack (including positive and zero values) and its coordinates are in `exact-evidence.json`, under `rectangles[].vertex_slacks`; the full clipped polygons appear alongside. This is a finite proof for every point of the square, not a sampled quantile test.

## Target expectation from marginals alone

Let Z,W be ANY random variables with laws G; they may live on any probability space and have any dependence. Since their laws have support [0,20a], the global inequality implies h(Z+W)<=d(Z)+d(W) almost surely. The continuous functions are bounded on these compact sets, so expectations exist, and linearity plus pushforward integration gives

    E h(Z+W) <= E d(Z)+E d(W)
              = 2 integral d dG = 2 integral_0^1 aD(r(u)/a) du = B.

The last equality uses the definition G=r_*Leb, not a representation of the JOINT law by independent uniforms, nor recovery of uniforms by inverse CDFs. A definition of d on the real line, if desired, can extend it constantly outside its support; it changes no expectation.

Solving r(u)=3a,7a,17a gives the extra preimages exactly. On [1/5,2/5], r(u)=3/20+(11/10)(u-1/5), giving u=617/2200. On [2/5,3/5], r(u)=37/100+(31/20)(u-2/5), giving u=1613/3100. On [4/5,1], r(u)=28/25+(47/20)(u-4/5), giving u=4223/4700. No other roots occur since r is strictly increasing. Together with the fifths these make eight affine pieces. Exact trapezoidal integration on each produces

    B = -83231059/641080000.

The checker derives these roots rather than assuming them and stores all eight exact contributions.

## New source coupling and all exact integrals

Use ([0,1),Borel,Lebesgue probability) and U(u)=u. The printed list

    p=(17,16,15,14,13,11,10,9,7,5,3,1,0,18,19,12,8,6,4,2)

contains every integer 0 through 19 exactly once. On bin Ii=[i/20,(i+1)/20) let T(u)=u+(p_i-i)/20. Translation sends Ii bijectively to I_(p_i). For any Borel E,

    Leb(T^-1 E)=sum_i Leb((E intersect I_(p_i))-(p_i-i)/20)
               =sum_j Leb(E intersect Ij)=Leb(E).

Thus T is measurable and measure-preserving. It need not be increasing or continuous at bin boundaries. V=T(U) is uniform; (q1(U),q2(V)) has exactly the prescribed source marginals. Consequently J=(q1+q2 o T)_*Leb genuinely belongs to D2(F1,F2). A value at 1, if using [0,1], is immaterial.

Every fifth is a twentieth-bin boundary. Translating a fifth-break back by a multiple of 1/20 also gives a twentieth-bin boundary. Therefore f(u)=q1(u)+q2(T(u)) is strictly increasing affine within each bin. The checker nonetheless inserts all possible q-break preimages first. It then solves f(u)=ak for every interior H knot k=4,10,20,24,38, inserting roots strictly inside each current affine branch; roots at endpoints already occur in the partition. Between consecutive roots h(f(u)) is affine. There are exactly 31 nonempty pieces in all. On a bin's upper endpoint integration uses the same affine translation's left limit; another bin's definition at the endpoint does not affect the integral.

Every printed bin integral agrees independently, in order:

    7/10000,27/10000,89/20000,2969/520000,6997/1160000,
    99/20000,2573/440000,2813/440000,7253/1240000,7453/1240000,
    6461/1080000,143/40000,-57/40000,-21/800,-151/4000,
    -5149/275000,-37387/1900000,-69769/3800000,-35407/1900000,-11/500.

For each of the 31 pieces the evidence records both endpoints, both sum values, both payoff values and its exact trapezoidal integral (length times endpoint-payoff average). These are actual interval integrals, not conditional averages. They sum to

    A = E_J h = -68997954679/659497410000,
    A-B = 100817889097/3999532680000 > 0.

All rounding allowances are zero. Equal probability laws have equal integrals of a bounded Borel function. Hence J cannot belong to D2(G,G), since every such law has h-expectation at most B<A. This is a literal refutation of accepted Conjecture 1 and its version (ii), with n=2. These source quantiles are not common-scale copies: the first-slope ratio is 2, the second 13/9, so no constant scaling works (nor a location-scale relation since both start at zero). No failure of versions (i)/(iii) follows.

## Substantive objection and retained holds

The new certificate materially removes mathematical audit obstacles: it supplies a global continuous dual, 51 small exact substitutions, a 20-entry coupling, and exact continuous integration. It does not change the strongest substantive question: whether an earlier exact same-inclusion refutation or a complete classical adaptation already supplies this in-class excluded law. Standard weak duality is the mechanism, not by itself such a prior resolution. Shortness alone is not an exclusion criterion. The earlier source atomic example does not itself give decreasing-density marginals; the prior review's nonincreasing-density average-mass obstruction explains why automatic smoothing of its two separated atoms is invalid. No new smoothing/subsumption search was performed here.

Actual accepted source Theorem 1's proof produces CDF mixtures using Birkhoff permutations; it does not turn these into averaged inverse CDFs. The accepted Example 3 explicitly concerns preservation of existence of a constant sum via the mean-length criterion, not this nonconstant J. Other previously reviewed envelope/VaR results concern separate scalar objectives. The new continuous certificate strengthens the explicit witness, but does not create source-version equality, independent priority evidence, or a novelty upgrade. The preliminary internal compression checker was never external review; this lane supplies the independent mathematical reconstruction.

The unread 2016 *Joint Mixability* original proof, exact final typeset version comparison, current proof-registry heads/bodies and parked historical intervals retain their previously documented limitations. They were not reprobed. Existing original-proof and registry/history HOLD remains; any future investment/acceptance needs root's disposition and remaining campaign gates. No statement that the 2016 proof cannot contain a subsuming bridge is justified here.

## Smaller literal formal obligations, future use only

1. Define the explicit continuous piecewise affine q1,q2 and their Lebesgue pushforwards. Prove the displayed reciprocal densities, their monotonicity on supports, unit mass and atomlessness by branchwise affine change of variables.
2. Prove the inverse-CDF identities on (0,1), including r as the arithmetic quantile average, and identify the literal all-1/2 quantile mixture as (G,G). Endpoint conventions may be handled as null sets, not left as inverse-CDF assumptions.
3. Define the explicit 20-bin translation T, prove the displayed permutation bijective and T measure-preserving for Borel sets, and obtain J in the actual source aggregation set.
4. Define bounded continuous h and support-bounded d. Prove the closed-polygon covering and affine-minimum argument (or an equivalent direct piecewise affine proof), then the finite exact nonnegative vertex slacks, yielding the global dual inequality on the whole closed square.
5. Prove bounded integrability, pushforward integration and marginal linearity for arbitrary target couplings. Prove the eight target and 31 source branch integrals and rational positive gap. Conclude J outside D2(G,G) by equality-in-law invariance of bounded expectations, and negate the literal Conjecture 1/version (ii).

There is no target inverse-uniform recovery obligation, midpoint Lipschitz error estimate, optimizer correctness obligation or 40000-entry finite bridge in this smaller route. A formal endpoint conditional on the global inequality, densities, quantile identity, measure preservation or computed expectations would still be incomplete. Python PASS is evidence for ordinary mathematics, not a kernel proof. No formalization was started.
