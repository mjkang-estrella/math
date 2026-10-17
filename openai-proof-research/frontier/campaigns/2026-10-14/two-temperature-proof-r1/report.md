# Independent proof review R2T, round 1

**Verdict: PASS_FULL_R2T.** The unchanged candidate proves the complete frozen target, conditional on the stipulated pinned source framework. No repair, narrower hypothesis, modified potential class, or reduced density/temperature quantifier is needed. This is a mathematical reading review, not formal verification, a contribution verdict, or acceptance authorization. Campaign count is unchanged.

Original review prose CC BY4.0. Reviewer acts for the research campaign of Myeongjin Kang, no affiliation. Third-party source rights are retained.

## Object and scope

Reviewed candidate SHA256 `7392c10ee88ba844ae2115cb48bbeff0ba8aaf40641bae42b818825d12778230`; frozen scope SHA256 `e595c73286a91733d95e3dc46800e1e51ed0af8d290490ffb93058815c5f79c2`; author seal SHA256 `a30af383bfa83f5855d1bb83acc981ae9b6308af37a715dc71c3c8294d6f8144`. The full 56-file payload, exact directory membership and source identities were checked independently. No author code was executed. The complete candidate, scope, reading contract and both checkpoints were read. The old analytic brief's first 100 lines were read for original assignment/exclusions; no claim of reading its full historical appendices is made.

The conclusion is one bounded continuous radial pair potential, stable for every finite configuration including coincidences, with tail bounded by C r^(-3-1/32); finite free-cube canonical limits for every positive beta and density; and two fixed inverse temperatures in the prescribed open windows, each giving a strict finite one-sided beta derivative jump at every density in the same open interval centered at 2p. The argument proves all of this with one fixed microscopic parameter and one attraction schedule. It does not merely establish an ideal pressure diagram, different potentials, different density intervals, or distinct-density coexistence.

## Reading and dependency contract

All seven bounded-core section files were read in full, including the proofs: foundations, local_bounds, transform, range, initial, iteration and introduction. The companion divergent-core introduction was read in full, including its theorem and four-step construction. It supplies no premise here. Other companion files were authenticated, not relied upon or claimed read. Git blob identities were independently compared with the complete preprints-tree.json; pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Exact identities and extents are in input-receipt.json.

The principal upstream interfaces are f:packing; f:stability and canonical-bounds; f:grand-tail and thermodynamics; f:moments, perturbation and tail-pressure; k:transform-properties, active-parabola and subdifferential; k:range and its box-pressure/kernel-rows lemmas; i:bare-pressure and initial-separation as proof patterns; m:one-step, pressure-ball and canonical-corner. Their truth is stipulated. The audit below checks that changing the core does not silently apply a theorem outside its proved interface, and independently verifies the new microscopic and two-neighborhood deductions. No outside literature theorem is required for this proof verdict. Literature priority/substantiality belongs to the separate contribution review.

## 1. Geometry and stability

For a good-pair clique, the inner relation is genuinely transitive: if x-y and y-z are inner edges and x differs from z, then |x-z| is below ell, and goodness forces it into the inner shell. This also rules out coincident distinct labels. Five points in a single narrow shell contradict the rank bound for four difference vectors in R3. With squared-distance error epsilon=2Delta+Delta², each Gram entry differs by at most epsilon, so its operator error is at most 4epsilon<1/2. Thus each inner class has at most four labels. Any choice of one representative per class has all distances in the outer shell, so at most four classes occur. The bound 16 holds for every clique of the arbitrary configuration's good-pair graph, not merely for already-free configurations.

In a free configuration, every length-two path of distance-below-one edges closes, by 2(1+Delta)ell<1. Each component is therefore such a clique. Distinct components have distance at least one, so their representatives satisfy the packing bound M_L.

The weighted clique argument gives at most 15m²/32 good pairs. In a cell of diameter below one, at least m²/32-m/2 pairs consequently have energy exactly t². Summing proves the new D0=t²/32 and B0=t²/2 bound, including coincident configurations. The attraction row estimate is independent of shell geometry. D0>=8M0 implies a coefficient greater than t²/64; at most 216 L³ cells give c=1/13824. Both size constraints on t are compatible with eventual enlargement of t. No fixed finite t is required to work uniformly in the construction limit t→infinity.

## 2. Framework transfer

The full foundations proof uses only bounded nonnegative core, supremum t², support within two, the displayed cell coercivity, and the nonpositivity of interactions across boxes separated by two. These all hold. The canonical lower estimate changes c; the Jensen upper estimate is unchanged. The grand tail remains coercive for the entire auxiliary mass interval. The integer box-count adjustment proves the limit along every sequence of real side lengths and integer counts, including floor(rho L³). Convexity/continuity in density and concavity in beta transfer with the same argument. No finite-range assertion is imposed on the eventual potential.

The conditional occupation proof retains complete intra-cell core under exactly the deletions needed in the range estimate. Its conditional energy lower bound has the new D0, same B0 and same attraction row bound. Finiteness of each exponential moment precedes maximizing over cells. The closure exponent is 4M0²/D0²<=1/16. Thus constants remain uniform over ranges, cropped cells, finite regions and permitted interpolations, while being allowed to depend on the fixed t. Differentiation and tail-mass pressure continuity follow with these constants.

The ideal transform uses the transferred density duality and coercivity. Its active shifts are precisely maximizing densities, with a bound uniform also for all sufficiently large t. The exact source subdifferential formula is applicable because active shifts are compact for each positive a and shifted parameter sets remain in fixed compacts. The formula uses actual supports, not heuristic phase gradients.

For the range estimate, deleting reference inter-box interactions preserves complete intra-small-cell core. The signed deletion cost is bounded by the absolute core-plus-attraction majorant; only support and supremum of the core enter. The reference boundary strip contributes O(R0/z); kernel row errors contribute O(z/R). The upper grand-count cutoff remains uniform in the modified family. The lower independent-box Jensen argument uses the exact square completion in the candidate and never requires convergence of a finite-box mean density to an active shift. Consequently the source proof supplies the claimed O(sqrt(R0/R)) rate with constants independent of earlier ranges and of small positive added mass. There is no hidden one-shell hypothesis left in this transfer.

## 3. All component types and pressure convergence

For a component with k inner classes and M particles, choose class roots and a whole root. The transformation to root positions and relative displacements is triangular with Jacobian one. The k-1 non-whole class roots have O(ell³) integration volumes; the M-k other labels have O(s³) volumes. The overcount of possible partitions/root assignments is bounded by constants because M<=16. Splitting labels into unordered components cancels N! and leaves K!, with finite type factors. Dropping restrictions only increases the integral, while retaining K<=M_L is valid.

All intermediate components are included: k<=M<=4k and 1<=k<=4. For fixed k the exponent is affine in M, hence maximized at M=k for h<=18 and at M=4k for h>=18. Each endpoint expression is affine in k. The resulting four possible lines are h, 4h-9, 4h-54, 16h-225, with the third everywhere dominated by the second. Thus no mixed class size can add a missing dominant branch.

The removed-label set comprises every label incident to a bad pair. At least |J|/2 bad pairs exist and each costs t². Removing J leaves a free configuration, and all discarded remaining core energy is nonnegative. Summing all label subsets yields exactly the exponential prefactor stated, by binomial/factorial cancellation. Shell endpoints and distance exactly one do not invalidate this upper bound.

The lower realization of 16 particles is geometrically feasible. Outer roots form a tetrahedron at the middle of the outer plateau. Each class is an inner tetrahedron. A cross-class displacement differs from its outer-root displacement by O(s), uniformly over the finite number of edges; since s/ell→0, all those edges remain inside the plateau after fixing small relative balls. The twelve inner offsets and three outer offsets give ell^9 s^36=exp(-225t). The single and outer-tetrahedron motifs give exponents 0 and 9. Root balls about distinguishable separated centers and deterministic internal label order make the factorial lower bound disjoint and valid.

For rigor in the short limit-order sentence, use the explicit construction already invoked from source initial.tex: for any desired uniform error on a parameter compact, fix packing-period and dilation parameters with center density sufficiently near p, then fix t sufficiently large for the plateau, separation and entropy errors; take the volume limit at each such t. This is exactly the candidate's source-based lower-bound argument, not a new hypothesis or missing mathematical operation. It gives locally uniform convergence together with the explicit upper bound.

## 4. Both slope triples

Direct exact arithmetic confirms all four affine planes, the two parameters (1,-3/4) and (21/16,-27/16), inactive values -45p and -45p/64, and both stated positive barycentric representations at density 2p. See exact-checks.json. These finite checks supplement the analytic argument rather than proving a continuum transition.

The inactive plane is strictly separated on small closed neighborhoods inside the required open beta windows. At an active finite-t shift, comparison of the limiting objective with its maximum excludes that plane and localizes the shift near one of the three remaining densities. Fixed beta secants bound the first coordinate of each underlying support because the limiting bare pressure is beta-independent. The exact transform hull formula then gives (4.1) for actual generating supports. Uniformity over the two compact neighborhoods permits the same single finite t.

For either triangle, the chosen g is strictly interior, so its support-function margin eta0 and distance from every edge are positive. Perturbing each vertex by tau loses at most tau in support functions. The exclusion of the hull of any two balls follows from distance to the corresponding segment. Hence the common ball radius gamma=eta0/2 is valid for either triangle. The growth inequality is valid globally because the maximum of all four planes dominates the active triple's maximum.

## 5. Persistence, limit and quantifiers

The one-step density-band estimate uses P's Lipschitz bound at y and x and q's active parabola at x. The band has radius below p/8. Since generating group centers differ in density by at least p and r<tau<p/16, at most one group is possible throughout the entire la neighborhood; nonempty subdifferentials and the hull assumption guarantee one exists. Convexity of that ball contains all supports of P there. Endpoint supports bound P(y)-P(x), giving the 2delta/(la) transfer for every direction. The transform support displacement is at most aU_*²/2. Thus (5.1) holds for either neighborhood with common constants.

With R_(n+1)=R_n², delta_n=O(R_n^-1/4) and a_(n+1)=R_n^-1/8, every prescribed domain, slope, density-band and pressure-error loss is summable and made small by enlarging R1 once. The references are physical family members. The pressure telescoping uses the small-mass transform bound at the same parameter, so does not demand approximation estimates at cumulatively drifting shifted parameters.

Minimizing P_n-g_i·lambda inside each fixed half-radius ball gives an interior minimizer: the boundary growth eta0 rho/2 exceeds twice the uniform error eta0 rho/8. Its subdifferential contains g_i; the two-group exclusion forces all three groups to occur. Choosing one actual support per group yields the entire common support ball, not just three near-slopes at different points.

One subsequence in the compact product of the two parameter balls gives both limiting parameter points for the same infinite potential. Tail-mass continuity and range errors identify the limit pressure with that potential. Passing every support inequality to the limit and extending a local support globally proves both full support-ball inclusions. The limit beta values remain strictly inside the original disjoint windows because the closed neighborhoods were chosen there.

Uniform convergence of the potential series yields boundedness/continuity; the cell estimate yields all-configuration stability. The summable weighted masses a_n R_n^(1/32) give the pointwise required tail, including the compact core contribution. The thermodynamic proof already covers the infinite sum for all positive beta and density.

Finally eta=min(gamma/2,p) is positive and less than 2p. For every rho in the same resulting interval, both slope balls contain the stated two energy coordinates at that rho. Partial duality gives both upper supporting lines for the finite concave canonical H. Its finite one-sided derivatives at each interior beta are ordered with gap at least gamma. The factor t/beta changes that gap to at least t gamma/beta, since the derivative contribution of 1/beta cancels by continuity. Neither potential nor temperatures are selected anew for rho. This proves the full universal-density conclusion at two fixed temperatures.

## Disposition

No fatal, repairable, or unresolved mathematical objection found in this first independent proof review. No candidate edit is requested. Contribution, manuscript, formalization and acceptance gates remain separate and unawarded here. The proof PASS is conditional only on the campaign's stipulated pinned-source truth, not on empirical diagnostics or an unproved new lemma.
