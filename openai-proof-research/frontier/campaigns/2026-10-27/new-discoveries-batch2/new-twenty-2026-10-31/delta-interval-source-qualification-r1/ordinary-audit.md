# Ordinary audit: MathDB 377613

Decision: PARK. Neither the full conjunction of the Delta_3 and Delta_4 formulas nor a counterexample has been proved. No execution task is justified. The following are ordinary deductions, not formal certificates.

## Definitions and endpoints

Original equations (2),(3), section 7.2 and Lemma 7.6 define D(E) as the supremum of measures of symmetric subsets, symmetry being E'=2c-E'. The largest subset at fixed c is E intersect (2c-E), so D(E)=max_{s in [0,2]} integral 1_E(u)1_E(s-u)du for finite interval unions, with s=2c. Delta_k is the supremum of universally forced measures, equivalently the infimum of D over k-interval sets of measure epsilon. A maximal symmetric set can be trimmed symmetrically to any smaller measure by selecting pairs, which supplies the equivalence of these two formulations.

Use 0<=x1<=...<=x_(2k)<=1 and intervals (x_(2i-1),x_(2i)). Their interiors are disjoint; pairwise endpoints and touching boundaries have measure zero. The measure is sum_i (b_i-a_i). Reflection and translation preserve D; positive dilation multiplies both measure and D by the scale. There is no modular wrap-around.

“At most k” and the source's “union of k intervals” have the same infimum for epsilon>0: pad with empty intervals in the closed endpoint model; conversely split positive intervals at finitely many interior points to get exactly k disjoint open intervals. Splitting changes only a finite set, hence D is unchanged. If a stricter convention requires positive gaps/components, for 0<epsilon<1 perturb endpoints into the relative interior of the ordered-endpoint measure slice. Such a point exists by allocating positive lengths epsilon/k and positive gaps from 1-epsilon. Convex interpolation preserves measure and converges to the original endpoints. Since |D(E)-D(F)|<=2 measure(E symmetric-difference F) and that measure is at most the sum of endpoint displacements, the infimum is unchanged. At epsilon=0 the positive-interval family is empty; the conjecture uses the continuous/empty-set extension 0. At epsilon=1 the partition by removed points represents a full-measure k-interval set; requiring positive gaps there would be inappropriate. Do not encode an infimum of an empty family as 0 without this explicit convention.

The closed endpoint slice is compact and nonempty for every epsilon in [0,1]. D is continuous by the preceding bound; a minimum exists there. Exact endpoint and measure-zero bridges must accompany any formal endpoint.

## Overlap and branches

For I_i=(a_i,b_i), define
h_ij(s)=max(0,min(b_i,s-a_j)-max(a_i,s-b_j)).
Then F(s)=sum over ORDERED i,j h_ij(s); D=max F. No extra factor of two belongs outside this sum. Off-diagonal terms appear twice. This is the source's displayed formula after a translation in the integration variable, not a different objective.

For fixed endpoints every summand has breakpoints among a_i+a_j, a_i+b_j, b_i+a_j, b_i+b_j. Consequently a maximum is attained at one of S={x_p+x_q:1<=p<=q<=2k}, including plateaux and the identically zero case. There are at most 21 candidates for k=3 and 36 for k=4, not just sums with p<q. Doubled endpoints are essential.

A COMPLETE weak order of S ALREADY fixes every branch, including evaluation at s=x_p+x_q. In detail, min chooses b_i versus s-a_j by comparing s with b_i+a_j; max chooses a_i versus s-b_j by comparing s with a_i+b_j. The four possible selected differences are b_i-a_i, b_j-a_j, b_i+b_j-s, and s-a_i-a_j. Their positivity is either endpoint ordering or comparison of s with another member of S. Thus no new independent hyperplanes are needed. The apparent four-endpoint comparisons are precisely (x_p+x_q)-(x_r+x_t). r265's added branch-comparison instruction is safe but redundant if its pair-sum order is complete. Ordering only interval-center sums, or only distinct endpoints without doubles, would be insufficient.

Closed chambers with adjacent ordered-sum inequalities cover ties/faces. At a tie either branch has the same value, so linear formulas agree on the face. Include zero lengths, touching intervals, tied sums and boundary epsilon. Full-dimensional strict chambers alone without their closures do not cover the domain.

## Verified partial work and its source bridge

If lengths are sorted l1>=l2>=..., a self reflection gives D>=l1. Reflection exchanging the centers of the two longest intervals contributes 2*l2; these two contributions lie in disjoint intervals. Thus epsilon<=D+(k-1)D/2 and D>=2epsilon/(k+1). For k=1 use D=epsilon separately.

The r265 set E_t=(0,t) union (2t,3t) union (5t,7t) has measure 4t and D=2t for 0<=t<=1/7. The reported support/edge argument is correct (a smaller-pair/self overlap can also be read directly from Lemma 7.6). But it is explicitly source-derived: Table 3 prints the B*[2] witness S={1,2,5,7} in [1,7]. Proposition 5.1's interval conversion gives (0,t) union (t,2t) union (4t,5t) union (6t,7t). Merge the touching first two intervals modulo one point, and reflect about 7t/2. The result is E_t modulo finitely many points. Proposition 5.1 gives the upper bound and the length argument gives equality. This is a complete routine bridge for the INITIAL segment, not for the full conjecture. It carries zero new credit.

The source also gives the terminal line for every k>=2 on [3/4,1]. Neither this nor the unrestricted Delta tail beginning at 11/16 supplies the fixed-k conjectured earlier terminal ranges. The continuous limit of Lemma 6.10 contains a half-density alternating block; treating it as a fixed four-interval indicator would be an invalid bridge.

## All-parameter lower and upper obligations

Write P_k for the printed polygon. Delta_3's four successive slopes are 1/2,6/5,5/6,2. Delta_4's six slopes are 2/5,10/13,4/9,8/9,10/9,2. Slopes decrease internally: the polygons are not convex. Taking the maximum of ALL extended segment lines is WRONG. Work on each closed epsilon slab separately, with its own affine line.

On a chamber the exact constraints are endpoint order/bounds, sum lengths=epsilon, its sum-order inequalities, the epsilon slab, and d>=F(s) at each candidate sum, where the branch-fixed F is affine. To prove the slab lower bound d>=a epsilon+b, give nonnegative rational multipliers of inequality rows, unrestricted multipliers of equality rows, and check exact coefficient and constant identities. An alternative exact Farkas certificate excludes d<a epsilon+b. Infeasible chamber-slab pairs need an infeasibility certificate; silently skipping them is not a cover. A dual certificate at isolated epsilon values does not prove a slab. A proof of lower bounds alone is not equality.

Upper bounds require admissible endpoint families for every slab with all candidate overlaps <=P_k(epsilon), or a proved piecewise family with complete cover. Parameter interpolation of optimal endpoint examples is unjustified across overlap branches. Within a fixed closed chamber an affine endpoint interpolation and its epigraph inequalities do interpolate linearly; that conditional observation must be verified, not assumed. No such complete list of families was supplied in r265 or recovered here. The source reports computational upper bounds without printing those families in section 7.2/Figure 8.

Refutation needs one rational epsilon and ordered rational endpoints with measure epsilon, and EXACT checks F(s)<P_k(epsilon) at ALL candidate sums. A smaller value at a few centers is not a refutation. No witness is claimed.

## Actual certificate scale and selective-route qualification

One leaf uses 6 or 8 endpoints, d and epsilon: 8 or 10 scalar variables before eliminating the measure equality. An intentionally redundant order description uses at most choose(21,2)=210 or choose(36,2)=630 comparisons. There are 21 or 36 epigraph rows; constructing them uses at most 189 or 576 ordered-pair overlap evaluations. A minimal order description can use only 20 or 35 adjacent comparisons after an order is fixed. These are per-leaf sizes, not a count of feasible leaves.

For rational row data a conic certificate of an implied affine inequality can be sparsified in the augmented coefficient-and-constant space to at most 9 or 11 inequality generators, allowing equality generators with either sign. This is an existence size bound, not a supplied dual, bit bound, or runtime estimate. Exact rational identities are readily kernel-checkable locally. Coefficient heights and the total number of required leaves are unknown. The formal interface must also prove that a generator emits the specified row, not trust opaque solver labels. Factorials 21! and 36! are only crude order-list bounds and are not chamber censuses or plausible workloads. No chamber enumeration, solver, numerical search, or Lean was run.

A potentially selective strategy would branch only on comparisons needed by a failed symbolic lower-bound certificate, sharing successful certificates on coarser cells. It needs an independently proved small cover/pruning lemma before it is a tractable execution plan. Reflection gives only a factor-two symmetry and does not supply that lemma; active constraints in one optimum do not imply all optima have that pattern. We have no valid small cover, no bound on its leaves, and no concrete dual for the first unpaid slab. This strategy therefore does NOT justify a dormant Pi brief.

Precise next ordinary lemma, already beyond the paid first segment: for every three disjoint intervals of total measure epsilon in [4/7,7/11], prove 5D(E)>=6epsilon-2 by a bounded, explicitly covering case argument. A useful selective decomposition must exhibit its branches and local inequalities before execution. Even that lemma alone would still leave Delta_3's [7/11,5/7] lower bound, the earlier terminal upper family, and Delta_4's remaining slopes/families. Do not promote it as a full endpoint.
