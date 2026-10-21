# Planar first-passage metric changes: integrated notebook

PREFREEZE / no nominee. Authorized Codex / GPT-6 Astra / high / default service tier. Supplied campaign 19/20, latest R041; parent alone adopts grades and counts. No full theorem was frozen because the closed deductions below are compatible source/primary compositions, and the further geometric operation is unproved. Exact source, primary and original-history identities and extents are private. N is the stipulated simultaneous planar no-bigeodesic source; S is its shape-regularity companion; A and D are the actual primary structural and directional papers. The source truth and operative proofs are accepted, not audited.

## 1. Feasibility scope, and what the parameters mean

The first calculations concern iid finite nonnegative edge weights t on the unoriented nearest-neighbor edges E of Z², with a nonatomic law G satisfying E[min(X1,X2,X3,X4)^2]<infinity. This is N's exact law scope. The bounded-defect and finite-change deductions do not need strict convexity. For the directional construction in §§6–10, specialize to iid Exp(lambda), for any fixed lambda>0. S then gives a strictly convex C1 norm ball; D supplies the actual fixed-direction convergence/coalescence interface.

T_t is the passage metric. A ray/double ray is simple, with every finite segment minimizing. Costs count traversals for walks. A finite perturbation changes finitely many weights. A summable perturbation is ANY assignment s_e>=0 with

 A(s,t) = sum_(e in E) |s_e-t_e| < infinity.                         (1)

The perturbation may depend on the entire original environment, may create ties or zero edges, and need not have a stationary, product or absolutely continuous law. Every universal assertion about s below is deterministic on one original full-probability event. No uncountable intersection of new random-environment events is taken.

An additive C-defect double ray p would satisfy

 cost_t(p[i,j]) <= T_t(p_i,p_j)+C  for every i<j, C<infinity.        (2)

The task initially investigated (2). The reduction in §2 closes this question by a finite lowering, before labels of approximate rays are needed. It therefore does not supply a substantial nominee. The accepted original moment-free project theorem remains unchanged and is not retried or relabelled here. One could substitute an independently accepted no-bigeodesic premise at that wider scope, but that substitution would add no operation to this notebook.

## 2. Finite lowering excludes every bounded-defect double ray

Let a=ess inf G. Because G is nonatomic, t_e-a>0 almost surely. Choose theta>0 such that q=4 E exp(-theta(t_e-a))<1. For a root v, integer K>=1 and length n, exponential Markov and simple-path counting give

 P(exists simple n-edge path from v with sum(t_e-a)<=K)
       <= exp(theta K) q^n.                                    (3)

Borel–Cantelli and countability of v,K show that only finitely many simple paths from any fixed root have bounded shifted cost. In particular every simple infinite path has divergent shifted cost. The same count with t_e gives proper passage balls, finite minimizers, and a finite set of simple paths below any given root cost. Conditional atomlessness gives unique finite t-minimizers.

Suppose (2) has positive probability. Enlarge C to an integer. Any witness has a finite central segment F whose shifted cost exceeds C+2. Choose a rational epsilon>0 with |F| epsilon<1 and G([a,a+epsilon])>0. Countably many integer C, finite oriented simple segments F and rational epsilon cover the existence event. Hence a deterministic triple has a witness event E of positive probability. Its definition requires a double ray containing F with the stated defect and saving; the countable segment inequalities and path projection give completed measurability. No measurable selection of a whole path is needed after this reduction.

Independently replace the weights on this deterministic F by iid G restricted to [a,a+epsilon], leaving every other weight unchanged. On E the total saving on F is greater than C+1. For endpoints p_i,p_j on opposite sides of F,

 cost_s(p[i,j]) < cost_t(p[i,j])-C-1 <= T_t(p_i,p_j)-1.            (4)

Every path avoiding F keeps its cost and costs at least T_t(p_i,p_j). Therefore EVERY s-minimizer between these endpoints meets F. The changed environment is proper because it differs in finitely many finite edge values. Fix one vertex z incident to F visited by infinitely many of these minimizers, orient them from p_i to p_j, and use finite branching to extract both rooted arms. Both endpoint distances from z tend to infinity. All finite limit segments are minimizing and simple, so the limit is an s-bigeodesic.

The unconditional s-law is absolutely continuous with density

 product_(e in F) 1_[a,a+epsilon](s_e)/G([a,a+epsilon])            (5)

relative to the original product law. It thus assigns zero probability to N's forbidden bigeodesic event. But E has positive probability in the coupling and (4) forces that event for every replacement outcome on E. Contradiction. Conditioning the s-marginal on E was NOT used to claim it is product.

The outcome is simultaneous exclusion of all finite C and all paths in (2). This uses elementary path counting, bounded-density finite replacement, and compactness, all compatible with N and the actual primary modification operation. Neither a new quantitative rate nor a new exceptional-label argument was required.

## 3. Divergence of the detour gap, including overlapping arms

Let B_R=[-R,R]² intersect Z². For a finite nonempty K define

 D_K(R) = inf_{x,y outside B_R, z in K}
          [T_t(x,z)+T_t(z,y)-T_t(x,y)].                          (6)

This is nonnegative, nondecreasing in R and measurable (countable infimum). I claim, as an author calculation,

 D_K(R) -> infinity, simultaneously for every finite K.          (7)

Suppose instead the infima stay bounded. Choose triples with excess <=C and endpoint norms tending to infinity, increasing C by one to handle nonattained infima. Pass to a subsequence with the same z in K. Let alpha_n and beta_n be the unique t-geodesics from z to x_n,y_n. Extract local limit rays alpha,beta.

Two rooted geodesics can meet only in their common initial segment: a divergence and later meeting contradict finite uniqueness. If w is any common vertex of the limiting rays, their fixed prefixes to w occur in both finite geodesics eventually. The concatenation alpha_n reversed followed by beta_n contains a removable loop through z of cost 2T_t(z,w), so

 2T_t(z,w) <= T_t(x_n,z)+T_t(z,y_n)-T_t(x_n,y_n) <= C.            (8)

Properness confines all common vertices to a finite passage ball. Thus alpha and beta have a last common vertex w and thereafter are disjoint. Erasing their shared prefix gives a simple double ray through w.

Any subwalk of a walk of excess <=C has excess <=C: otherwise replacing that subwalk by a shorter path would reduce the whole walk by more than C, contradicting the lower bound T_t for its endpoints. Apply this to the finite concatenations and pass to each fixed segment of the double-ray limit. It satisfies (2), contradicting §2. This proves (7); countably many finite K give one event. In particular the erroneous shortcut of treating the original two-arm concatenation as simple is unnecessary.

## 4. Universal changes and a quantitative deterministic escape test

For any s satisfying (1), every simple path changes cost by at most A, so

 |T_s(x,y)-T_t(x,y)| <= A.                                     (9)

Nonnegative weights permit loop erasure. The set of simple s-paths from a fixed root of cost <=L is contained in the finite set of t-paths of cost <=L+A. Hence s-minimizers exist; simple ones can always be used; passage balls are finite. No positive lower bound on individual s_e is required.

An s-bigeodesic would have t-excess at most 2A on every finite segment by (9), contradicting §2. Thus EVERY summable change has no simple bigeodesic on the SAME t-event.

If a simple s-minimizer P from x to y visits z in K, then

 T_t(x,z)+T_t(z,y)
 <= cost_t(P)
 <= cost_s(P)+A
 = T_s(x,y)+A
 <= T_t(x,y)+2A.                                               (10)

Consequently D_K(R)>2A implies that every s-minimizer with x,y outside B_R avoids K. This implication is uniform over the entire perturbation ball A(s,t)<=A0 whenever D_K(R)>2A0. It is a deterministic threshold expressed in the original random gap, not an asserted tail bound on that threshold. Exact t-minimizers are included at A=0. N alone plus compactness already proves the A=0 avoidance; finite lowering pays the robustness for every finite A.

## 5. The metric at infinity and finite-support ray classes

If s-t is supported on finite F, let K contain its endpoints. For sufficiently remote x,y, minimizers in BOTH metrics avoid K by (10). Such paths have equal t and s costs. Cross-comparing the two minima gives

 T_s(x,y)=T_t(x,y),
 {simple s-minimizers x to y}={the t-minimizer x to y}.           (11)

This includes all remote endpoint pairs at once, not just a prescribed sequence. It does not assert that the distances from a root inside the changed region eventually agree.

Every ray in either metric eventually leaves B_R. All its later segments have remote endpoints, so (11) shows that it is a ray in the other metric after deleting a finite prefix. Thus the sets of geometric ray tails coincide, simultaneously over ALL rays. This conclusion is stronger in its perturbation quantifier than a resampling coupling; it is still paid by (7), path comparison and compactness. For fixed u in §6, the t-directional family coalesces, hence every s-ray of direction u has that same tail. An arbitrary finite change can introduce multiple finite prefixes; uniqueness from a given root requires an additional finite-uniqueness assumption on s.

For a general summable change and epsilon>0, choose finite F with

 a_F = sum_(e outside F)|s_e-t_e| < epsilon.

For remote endpoints, both minimizers avoid the vertices of F. Each changes cost by at most a_F, hence

 sup_(x,y outside B_R) |T_s(x,y)-T_t(x,y)| <= a_F                 (12)

once D_K(R)>2A. Taking increasing finite F proves that this supremum tends to zero. Summability gives analytic metric convergence but (11)'s exact tail equality is not inferred for infinite support.

## 6. Fixed-direction input with its exact quantifiers

Fix a deterministic unit u. Under Exp(lambda), S's strict convexity and differentiability identify the tangent-contact sector as {u}. D's actual Theorems 1–2 then give a probability-one event Omega_u on which, for every x and EVERY sequence z_n escaping in direction u (including environment-selected sequences), the t-geodesics to z_n converge locally to the unique ray Gamma_t^u(x). The rays from all roots coalesce, and

 B_t^u(x,y)=lim_n [T_t(x,z_n)-T_t(y,z_n)]
          =rho_u(y-x)+o(|y-x|) for fixed x, rho_u=grad mu(u).     (13)

For any fixed finite list of roots, their rays have a common future vertex. Local convergence shows that the passage differences for that list are eventually exactly constant along any such target sequence. This is the actual primary proof operation, not just convergence in distribution of a stationary cocycle.

Work on Omega_u intersected with the event in §§2–5. It suffices for ALL summable s simultaneously; there is no new probability event indexed by s. We do not claim simultaneous uniqueness for every random u. One may of course take a prescribed countable set of deterministic u.

## 7. Finite changes: an exact attachment formula

First let s-t have finite support F. Fix x. Choose R large enough to contain x,F and so that (11) applies to all pairs outside B_R. Let P be the finite vertex boundary of B_(R+1). Every path from x to a more distant z hits P. Subpaths of a minimizing path minimize. Since p,z are outside B_R, (11) gives T_s(p,z)=T_t(p,z). Triangle inequality and a first exit from a chosen minimizer therefore give the exact formula

 T_s(x,z)=min_(p in P) [T_s(x,p)+T_t(p,z)].                      (14)

There is no constraint that the candidate concatenation remain simple; nonnegative loop erasure suffices for the upper bound. For the lower bound, the actual minimizing prefix has cost T_s(x,p), and its suffix T_t(p,z).

Subtract T_t(x,z) from (14), and use (13) for the finite P. Along every u-directed sequence the difference is eventually constant, equal to

 h_s^u(x)=min_(p in P) [T_s(x,p)+B_t^u(p,x)].                   (15)

The value is independent of the auxiliary boundary, since it is a distance limit. Equation (9) gives |h_s^u(x)|<=A. Equation (11) shows h_s^u(x)=0 outside a finite ball (depending on F and A, uniform in u for which the limit exists).

Subtracting two limits yields

 B_s^u(x,y)=B_t^u(x,y)+h_s^u(x)-h_s^u(y).                       (16)

The signs in (15) use B(p,x)=lim[T(p,z)-T(x,z)]. The signs in (16) come from subtracting the two rooted distance corrections. An extra factor or opposite sign here would incorrectly move the slope.

## 8. Summable changes: a vanishing correction at infinity

Let F_n increase to E and s^(n)=s on F_n, t elsewhere. Put a_n=sum_(e outside F_n)|s_e-t_e|. All s^(n) are nonnegative. Uniformly in x,z,

 |T_s(x,z)-T_s^(n)(x,z)|<=a_n.                                 (17)

The finite-change limits h_n^u(x) from §7 are Cauchy, uniformly in x; for m>=n their difference is at most sum_(F_m minus F_n)|s-t|<=a_n. Define their uniform limit h_s^u. For any u-directed sequence, (17) and the eventually constant finite-change formula show

 lim_{z->u infinity}[T_s(x,z)-T_t(x,z)]=h_s^u(x).                (18)

The same epsilon proof works for each arbitrary target sequence on the already fixed event; no perturbation-dependent null set appears. Moreover

 |h_s^u(x)|<=A,
 h_s^u(x)->0 as |x|->infinity,                                 (19)

because (12) controls both remote endpoints before taking the target limit. Thus (16) holds for every summable s, and its correction is in c0(Z²). At finite support the correction has finite support. Uniform approximation is what pays the infinite perturbation; no claim that an arbitrary infinite perturbation has an absolutely continuous law is made.

For two summable changes r,s of the same t,

 sup_x |h_s^u(x)-h_r^u(x)| <= sum_e |s_e-r_e|.                  (20)

This follows directly by comparison of distances and passage to their common directional limits. In particular B_s^u has the SAME asymptotic linear part rho_u, with a bounded correction to B_t^u. There is no claim that its expectation equals rho_u when s is chosen adversarially; stationarity has not been preserved.

## 9. Calibrated directional rays in the changed metric

The limit B_s^u is additive, antisymmetric and bounded by T_s in absolute value. Take simple s-minimizers from x to a u-directed sequence and a local subsequential limit q. Properness guarantees an infinite simple ray. For any edge v->w on a fixed prefix of q, the finite minimizing equality gives

 T_s(v,z_n)-T_s(w,z_n)=s_{vw}

eventually along the subsequence. Taking (18) at v,w proves B_s^u(v,w)=s_{vw}. Additivity calibrates every prefix of q.

Equation (9) leaves the shape norm unchanged. Calibration, (13), and (16) give

 mu(q_j-x)-rho_u(q_j-x)=o(|q_j|).                              (21)

Every limiting direction lies in the contact set of rho_u. Strict convexity makes that set {u}, so q is u-directed. This proves existence from every root for every summable change. Conversely, ANY simple s-ray already known to have direction u is calibrated by B_s^u, by taking its own vertices as targets in (18).

This construction proves neither uniqueness nor coalescence for general infinite-support s. It also does not prove that every s-ray has some asymptotic direction: that would require identifying the boundary limits of arbitrary approximate t-rays, not just the fixed-direction limits in (18). The strict-convexity argument (21) needs an already identified calibrating slope; strict convexity alone does not supply it.

## 10. Exact residual identity and a converse construction

For an oriented edge write

 a_u(v,w)=t_{vw}-B_t^u(v,w)>=0,
 d_{vw}=s_{vw}-t_{vw}.

Let q be any s-ray of direction u. Calibration and (16) give

 a_u(q_i,q_(i+1))
    =h_s^u(q_i)-h_s^u(q_(i+1))-d_{q_i q_(i+1)}.                (22)

Because q is simple, the d-series is absolutely summable. Because q escapes, (19) makes its terminal h value tend to zero. Therefore the whole tail defect is exactly

 sum_(i>=m) a_u(q_i,q_(i+1))
     =h_s^u(q_m)-sum_(i>=m) d_{q_i q_(i+1)} >=0,               (23)

and tends to zero as m->infinity. This is much stronger bookkeeping than merely declaring a bounded total error.

There is a converse feasibility construction which makes the unpaid geometric issue concrete. Suppose a simple u-directed path q in the ORIGINAL environment satisfies

 B_t^u(q_i,q_(i+1))>=0 for all i,
 sum_i a_u(q_i,q_(i+1))<infinity.                              (24)

On its unoriented edges set s_e=B_t^u(q_i,q_(i+1)); leave all other weights at t_e. Simplicity prevents conflicting assignments. Then s>=0 and its perturbation norm is exactly the series in (24). The original B_t^u remains dominated by every s edge in BOTH orientations, since |B_t^u(v,w)|=s_e on each changed edge. Hence it is dominated by T_s. Along q it is calibrated, so q is an exact s-ray.

Every original t-directional ray is also retained. A positively changed (lowered) edge has a_u>0 in q's direction and B_t^u>=0; it cannot be calibrated by the t-u family in either orientation. Thus all t-u rays have unchanged costs and remain calibrated by B_t^u. They coalesce and provide targets along a common tail, so the directional B_s^u is exactly B_t^u. Equations (16),(19) then force h_s^u=0.

Thus an escaping path satisfying (24) and failing to coalesce with the original family would produce a summable adversarial change with the SAME directional Busemann field but additional noncoalescing geometry. Existence of such a path is NOT asserted. Nor is its exclusion established. This conditional construction is not a nominee or a finding; it identifies exactly why the completed analytic conjugacy does not settle the geometric question.

## 11. Why the remaining passage from small defects to coalescence is unpaid

For a fixed finite pair v,w, properness and unique t-minimizers imply a positive gap gamma_t(v,w) between the optimum and the next simple path (or infinity if there is none). Perturbation mass less than gamma_t(v,w)/2 preserves that finite path. But the endpoints needed to compare two infinite rays move. Nothing in (7), (12), (18) or qualitative C1 strict convexity bounds these moving gaps below in terms of the remaining perturbation mass. Both may tend to zero with unrelated rates.

The original primary proof uses invariant law, finite-energy modification, ordered/coalescing selectors and, for fixed direction, identification of extremal rays. An adversarial s in (1) need not retain stationarity or that conditional law. Reapplying those probability arguments to s would be a hypothesis error. The source label budget similarly starts from exact minimizing rays and uses output-conditioned hidden raises; (22) is a nonnegative residual with a finite budget, not exact calibration by t. The finite-lowering trick of §2 concerns two-ended paths and does not create a contradiction from two rays travelling to the same end.

A proof of geometric rigidity would have to rule out the finite-total-residual escape mechanism in (23)–(24), or prove a compatible positive total toll for infinitely many evasions of the original coalescence structure. No such estimate is supplied here. Under ties, even eventual identical tails is not justified by purely deterministic metric stability: in a one-ended chain of diamond cells, give the main edge from v_n to v_(n+1) cost 1 and the alternative two-edge route through w_n costs 2^(-n) and 1, respectively. Lower the first alternative edge to zero. Its original Busemann increment from v_n to w_n is zero, while that from w_n to v_(n+1) is 1, so this lowering preserves the whole one-ended Busemann potential. Total modification is finite, distant distance changes tend to zero, and the one-ended Busemann potential is unchanged; two minimizing rays can choose different arms in every cell and fail to have identical tails. This is a deterministic locally finite graph diagnostic, NOT an iid Z² counterexample and NOT an assertion that the s-field in this task realizes it. Imposing finite uniqueness eliminates this diamond example but does not itself prove the moving-gap estimate.

## 12. Strongest reduction and disposition

The completed chain is: finite lowering of a hypothetical bounded-excess double ray; compactness; diverging uniform detour gap; universal finite/summable perturbation escape; exact remote metric and ray-tail equality for finite support; remote metric convergence for summable support; finite-boundary attachment; a c0 Busemann correction for every summable perturbation; fixed-direction calibrated ray existence; and the exact residual/converse calculations.

All closed operations are paid by the stipulated source, actual primary finite-change/directional mechanisms, and elementary comparison, compactness and uniform approximation. The primary boundary-correction construction in N's appendix is particularly close to (16); replacing its restricted metric by a finite attachment and passing in the summable norm is compatible bookkeeping. Quantifier strengthening alone is not asserted substantial.

No full substantial candidate was frozen. The further geometric exhaustiveness/coalescence operation is unproved, and no weaker or renamed old target is offered. There is no independent correctness or contribution grade, formal support, manuscript, release, acceptance or count claim. The limits are limits of this construction, not nonuniqueness results or worldwide open-problem certifications.
