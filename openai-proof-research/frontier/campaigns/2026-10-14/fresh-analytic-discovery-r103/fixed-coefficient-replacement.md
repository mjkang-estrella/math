# Fixed geometric-history coefficients: telescoping and replica protection

Author proof assembly. Scope-status.json remains unchanged. This note concerns finite-dimensional laws only; the full J1 target is still pending. All uses of the stipulated sources are specified, and no independent review is claimed.

## 1. Normalization and the separated range

Write lambda=e^-2, a_e=A_e(B0 e,1), and r_e=1/E N_e(Q*). Source V's calibration and source A's amplitude give lambda r_e a_e comparable to1 and a_e comparable to e^(5/4). Fix k, a finite polygonal test family, a bounded test F of finitely many observations, and a compact set of insertion tuples separated from one another and every tested boundary by 10R>0. Balls of radius3R are disjoint. Constants below may depend on k,R and the tests, never on e or on the selected lifetime marks.

Let D_i be the fair geometric presence-history difference at location i. After excluding histories with more than one presence change, its history is a birth, death, or constant presence. Let C_i be the signed one-refresh color-history operator on geometry containing location i at all observation times; for a constant presence put C_i=0. Operators at distinct sites commute in each expansion. Products of D and C are understood as finite linear combinations of experiments: a C site is always a nucleus, while a D site ranges over its presence subsets. There is no assertion that a color operator is defined on a diagram in which its own point is missing.

Their exact finite experiment telescoping is

 product_i D_i - product_i C_i
 = sum_i (product_{j<i} C_j) (D_i-C_i) (product_{j>i} D_j).       (1)

One can verify (1) by expanding all finite signed experiment measures. Values at common hybrid experiments cancel. A partial product has total variation at most C^k. In (1), a constant-presence C_i=0 is legitimate: replacing that slot by zero deletes that term's principal coefficient.

## 2. Conditioning without inside-pivotal conditioning

Choose e << h << l << R. Around i use a base-process screened seam near h and a common annulus out to l. All selected locations other than i lie outside B_(3R)(zi). The outside sigma-field E_i contains marked base variables beyond the seam's outside collar, the seam variables themselves, all selected history marks, and any auxiliary choices made outside that collar. Conditional on E_i and seam success, the inside marked Poisson process is the original independent inside process with the seam attachments fixed. The source A05 cut construction proves precisely this independence; it is not independence of unrestricted Voronoi events.

The other sites' necessary influence probes can be placed in their disjoint R-balls. Call their intersection J_-i. It is E_i measurable. If any probe fails to have the required arms, the corresponding signed coordinate cancels for EVERY formal cap state at i. Thus after applying the other k−1 signed operators the conditional payoff has sup norm at most C^k 1_(J_-i). This cancellation is why it is valid to retain all k−1 factors even while using an operator TV bound at i. No event that i is pivotal is put into the conditioning sigma-field.

The quantifier EVERY formal cap state can be checked deterministically. A source formal cap is a noncrossing pairing of alternating switch ends. Draw its disjoint wall arcs in an abstract disk and color the complementary faces consistently with the boundary runs; refine this disk into a finite colored triangulation if needed. It therefore supplies a planar filling for the connectivity argument, even if it is not a Voronoi filling on the original inside nuclei. Replacing the disk at i by such a filling cannot alter a disjoint probe at j. If varying j changes a tested crossing in any of these fillings, the usual local pivotal implication still gives the required arms across j's unchanged probe. Thus absence of the j arm test forces cancellation for all formal fillings at i, simultaneously. The support bound on the conditional payoff is an operator bound on the full formal state space, not just on caps sampled by the original inside law.

With one replica, expose the wall diagram between h and l. If it has at most four transmitted ends, the two-cap normal form from bulk-kernel-and-boundary.md applies. The outside histories produce a function f(u,v) of the absent and present cap bits; its four coefficients depend only on E_i and the annulus, not on the unrevealed inside state. The exact formulas in single-jump-replacement.md identify D_i-C_i with a bounded test of the signed fair-insertion marginal. A constant-presence D_i is directly such a marginal. Source A Corollary tr:insertion gives its conditional TV bound C(e/h)^(2+nu). The bound holds against arbitrary bounded outside data. The other-site expectation contributes at most C_(k,R) a_e^(k-1), by disjoint buffered probes. Hence this part of the error is at most

 C_(k,R) a_e^(k-1) (e/h)^(2+nu).                         (2)

Screen failures at fixed positive h have exponentially small cost; retaining the other probes makes them negligible after normalization. The source corollary already sums internal failed screens. None of its even/isotropic cancellation is applied to an inside law conditioned on pivotality.

## 3. Retaining the active factor on six-wall failures

On six-or-more transmitted walls between h and l, abandon the signed cancellation but retain a necessary active influence probe from B0 e to a buffered scale below h. The geometric D_i and color C_i each vanish unless some tested crossing depends on that slot. The source localization failure decomposition supplies the same microscopic arm cost. Disjoint buffers, quasi-multiplicativity, and the source six-arm bound give

 |error_bad| <= C_(k,R) a_e^k A6(c h,c' l)/A4(c h,c' l).   (3)

Fixed changes of radii are absorbed into constants; one may first choose a sufficiently small h/l. The denominator is bounded below by c(h/l)^g with g<2, whereas A6 is at most C(h/l)^(2+beta). Consequently the ratio is at most C(h/l)^(2+beta-g), tending to zero. The other k−1 arm factors in (3) were not discarded. After multiplication by (lambda r_e)^k, (2) tends to zero as e tends to0 with h fixed, because a_e is comparable to e^(5/4) and 2+nu>5/4. Then (3) tends to zero as h/l tends to0.

## 4. A second replica

The inside geometric change at i would also affect the other replica's diagram. It is not legitimate to average the active inside while retaining an inside-dependent inactive observable. Introduce the source V06 protection event: in an annulus from l to R, the inactive replica has no four alternating arms, with base screens imposed. This event is measurable above the seams and is unchanged by all inside exchanges. On it every inactive crossing is unchanged by ANY inside modification and every setting of the other selected histories. Its contribution can therefore be included in E_i without changing the preceding active-message argument. The source proof explicitly includes cell changes, not only recolorings.

For the complement, retain the active arms below l, arms of both replicas through the protection annulus, and the k−1 other-site probes. Conditional on its common geometry, the labels have independent fair colors. The second-moment arm bound gives E[p_arm(eta)^2]<=C A4(l,R)^2. Quasi-multiplicativity then yields

 |error_unprotected| <= C_(k,R) a_e^k A4(c l,c' R)+o_e(a_e^k). (4)

This is exactly the multiplicative protection operation read in V06 lines545-595, with only one active local replacement. Choose l/R small after fixing R, then h/l small, and finally let e tend to0; equivalently take the iterated limit e->0, h/l->0, l/R->0. Combining (2)-(4) and the finite sum (1) proves vanishing of normalized fixed-k replacement errors on the separated range for single-active labels, including constant-presence slots.

### Restoring the common inserted geometry in the source kernel

There is an additional geometry convention to reconcile. The intermediate single-active C_i may insert zi only into its active replica, while the SOURCE color-history kernel inserts zi into the common geometry of BOTH replicas, giving the inactive label a fair constant color. Let R_i^inactive denote that constant fair insertion. The exact correction is

 C_i^source-C_i^active = C_i^active (R_i^inactive-I).

For a nonzero correction, the active centered color coordinate and the inactive geometric coordinate must both influence a test at zi under some settings of the other slots. Their common exterior probe therefore has four arms in BOTH labels. The same second-moment estimate used below bounds the correction on separated tuples by C_(k,R) a_e^(k+1), including all other k−1 factors. A finite telescoping over the selected sites and location UI removes this error after normalization. Only AFTER this correction is the principal coefficient literally the source's common-geometry color-history kernel. Inactive geometry is not silently equated across these two formulations.

## 5. Shared initial locations: exact replica marking

For two conditionally independent processes given the initial uncolored geometry, mark each initial point by independent death times d1,d2 and independent fair colors c1,c2. The common persistent base consists of points with both dj>aT, intensity lambda exp(-2aT), where a=r_e/2. Birth processes in the two replicas are independent, each with intensity lambda in space-time. These are independent Poisson marked classes; they are not two independent initial geometries.

Initial points dying in BOTH replicas inside the physical window have spatial intensity lambda(1-exp(-aT))²=O(lambda a²). Their removal changes any fixed list of observations with probability O(a²/r_e)=O(r_e), by the same intensity-interpolation pivotal calculation as lifetime-expansion.md, separately in each replica and then a union bound. The initial point count itself is not small. This removal is only for finite lists.

The remaining rare initial type is, for example, death in replica1 and constant presence in replica2. Its fair history operator is H1 H2-I, with H1 a death history and H2 constant. Exactly

 H1 H2-I = (H1-I)+(H2-I)+(H1-I)(H2-I).                 (5)

Colors are independent across labels, so the tensor product here is literal conditional on the common geometry. The first summand is a single-active death; the second is a single-active constant insertion and has zero limiting coefficient by Sections2-4. The third requires influence in BOTH labels at that site. On a separated tuple its microscopic probability is at most C_R a_e² by the quenched second-moment arm bound. Other sites retain their single arm factors, giving C_(k,R) a_e^(k+1). After the one-event normalization (lambda r_e)^k this tends to zero. Simultaneous base-screen failures are summed with the outermost-failure method; its polynomial loss has exponent2g and the exponential screen tail still sums. The opposite initial type is identical. Births have only one active label from the outset.

Thus a rare shared location is NOT assigned the source q² repeated-label factor. Its double-active part is removed by the extra microscopic arm probability instead. For fixed k, collision/boundary neighborhoods are removed first by location uniform integrability, so this separated estimate suffices. A one-arm-per-site forest bound controls all marked types uniformly and supplies the series tail; (5) costs only a fixed exponential factor in k.

## 6. Summation and finite-dimensional conclusion

The normalized temporal measures of births and single deaths converge to Lebesgue measure times a/r_e=1/2 for EACH active replica. For example a rescaled birth in [tau,tau+d tau] has spatial intensity lambda a d tau; a surviving single initial-death class has intensity lambda a exp(-a tau) exp(-aT) d tau. Both normalized densities tend to1/2. Short-lived births and double-death initial histories have already been removed for finite lists. Their sum therefore gives the color-refresh signed history weight

 w_refresh = integral_0^T (law of fair color refreshed once at tau - law of constant fair color) d tau.

An actual rate-r_e color-refresh history has signed measure r_e w_refresh+O_T(r_e²) in total variation relative to its constant fair history; the probability of two or more refreshes is O_T(r_e²). The source coefficient majorant controls the total contribution of this remainder by O_T(r_e). Base intensity differs from lambda by a factor1+O(a); its mesh and pivotal normalization are asymptotically unchanged by the source amplitude.

For each fixed k, the replacement above plus source V Lemma common-calibration identifies the geometric coefficient with the corresponding triangular refresh coefficient, with one or two replica labels. Location UI first removes collisions and boundaries; no arbitrary Jordan-boundary statement is needed. The common summable majorant C_T^k k^(-(1-g/2)k) proved by the forest argument permits passage through the full series. In the triangular model the two color replicas are independent on a deterministic lattice. Hence the one- and two-replica finite-dimensional limits are the target dynamical law and its independent square.

For any fixed finite family of crossing observations, let Z_e be its conditional probability given the initial uncolored geometry. The one-replica result gives E Z_e->p; the two-replica result gives E Z_e²->p². Thus Z_e->p in L² and in probability. This is the proposed author-level quenched finite-dimensional bridge, not the full frozen theorem. It relies on the explicitly stated cap reduction, source signed-message contract, and simultaneous subset localization in the preceding notes. Those interfaces still require independent scrutiny before any full proof claim.

## 7. Reading and remaining scope

New source reads: V06 lines520-630, including the full inactive protection argument; A05 lines875-909, completing the fair-insertion corollary proof; V07 lines60-110 reread for calibration normalization. Previously read V05 forest and location UI and V07 full common calibration are used as specified. The long A05 transfer proof before the corollary has NOT been read in full; the corollary is a stipulated source theorem with its actual contract and proof read. Primary reading limits remain as previously recorded.

J1 tightness is not implied by the finite-dimensional bridge. In particular, deletion of short-lived particles was not uniform over paths, and arbitrarily short paired crossing excursions can escape all fixed time lists. A stopping-time or small-scale pivotal stability estimate remains necessary. No manuscript, independent gate, nomination, or count change is asserted.
