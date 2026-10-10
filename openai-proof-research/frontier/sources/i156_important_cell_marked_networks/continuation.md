# I156 continuation: same-site data and relative boundary-separation mass

These are new deductions, separate from the unchanged original audit. The full important-cell network theorem is not proved here. All pinned OpenAI lower operations are stipulated; the deductions use their actual event, exploration, forced-test, history and sewing constructions. This is a technical partial, not a nomination.

## Model and normalization

Use the original whole-plane Poisson process of intensity e^-2, independent fair initial colors, closed-cell quad crossings without wiring, and all cells meeting a test, including cells whose nuclei lie outside it. Freeze the geometry. Write r_e=(E N_e(Q*))^-1, so refresh clocks have rate r_e and actual flips have rate r_e/2. At each refresh use an independent fair bit. An initially delta-important nucleus v belongs to the unique half-open delta-grid square S(v) and has four alternating arms from its cell boundary to the boundary of 3S(v), inside that square and not using its own color. This definition is not changed at large cells. The cutoff retains exactly these initial sites with their original clocks.

Let K be a compact subset of D=(-2,2)^2 and take fixed delta small enough that every 3S with S meeting K is compact in D. For example delta<dist(K,D^c)/4 suffices. Auxiliary quads whose triple squares extend outside D cannot be called quads of H(D); one could instead use a larger ambient domain and restriction, but that additional construction is not being silently used here. All statements below are local on such K. Let alpha4(delta,1) denote the triangular alternating four-arm probability in a fixed square-annulus convention. Bounded changes of radii change only constants. The source calibration and quasi-multiplicativity give

    r_e e^-2 A_e(b_e,delta) <= C / A_e(delta,1),

with b_e=B0 e. Fixed-scale critical comparison gives the corresponding limsup bound C/alpha4(delta,1). In particular these are normalized counts, not unweighted probabilities times the number of cells.

## 1. Same-site membership extraction

**Lemma 1.** Fix finitely many polygonal quads Q_1,...,Q_m compact in D. Their initial pivotal measures have joint same-site membership-pattern measures

    nu_A,e = r_e sum_v [product_(j in A) I_j(v)]
                       [product_(j notin A)(1-I_j(v))] delta_v,
    empty != A subset {1,...,m}.

These measures, jointly with the initial H state, converge to the calibrated triangular/GPS pattern measures, annealed and quenched in probability. Their Poisson time marks, with one shared clock on each overlap and fair postmark bits, converge jointly as well. This includes the measure of the finite pivotal union. It does not include every initially important site.

**Proof.** For k distinct inserted sites v_1,...,v_k give site i a dedicated observation label i, and give all sites label 0. For each i fix a nonempty subset A_i of the quad indices. Under L_i the initial fair bit b_i is unchanged at every label except i, where it equals 1-b_i. Put w_i=L_i-P0; its full variation norm is at most two, independently of |A_i|. Test

    H(omega^0) product_i product_(j in A_i)
                   |f_j(omega^i)-f_j(omega^0)|.

Expand the product of the signed w_i. If its ith factor is -P0, *no site* differs between labels i and 0: the other L_l change only at their own dedicated labels. Since A_i is nonempty, that entire summand is zero. The sole surviving term is

    E[H(omega^0) product_i product_(j in A_i) I_j(v_i)].             (1)

Thus several quad memberships at one site are paid at one insertion, not miscounted as several distinct-site factorial labels. The source permits these arbitrary finite histories. Spatial continuous tests multiply (1). Source Sections 06–07 compare its normalized insertion integral to the triangular integral; Section 05's nonnegative event bound supplies domination. Membership in an exact pattern A is now expanded by the genuine finite identity

    product_(j in A) I_j product_(j notin A)(1-I_j)
      = sum_(B subset A^c) (-1)^|B| product_(j in A union B) I_j.  (2)

Every monomial in (2) is nonempty. At k spatial labels this is a finite sum with at most 2^(mk) terms; m is fixed, so the extra factor is absorbed in the source exponential-in-k constant. Alternatively use the disjoint finite pattern partition directly. The union indicator is sum_(A nonempty) of its pattern indicators, or 1-product_j(1-I_j). It is not the sum of individual pivotal indicators.

For completeness, measure-law identification needs more than formal moments. On a bounded box, the mass of every pattern and their union is bounded by M_e=r_e sum_j N_e(Q_j). Its distinct-site factorial series obeys the source C^k k^-ak bound, a=1-g/2>0, with m-dependent C. For positive theta,

    E exp(theta r_e N) = sum_k E[(N)_k]/k! (exp(theta r_e)-1)^k.

The normalized parameter (exp(theta r_e)-1)/r_e stays bounded as e tends to zero. The displayed source series therefore gives uniform exponential moments on bounded theta intervals. Ordinary-moment partitions with repeated spatial sites carry r_e^(k-l) when only l sites are distinct and vanish for l<k. This proves uniform integrability and determinacy. Location Lp bounds remove diagonals and polygon-edge strips. A box containing the test domains with positive margin captures all relevant nuclei except for an exponentially small cell-reaching event; polynomial Poisson moments and the source remote-cell estimates control its weighted mass. The limits are diffuse and give fixed lines zero mass. These facts give joint weak-measure convergence from (1)–(2).

Initially take H to be any bounded finite crossing cylinder. Continuous functions on H(D) are uniformly approximated by finite such functions using the geometric finite-entourage bridge audited separately. This gives the joint H state without asserting X=H. To identify the name of the triangular limit, first exclude a rho-neighborhood of all tested quad boundaries. There every pivotal site is rho-important up to a fixed change of the cutoff constant. The GPS important measure and its stable single-mark network identify whether toggling that mark changes each of the finitely many crossings. Their simultaneous Boolean readout gives exactly the pattern partition above under the important measure. The near-boundary contribution tends to zero by the same fixed-degree location integrability already used; then rho decreases. Thus identification with GPS pattern measures does not presume that arbitrary weakly convergent overlapping measures retain their overlaps. Alternatively, the common factorial limits and exponential tightness already identify the triangular subsequential law uniquely before attaching this GPS description.

The same extraction works in each of two independent colored replicas on the same frozen geometry. Shared geometric insertion labels have the source's extra vanishing q_e; summability, not a raw count of sites, removes them. Hence conditional bounded-test means converge in L2 to their common limiting expectations. Tight compact sets in H times the finite vector of measure spaces and finite Lipschitz nets yield quenched convergence in probability.

At finite e the patterns partition the retained nuclei. Conditional on the initial configuration, pattern A has intensity nu_A,e(dx) dt Fair(db), and different patterns have independent Poisson measures. The mark for pattern A is projected to every quad j in A. This is exactly a single clock shared at overlaps. Joint Laplace functionals pass to the limit under weak-measure convergence on bounded time windows and continuity sets. Truncation of remote support handles the noncompact spatial notation. The two-replica version follows by the same conditional argument. The expected number of unordered pairs of refreshes at the same retained nucleus is T^2 r_e E nu_union,e/2, which tends to zero. At each finite e repeated marks are still permitted, and the clock rate is r_e, not r_e/2. The actual color-change probability at a refresh is one half. This proves the lemma. No operation in this proof identifies a connectivity network. QED.

**Optional finite-response consequence of the same identity.** For a fixed k, finitely many additional observation labels may encode every prescribed toggle assignment to the k inserted sites. At these labels L_i has the assigned bit, while the dedicated label i retains its former rule. Multiply the preceding test by any bounded function of the crossing responses at the additional labels. Negative constant-history terms still vanish at a dedicated label. Thus the source also compares the initial-membership-weighted finite crossing response table at finitely many inserted sites. Repeated visits to a selected site can be encoded by additional finite labels, with fair postmark bits in its history law. This is a finite-history coefficient statement only. It does not assert that these tables define a stable network, a consistent H state for all quads, or an entire path law without the remaining geometric steps.

## 2. Screened inclusion and its normalized error

**Lemma 2.** In general J_(S,h) is not a subset of I_delta (the original audit gives the counterevent). If the cell of v in S is contained strictly in 3S, color-pivotality for a quad with domain 3S implies initial importance. Consequently, for a fixed delta and K as above,

    E[r_e sum_(v in K) 1{v in J_(S(v),h) \ I_delta}]
       <= C |K| r_e e^-2 exp[-c(delta/e)^2] -> 0.                (3)

The bound is uniform in the boundary mesh family.

**Proof.** Use the two settings of the cell's color. A black crossing in one and its complementary white separator in the other must both use that cell. Removing the cell leaves two arms of each color to the appropriate opposite marked boundary arcs, alternating around the cell. The interior containment ensures these are arms from its boundary to the artificial boundary. No boundary wiring is used. Closed black cells and the open white separator are the standard complementary convention of the stipulated local-change lemma; the latter can be thickened away from black cells along a finite witness. Deterministic square corners or marked points have no tangencies to Poisson vertices outside a null geometry set. Closed marked-side endpoints are shared in the usual quad convention, which does not remove the separating white crosscut. The implication is exactly that lemma applied with the cell strictly in the interior, not a claim about a cell crossing the artificial boundary.

Every v in S has distance at least delta from the boundary of 3S. Failure of the containment therefore requires the Palm cell of v to reach distance delta. A finite conical/occupied-square cover about v gives probability at most C exp[-c(delta/e)^2]. Insertion of v cannot spoil occupancy of the other nuclei in those sectors. Mecke integrates this Palm probability, giving (3). It does not multiply the probability of a global bad tessellation by an unbounded random count. Calibration makes r_e e^-2 at most polynomial in 1/e, so the exponential wins. The same screening covers remote nuclei whose cells enter the relevant collars. QED.

## 3. Relative separation mass: a paid estimate short of A151-rem

Write c_S for the center of S and R=3delta/2, so 3S=B_infinity(c_S,R). Let G_(S,u) be Vanneuville's GI_ext_u(R/e), rescaled and translated to 3S, with 0<u<u0. This is the event excluding three arms in every boundary patch A(y;10uR,R/4) intersected with 3S. It controls the distance from an outgoing interface endpoint to every other outgoing interface, not only endpoint pairs.

**Proposition 3 (relative mass of outer separation failures).** For fixed delta and K as above,

    limsup_(e->0) E[r_e sum_(v in K) 1{v in I_delta}
                                          1{G_(S(v),u)^c}]
      <= C_K alpha4(delta,1)^-1 u.                            (4)

The order is e->0 for each fixed positive u, followed by u->0. In particular e must satisfy R/e>=100/u. This is a power bound for the mass on **separation failures**, not for the mass absent from J. It does not prove the displayed A151-rem power, or any vanishing modulus for that omitted mass.

**Proof.** Work in the Palm law with a nucleus at v in S. Separate two sets of underlying marked Poisson coordinates. The inner set is contained in B_infinity(v,delta/8). In that set use buffered dyadic necessary four-arm probes out to a small fixed multiple rho of delta (for example rho=delta/64), allowing failed screens as in source Lemma 2.3. The outer set is a fixed enlargement of the annulus A(c_S,3R/4,R), with its inner boundary still outside B_infinity(c_S,delta). The sets have a fixed positive gap, uniformly over v in S. On successful outer occupancy screens, every cell and every color used in G_(S,u) is determined by the outer coordinates. Define G^loc by completing these coordinates deterministically outside their enlargement. Its value agrees with G on that screen; the error probability is at most C exp[-c(delta/e)^2]. The completion is only a measurable test, not a change to the model. The Palm insertion v lies strictly outside the outer support, and on its screen cannot affect it.

The inner necessary probe P_v is measurable in the inner coordinates (and the Palm insertion) and has probability at most C A_e(b_e,rho). Importance implies P_v except for an outermost inner screening failure at a radius comparable to delta, whose probability is exponentially small. This formulation includes a large initial cell: if it skips a shell, occupancy fails there. To verify the relative bound for smaller failures, group by the outermost failed radius t and retain arms only from Ct to rho on disjoint buffered coordinates. Its contribution is bounded by

    C exp[-c(t/e)^2] A_e(Ct,rho)
       <= C A_e(b_e,rho) (t/b_e)^g exp[-c(t/e)^2].              (5)

The dyadic sum is finite uniformly; the tail t>=M b_e divided by A_e(b_e,rho) tends to zero as M->infinity. The final shell with no retained annulus is covered using the polynomial lower bound on A_e. A screen extending beyond the chosen inner support is instead included in the exponentially small fixed-delta error. Thus no unrestricted Voronoi arm events on merely disjoint planar sets were called independent. This also handles remote cells; on a passing screen they cannot enter, and on failure they are charged in (5) or the final exponential.

Vanneuville Lemma 2.14 gives P((G^loc)^c)<=Cu+C exp[-c(delta/e)^2] for R/e>=100/u. Its proof covers O(u^-1) boundary patches and pays a half-plane three-arm cost O(u^2) in each. Square corners cause no loss for this *outer* event: each patch inside the convex square is contained in a supporting half-plane. The poorer inner-boundary corner exponent is not substituted here. Independence of the two marked-coordinate sets therefore gives

    P^v(I_delta(v),G_(S,u)^c)
       <= C A_e(b_e,rho) u + C exp[-c(delta/e)^2].              (6)

The constants can be enlarged for the fixed buffers. The own color of the inserted site is irrelevant to its arms; all other inner colors remain fair. This justifies Palm insertion rather than conditioning on a random pivotal mark.

Integrate (6) over v in K using Mecke and multiply by r_e e^-2. The second term tends to zero at fixed delta. Quasi-multiplicativity and fixed-factor radius comparisons replace rho by delta, and the calibration displayed above supplies alpha4(delta,1)^-1 after the mesh limit. This proves (4). It is valid for each replica separately on shared geometry; summing the two marginals also bounds the probability of either replica's bad retained marks. No independence of the two geometric events is needed. QED.

On [0,T], (3) or (4) times T bounds the expected number of refresh marks in its corresponding bad set. Markov gives the same negligible-mark conclusion quenched in probability. Neither estimate implies that the remaining marks have the correct connectivity annotation.

## 4. The remaining concrete operation

The missing route-A implication is the following deterministic-plus-relative statement in the clipped Poisson cell complex. Starting with the four arms of a cell in S and the outer separation event, one must select four mesh boundary marks so that the two cell-color settings force the complementary quad crossings, with corner landings, returns of an interface near another endpoint, and cells crossing the artificial boundary treated explicitly. Boundary-return interfaces and the incidences of a clipped cell must be tracked, not replaced by a drawing of four separated endpoint dots. A proof that all important cells outside the events charged in (3)–(4) have such a witness would give the omitted-mass bound. Such a characterization has not been established here. Accordingly no vanishing modulus, let alone the requested displayed power, is claimed for important cells absent from J.

Even that mass implication would not by itself identify the marked networks. For a finite cloud of retained boxes, the required annotation records primal and dual connections among boxes and the four tested boundary arcs, including the cyclic incidences needed to evaluate **every** coloring of the retained boxes. Its Boolean readout must give exactly one of the complementary primal/dual crossings for each assignment. It must agree with the original cell tests for all assignments, not just with their initial crossing values. The finite-history consequence above provides the appropriate weighted coefficient tests, but does not establish the geometric stability of that annotation as the box size decreases.

The actual available machinery is substantial. The stipulated critical source Section 03 constructs oriented loops, prime-end banks, stopped faces and recursive explorations, paying bulk six-arm, boundary three-arm, line four-arm and fixed-point one-arm contacts before passage to the limit. Section 04 reads finite forced-square prescriptions jointly with the critical state, uses favorable tubes and their perturbations, and retains all complementary incidences. Section 06 gives relative site-to-square comparisons for arbitrary histories, including inactive-replica shielding and symmetric exchanges of marked Poisson geometry with Palm annotations. Section 07 supplies common calibration. The amplitude companion's Section 05 works with arbitrary noncrossing cap states, uniform output-seam norms and a domination argument **before** conditioning on rare explored shapes; its first-four-tip reduction and six-arm tail are relevant tools, not just an amplitude headline. Section 06 retains central arms while summing insertion failures and remote cells. These operations make the prospective reconstruction technical in this stipulated setting; they are not an already written proof of the missing marked-network law.

GPS dynamics Sections 6–7 define primal/dual networks by all boundary/box connection tests. Their stability argument takes a union over all admissible box families, so its global six-arm/boundary bad event is paid under the unweighted critical law before selecting random marks. Alternatively a Voronoi adaptation can use the relative marked-site laws above. It would be invalid to condition on a random pivotal site and quote an unconditional bad-event probability without either device. The remaining work must verify all-recolorings agreement, repeated sites and times, the hereditary closed H state, common mark-time synchronization for J1, and consistency when h and then delta decrease. The two-replica extension then needs the same annotated tests on shared geometry. B151 supplies the final cutoff removal only after that fixed-delta construction converges.

Route B has a different precise debt. GPS pivotal Proposition 3.1 couples exterior-face laws conditioned also on U_Theta=tau; Lemma 4.7 compares conditional expected counts for tau=0 and tau=1 by color reversal and controls failure contributions while retaining the crossing-bit conditioning. Equations (4.21)–(4.27) need that coefficient comparison, not just a four-arm probability. In Poisson geometry a valid version must carry the random revealed geometry and Palm insertion in these conditional laws, and bound conditional count errors on failed couplings. The amplitude companion's signed transfer/cancellation is not by itself this positive conditional-count identity. No such beta-versus-betahat proof is supplied here. Hex positivity, annular concentration and L2 arm comparability are insufficient substitutes. Failure to complete either route is not a counterexample to the target.

## Disposition

Paid new partials: explicit same-site pattern extraction and shared overlap clocks at finite-quad scope; the screened replacement for the false exact inclusion; and relative normalized mass estimate (4) for outer separation failures. Unpaid: the boundary-quad witness implication and marked-network stability/consistency, hence fixed-delta important-network convergence and the full H-valued common-time J1 process. No strong Markov/Feller assertion, exceptional-time result, interface-path topology or sharp rate is made. Eight accepted findings remain eight, two remain. There is no claim of a literature gap or worldwide priority.
