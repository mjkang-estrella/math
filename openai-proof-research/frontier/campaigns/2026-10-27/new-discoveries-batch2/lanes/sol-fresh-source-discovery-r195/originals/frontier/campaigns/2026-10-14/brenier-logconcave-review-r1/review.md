# Independent review of Theorem LC, round 1

Myeongjin Kang; no affiliation. Original review prose: CC BY 4.0; original review code: MIT. Third-party inputs retain their rights and are private reading material.

**Mathematical verdict: PASS_FULL_LC. Contribution verdict: TECHNICAL.** These are separate verdicts. The unchanged proof establishes the frozen LC claims, including the stated constant, under the entire stated source class. I found no mathematical defect requiring a repair. Relative to the accepted pinned source proof and established transport operations, however, the extension does not require a substantial new operation. In particular, the purportedly new weighted interpolation can be obtained directly, with better constants, by layer-cake integration of the pinned interpolation lemma. This review does not authorize counting or publication. Campaign count remains **4/10**.

## 1. Object audited and interpretation of the verdict

The object is the complete unchanged `inputs/author/candidate.md`, SHA256 `4b75256d320e8cab0e87c1476b442178ff623bcebb2002410c676b8f2da449d9`, with its referenced proofs in the nine pinned source files. The frozen scope is retained verbatim at `inputs/author/original-scope.md`, SHA256 **`d14eb78f156fda839a910797953d27445492625839dd6d0e2d22a2059fda29b4`**. The author seal was independently checked against the parent-supplied anchor **`4a57c056b08c74d48fd78bd4152e3eb0bfddefe83adbd0c03e98fdd53c6786e8`** before snapshotting its exact 33 members. No author code or numerical experiment was executed.

For clarity, the scope is: every integer d>=2, every compact convex full-dimensional K, every probability rho=f dx with finite-valued Borel f positive and log-concave on int K and zero off K, arbitrary boundary values, every nonempty compact Y, and R,L>=1 enclosing K,Y. With Lambda=sup(int K) f and P_K the sum of coordinate projection areas, the claimed squared constant is

    C_LC^2 = 18 d (1+sqrt(162))^2 R^2 + 52 L^2 Lambda P_K.

The conclusions are unique quadratic optimal plans induced by unique rho-a.e. maps for every target in P(Y), the map estimate C_LC W2^(1/3) for every pair of targets, and class-level sharpness. The scope file lists map uniqueness; the candidate also claims plan uniqueness, and this stronger assertion was checked. No positive lower density bound, target mass bound, smoothness, strict convexity, per-source sharpness, d=1, or unbounded source support is inserted.

I accept upstream theorem truth at openai/math revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, as instructed. I read the actual source bodies, not just their authenticated identities. The uniform-source theorem statements are not applied to weighted rho. Sections 2–8 below reconstruct the weighted substitutions against the source proofs. The alternative in Section 9 is contribution evidence, not a repair used to rescue an incomplete original proof. This is a mathematical reading review, not a formal verification certificate.

## 2. Density bounds, boundary values, and sections

Candidate Section 2 is valid. A finite concave function phi=log f on the open convex domain int K is continuous there and has a supergradient p at an interior point x0. Its supporting affine upper bound gives

    phi(x) <= phi(x0)+p·(x-x0) <= phi(x0)+2R|p|.

Thus Lambda is finite even when f tends to zero at the boundary or has no boundary limit. Positivity inside and zero volume of the convex boundary imply equivalence of rho-null and Lebesgue-null measurable subsets of K. In particular, positive cell mass implies positive volume, and tie hyperplanes are rho-null.

The source `cells:calculus` proof's segment-extension argument applies to every positive-dimensional affine section meeting int K: relative interior of the section equals its intersection with int K. Its relative boundary is null in that affine space. Coordinate projection maps take int K onto the interior of the projected body, so exceptional coordinate fibers not meeting int K have a null set of prefixes. These facts establish F3 and the Fubini uses; they do not assume a smooth boundary.

There is one harmless measure-theoretic wording point in candidate Section 3: Lambda bounds f on int K, not necessarily its arbitrary representative on partial K. The domination in the volume difference quotients is an a.e. bound. For a sequence of nonzero perturbations, pullbacks of partial K are null in the (z,t) volume coordinates, and a countable union removes them. For moving face integrals, every admissible equality plane meets int K, so its intersection with partial K is surface-null, again for each member of a sequence. Equivalently, use f 1_(int K) throughout these integrals. This changes neither any volume integral nor any of the relevant face integrals. It is the standard a.e. interpretation of the existing argument, not an added source assumption or a repaired statement.

The same observation resolves all fiber-boundary concerns in Lemma 4.1: the construction uses int U and int V, and their positive-volume interiors lie inside int K. Endpoints on boundaries carry no conditional mass. No derivative or prescribed trace of f at partial K is used anywhere.

## 3. Weighted cell calculus and prescribed masses

I compared candidate Propositions 3.1–3.2 with the complete `cells.tex`, especially the product-indicator difference quotient, graph identification of moving planes, connectivity, and implicit-function proof.

At a positive-mass distinct-site configuration, each cell contains a strictly active point in int K. Points in cells i and j give opposite signs of their affine difference, so **every** H_ij crosses int K. Coincident H_ij and H_ik would put three affine functions on a line with one between the others, preventing that middle function from being strictly maximal. Thus the triple-equality exceptional sets are surface-null.

For a continuous test a(x)=1 or x_k, replace the source volume integral by

    I_i = integral a(x) f(x) 1_K(x) product_(j!=i) 1_{ell_ij(x)>=0} dx.

Telescope the product, set x=z+h t n_ij in each changed factor, and cancel h against the difference quotient. The support in z,t remains bounded. Off the section-boundary and triple-equality exceptional sets, the unchanged indicators converge and f converges by interior continuity (or the K indicator is eventually zero). Integrating the changed indicator in t gives

    (r_i-r_j+z·(v_i-v_j))/|y_i-y_j|.

Dominated convergence consequently gives exactly the candidate's weighted DM and DB formulas, with the same coefficients b_ij in the mass-site and moment-intercept terms. The opposite direction gives two-sided derivatives. For varying configurations identify H_ij with a graph over its limiting plane; maps and surface Jacobians converge uniformly on a bounded region. The same null-set argument and bound establish continuity of every coefficient, including x_k x_l moments. Mass continuity makes the positive-mass parameter region open. Thus the asserted joint C1 regularity really holds for nonsmooth K and boundary-vanishing f.

For connectivity the generic segment between strictly active interior points avoids all triple equality sets. Each active-index change crosses an open face disk inside int K. Since f is continuous and positive on a smaller compact disk, its face integral is positive. Connectivity and symmetry give q·Gq=sum_(i<j) g_ij(q_i-q_j)^2, kernel the constants, and range H0={sum z_i=0}.

For prescribed masses m_i>0, the convex objective on H_m={sum m_i c_i=0} is bounded below by max c_i-R max|y_i|. Positivity of all m_i makes this coercive on H_m. Differentiation under the maximum is valid by null ties and bounded difference quotients, giving gradient M-m. A constrained minimizer has this vector proportional to m, and its zero coordinate sum makes it zero. At a solution, G:H_m->H0 is an isomorphism. The implicit function theorem gives a locally isolated C1 branch. Two distinct minimizers would have an entire minimizing segment, contradicting local isolation. This proves existence, uniqueness, and C1 dependence without a quantitative inverse bound. N=1 is immediate.

Candidate Lemma 3.3 refers to `cells:optimality`, located in **sharpness.tex**. Its entire plan argument transfers: merge repeated slopes, use null hyperplane ties, integrate x·y+c(y)<=u(x), and observe that any equality plan is supported on the unique maximizing slope over rho-a.e. x. It needs no uniform density.

## 4. Weighted triangular midpoint coupling

I checked the complete triangular construction and backwards substitution in source `moments:midpoint` against candidate Lemma 4.1, not merely its determinant heuristic.

For compact convex positive-volume U, D_k=proj_k(int U) is open convex. For every prefix in D_k its fiber has a nonempty open part in int U, so p_k>0. For k<d, the fiber boundary is null because this affine fiber meets int U. As a prefix tends to an interior prefix, the integrand converges off that boundary, with a common bounded-support a.e. bound Lambda. Therefore p_k is continuous on D_k. For k=d this is interior continuity of f. Fiber integrals are Borel on the full domain.

For each previously chosen interior prefix, p_k/p_(k-1) integrates to one by the definitions and Fubini. It is positive and continuous on a bounded open interval. Its CDF is strictly increasing there from zero to one. Its inverse is C1 in the active quantile variable, with derivative p_(k-1)/p_k. Borel dependence follows by testing CDF inequalities at rational values; no differentiability in earlier prefixes is asserted or required. Successive conditioning gives the desired normalized restriction law. The diagonal products telescope exactly to alpha/f(X) and beta/f(Z).

The midpoint H=(X+Z)/2 is in int K and is triangular, with positive C1 derivative in each last active variable. Coordinate AM–GM gives

    product partial_k H_k >= sqrt(alpha beta)/sqrt(f(X)f(Z))
                              >= sqrt(alpha beta)/f(H).

The last inequality has the correct direction. Substitution first in s_d, enlarging that image interval to R, then in s_(d-1), and so on, proves

    integral G(H) product partial_k H_k ds <= integral G dx

for nonnegative Borel G. All earlier derivative factors depend only on earlier parameters, so Tonelli applies. The factors are Borel by their formulas, and can grow near the cube boundary without obstructing one-dimensional substitution. Apply this to G=g f. The result is exactly sqrt(alpha beta) Law(H)<=rho, with no lost normalization or extra constant. Positivity of alpha,beta follows from positive volume, interior positivity, and null boundaries. This proves M for all U,V in the frozen scope.

## 5. Stationary moment estimate, constant 162

Candidate Section 5 is abbreviated, but its reference to the full source proof pays the following complete argument under the verified substitutions.

Fix the configuration and q. For sufficiently small s>0, the cells P_i^± at c±sq have masses alpha_i,beta_i>0 by continuity. Their weighted restrictions admit the Section 4 coupling. Averaging the two cell inequalities cancels ±s(q_i-q_j), so its midpoint lies in P_i. With gamma_i=sqrt(alpha_i beta_i), D_i=E|X_i-Z_i|^2, and A_i^±=E Phi(X_i or Z_i), the domination gives

    sum gamma_i[(A_i^-+A_i^+)/2+D_i/4]
      <= integral Phi drho
       = (1/2) sum(alpha_i A_i^-+beta_i A_i^+),

where Phi=R^2-|x|^2 is nonnegative and at most R^2. Both perturbed families partition K modulo null ties; this is the weighted partition identity, replacing the source's volume normalization.

Write delta_i=alpha_i-beta_i, A=sum gamma_i D_i, and B=sum delta_i^2/gamma_i. The exact gap identity and Cauchy–Schwarz yield

    (alpha+beta)/2-gamma
       = delta^2/[2(sqrt(alpha)+sqrt(beta))^2] <= delta^2/(8 gamma),
    |A_i^--A_i^+| <= 2R sqrt(D_i),
    A/4 <= R^2 B/8+(R/2)sqrt(A B)
         <= R^2 B/8+A/8+R^2 B/2.

Hence A<=5R^2 B, including zero cases. Meanwhile

    |Delta B_i| <= R|delta_i|+alpha_i sqrt(D_i).

At this fixed finite configuration we can decrease s until alpha_i,beta_i,gamma_i all lie in [M_i/2,2M_i]. Then alpha_i^2/M_i<=8 gamma_i and B<=2E, where E=sum delta_i^2/M_i. Thus

    sum |Delta B_i|^2/M_i <= 2R^2 E+16A <= 162R^2 E.

Divide by (2s)^2 and use the already proved weighted C1 derivatives; both differences have the same minus sign, which disappears after squaring. This is the exact stationary moment assertion. The smallness threshold for s may depend on q and the configuration's smallest mass, but no such threshold or inverse-Laplacian constant survives in 162. The proof does not require a uniform lower mass or density bound.

## 6. Fixed-mass moving sites and linear potential control

I read all of source `finite_stability.tex`, including the endpoint argument. Candidate Proposition 6.1 correctly reuses it with the preceding weighted calculus and moment estimate.

Delete zero coupling weights and merge identical endpoint pairs in an optimal finite target coupling sum m_i delta_(y_i^0,y_i^1). Optimality under a two-pair swap gives (y_i^0-y_j^0)·(y_i^1-y_j^1)>=0. Since endpoint pairs are distinct, expansion of the squared difference shows y_i(t)=(1-t)y_i^0+t y_i^1 are distinct for every 0<t<1, even if slopes collide at t=0 or 1. They stay in B(0,L), which suffices; they need not stay in Y.

Choose the C1 intercepts with fixed masses m_i and sum m_i c_i(t)=0. Let r=c'(t), v_i=y_i^1-y_i^0, and w=W2(mu,nu). Then sum m_i r_i=0 and sum m_i|v_i|^2=w^2. Differentiating the fixed masses and using the exact weighted face coefficients gives, for every q,

    sum r_i DM_i[q,0] = -sum v_i·DB_i[q,0].

Choose q with DM_i[q,0]=m_i r_i; the range statement permits it. Weighted Cauchy–Schwarz and Section 5 give E_r<=sqrt(162) R w sqrt(E_r), where E_r=sum m_i r_i^2. Thus ||r||_(ell2(m))<=sqrt(162) Rw. There is no bound on q and none is needed.

For u_t=max_i(x·y_i(t)+c_i(t)), local time Lipschitz continuity holds on compact subintervals of (0,1). At a strict maximum its derivative is x·v_i+r_i. Null ties at each time and Fubini establish this for a.e. (t,x). Consequently

    ||partial_t u_t||_(L2(rho)) <= (1+sqrt(162)) Rw.

The fundamental theorem of calculus and Minkowski give the corresponding time Lipschitz estimate in L2(rho). Individually |c_i'(t)|<=sqrt(162)Rw/sqrt(m_i), so each intercept has finite endpoint limits. This mass-dependent auxiliary estimate is only used for existence of limits, not in the uniform potential bound.

Finite maxima converge uniformly on K at endpoints. Merge repeated endpoint slopes keeping the largest intercept. Except on the finite union of hyperplanes there is a unique maximizing endpoint slope, and approaching interior maximizers must converge to it: a contrary fixed-index subsequence contradicts the strict gap. Their slope laws converge by bounded convergence to the original marginal targets, including all split masses at colliding sites. Weighted finite optimality then identifies the endpoint gradients. Extending the time inequality to 0 and 1 proves exactly P with coefficient (1+sqrt(162))R. N=1 and w=0 cause no exception.

## 7. Audit of the original slice proof for every h>0

Candidate Lemma 7.1 is correct on its own terms; the alternative in Section 9 is not needed for this verdict. Fix a coordinate line meeting int K. Its slice has interior (a,b), with g positive continuous log-concave there and bounded by Lambda. Restrictions of the two potentials are convex and L-Lipschitz.

If b-a<=h, both permitted difference sets are empty and the entire integral is bounded by 4L^2 Lambda h. Otherwise the function psi(t)=log g(t+h)-log g(t) is nonincreasing on (a,b-h): concavity makes fixed-length chord slopes nonincreasing. The nonnegative set J+ is an initial interval; write its right endpoint as tau in [a,b-h], allowing empty or full. The strict negative set shifted by h is exactly J-=(tau+h,b), up to endpoints. Equality plateaus belong to J+, including a whole interval of psi=0; the strict inequality in J- prevents double counting. In particular J+ and J- are disjoint, and the remaining E has length at most h. All sets are measurable slices of the candidate's Borel sets; measurability of a selected tau across prefixes is unnecessary.

For a.e. allowed t, each forward or backward convexity defect is between zero and 2L. For the forward direction set phi=u'+L>=0. Weight monotonicity gives

    delta+ g <= (phi(t+h)-phi(t))g(t)
              <= phi(t+h)g(t+h)-phi(t)g(t).

Integrating over (a,tau) gives exactly

    integral_tau^(tau+h) phi g - integral_a^(a+h) phi g <= 2L Lambda h.

This cancellation is valid when the two intervals overlap or tau=a: they are signed integral identities, not claims of disjoint intervals. The backward direction uses phitilde=L-u'>=0 and g(t)<g(t-h), giving

    integral_tau^(tau+h) phitilde g - integral_(b-h)^b phitilde g
       <= 2L Lambda h.

Again overlap does not matter. Therefore each of the four squared defect integrals is at most 4L^2 Lambda h, since delta^2<=2L delta. Translates of derivative-null sets are null, so shifted derivative expressions are legitimate.

For F=u0-u1, translate the F(t±h)^2 terms only toward the larger weight, exactly as in the candidate. J++h and J--h each lie inside (a,b), with overlap contained in [tau,tau+h]; their multiplicity is at most two. The unshifted sets are disjoint. Applying (A-B)^2<=2A^2+2B^2 therefore bounds the two quotient-square integrals by 6h^-2 integral F^2 g.

Finally use the exact identities for F' in terms of a quotient and two defects, and the three-term square bound. This gives 18h^-2 integral F^2g+48L^2 Lambda h on J+ union J-. E adds at most 4L^2 Lambda h. Thus (7.1) has exactly **18 and 52**. For short slices the simpler bound above implies the same inequality; the long-slice defect calculation is unnecessary there. No boundary derivative of g or lower bound on g is used.

Fubini over coordinate prefixes costs at most A_j in direction j. The exceptional lines missing int K have null prefix set by Section 2. Full gradients agree a.e. with coordinate derivatives by the source's convexity argument in `gradient:interpolation`; absolute continuity transfers this to rho. Sum over j to get G, with coefficient 18d on the potential term and 52L^2 Lambda P_K on h. Large h, monotone densities, constant densities, and long flat maxima are all covered.

## 8. Full targets, optimal plans, constant, and sharpness

For finite targets w>0, insert P into G and set h=w^(2/3). The two terms are respectively

    18d(1+sqrt(162))^2 R^2 w^(2/3),
    52L^2 Lambda P_K w^(2/3).

Their sum is exactly the frozen C_LC^2 w^(2/3), so taking a square root gives LC-b. For w=0 the normalized pair in P has zero difference in L2(rho), and G with h down to zero gives equal gradients.

I compared candidate Section 8 to the complete source `gradient:extension` and final `main:stability` proof. For finite epsilon_n-nets in Y, first-closest-point selection Q_n is Borel and W2(lambda_n,lambda_m)<=epsilon_n+epsilon_m. The finite estimate makes T_lambda_n Cauchy in L2(rho). A subsequential a.e. limit S takes values in closed Y; continuous-test convergence proves S#rho=lambda. Zero-mass sites are deleted, so the finite positive-mass contracts are respected.

Normalize the individual finite potentials at a fixed x* in K. Slopes bounded by L give a uniform Lipschitz and oscillation bound on K. Arzela–Ascoli supplies a uniformly convergent subsequence to convex u. Along a common full-measure set, finite supporting inequalities hold simultaneously for all z in K and pass to u(z)>=u(x)+S(x)·(z-x). The restricted conjugate u*(y)=max_(z in K)(z·y-u(z)) is continuous and bounded on Y. Fenchel inequality holds for every (x,y), with equality on the graph of S. Its integrated upper bound on correlation proves optimality **against every transport plan**, since the marginal integrals of u and u* are fixed.

Any optimal plan must have zero nonnegative Fenchel gap. At a.e. interior x, all coordinate partials of u exist and force every supporting slope to equal the same gradient, by testing ±coordinate displacements. The source marginal is absolutely continuous and partial K is null, so the equality plan is concentrated on this unique graph. Thus both the optimal plan and map are unique. This justifies LC-a and the candidate's stronger plan claim without a hidden regularity theorem for rho.

Use common Q_n for two targets. Pushing any coupling through (Q_n,Q_n) gives W2(mu_n,nu_n)<=W2(mu,nu)+2epsilon_n. Strong L2 convergence then passes LC-b to arbitrary Borel targets. No convexity of Y is needed; the enclosing ball suffices during finite site motion. Singleton Y is included.

For LC-c, the source's `sharpness:exponent` contract is exactly the uniform cube in every fixed d>=2 with three positive atoms. This source belongs to H. The family has W2=a^(3/2)/2 and map distance sqrt(a)sqrt(1+a^2)/2. The ratio for exponent alpha>1/3 diverges as a^((1-3alpha)/2). Fix enclosing radii once for that cube. This establishes only the claimed class obstruction, not sharpness for each fixed nonuniform f. No d=1 or unbounded-support extension has been inferred.

## 9. Separate contribution triage

The contribution verdict is **TECHNICAL**, not DUPLICATE: the bounded primary screen below did not locate an already stated theorem with the complete LC class and sharp W2 exponent. It is also not SUBSTANTIAL merely because the theorem class is broader or the exponent improves earlier statements. The relevant question is which operations remain new relative to source 374 and standard antecedents.

**Midpoint domination is a standard transport consequence.** One must distinguish the Prékopa set-mass inequality from the required domination of a particular midpoint law. The former alone does not construct that law. However, the pointwise change-of-variables machinery in McCann's proof does supply it routinely. For transport T between p0=f 1_U/alpha and p1=f 1_V/beta, let H_t=(1-t)id+tT. At a.e. regular source point, the Jacobian identities and determinant concavity give

    p_t(H_t(x)) <= p0(x)^(1-t) p1(T(x))^t
                 <= f(H_t(x))/(alpha^(1-t) beta^t).

The second step is just log-concavity of f. At t=1/2 this is M. This reasoning uses the pointwise Jacobian argument underlying McCann's Lemma 2.1, Theorem 2.2 and §4, **not** an unsupported application of his unweighted global Lq theorem as if it already stated a weighted bound. The candidate's triangular derivation is a valid direct version of the same established operation. Its elementary AM–GM step is not independent mathematical novelty. Prékopa's Theorems 2–3 and their proofs explain the corresponding restriction/log-concavity mechanism at the level of mass inequalities.

**Weighted interpolation has a direct layer-cake reduction.** Here is a complete operation-level comparison, stronger than title matching. For 0<t<Lambda let

    O_t={x in int K: f(x)>t},    K_t=closure(O_t).

Interior continuity and log-concavity make O_t nonempty open convex. Thus K_t is a full-dimensional compact convex subset of K; K_t\O_t is null. Moreover P_(K_t)<=P_K by inclusion of every coordinate projection. Restrict the same u0,u1 to K_t and multiply the pinned `gradient:slice-bound` by |K_t| to obtain

    integral_(K_t)|grad F|^2 dx
      <= 12d h^-2 integral_(K_t)F^2 dx +28L^2 P_(K_t) h.

Integrate in t from 0 to Lambda. Tonelli and the layer-cake identity give

    ||grad F||_(L2(rho))^2
      <= 12d h^-2 ||F||_(L2(rho))^2 +28L^2 Lambda P_K h.

Null level-set boundaries can be discarded separately for each t before Tonelli; equality with the measurable open-level integrals also avoids any issue about measurable projection areas. If desired, simply replace P_(K_t) by P_K before integrating. This proof needs only bounded, continuous, quasi-concave interior density for this particular operation. It directly pays the interpolation input with **12/28 instead of 18/52**. It does not replace rho's transport maps by a mixture of maps, and it does not assert that the *full* uniform-source stability theorem can be integrated. It is only an integration of a fixed-function inequality.

Consequently the direction-switching construction, though correct and useful, is not a necessary new obstacle for the LC extension. The older Delalande–Mérigot interpolation proof already supplies the one-dimensional convex-function and integral-geometry antecedent. Source 374 supplies the explicit h-form used in this reduction.

**The remaining operations are source adaptations.** The moment testing, geometric-mean gap, 162 algebra, fixed-mass site path, dual graph-Laplacian test avoiding inverse norms, endpoint limits, and target approximation are all in source 374, with the same quantitative logic. Weighting requires careful a.e. continuity and positivity checks, which Sections 2–8 verified; it does not require a new estimate once standard weighted midpoint domination is recognized. The new source class and boundary-vanishing examples therefore constitute a valid technical extension, not evidence of a substantial independent mechanism. The cube obstruction is inherited unchanged.

The primary stability statements below supply context rather than a duplication verdict. In particular, W1^(1/4) does not imply W2^(1/3) by W1<=W2, and a uniform-source statement cannot simply be invoked for weighted rho. Conversely, failure to find LC in a search is no worldwide novelty certificate. These distinctions are part of the TECHNICAL verdict.

## 10. Primary evidence, reading extent, and limitations

Exact retained primary bytes, versioned URLs, sizes, and SHA256 values are recorded in `inputs/primary/retrieval.json` and the input manifest. `primary-reading.md` gives specific actual reading extents and comparison records. The source-374 nine-blob match to the complete 13,223-entry preprints catalogue is in `inputs/source-authentication.json`.

The strongest contribution evidence is the explicit reduction in Section 9, independent of any worldwide priority inference. The external screen included actual theorem/proof reading of McCann 1997, Prékopa 1973, Delalande–Mérigot v2, Letrouit–Mérigot v3, Mérigot HAL v1, Wang–Wang v1, and selected relevant results in Ruan v1 and Ford v1. It did not inspect every article cited by those works. No unread abstract or citation-only entry is promoted to a primary mathematical premise. All external results serve comparison only; the original proof PASS in Sections 2–8 rests on its own checked arguments and the accepted pinned source contracts.

There is no open mathematical objection and no required repair to the audited candidate. An optional editorial improvement would make the a.e. density domination explicit and write out the moving-site reconstruction instead of the compressed list. The stronger layer-cake bound is a review deduction, not a change to the frozen original constant or scope.

## 11. Artifact checks and handoff

All 33 author files were authenticated before reading/execution decisions and retained unchanged inside this directory. All nine source Git blobs were independently recomputed and matched against the complete catalogue. Original author membership and hashes are checked again by the read-only review verifier. Mutable campaign context is snapshotted locally and is not compared to future live ledger or parent state.

The only executed stored code consists of the inspected original review verifier and its guard, authenticated by separately captured code hashes before use. The external Python audit guard rejects writes, mutation calls, subprocesses, and network events during verification. The checks concern exact bytes/membership, scope, verdict metadata, source identities, and unchanged author originals. Negative controls exercise a wrong external seal anchor, an altered frozen-scope byte view, an unlisted member view, and a counterfeit contribution/count metadata view. They are explicitly integrity controls, not mathematical tests. See `verification-controls.json` and `guard-receipt.json` for the measured results and their pre-seal/final-phase distinction.

No loose numerical grids were rerun; they cannot establish universal LC. No staging, commits, shared-file edits, nested agents, publication, uploads, external messages, manuscript, or Lean package were made. Parent integration and decisions remain separate. The detached SHA256 of this review's `seal.json` is reported externally in the final response; the seal binds the exact owned input/output membership and sizes/hashes without a future live-ledger dependency.
