# Recovery r4: FULL strict-BV continuity

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT. Third-party inputs remain private with original rights.

**Final disposition: UNRESOLVED. Full B is neither proved nor disproved. No substantial complete result is nominated.**

For clarity, define A_r g(x)=(pi r^2)^(-1) integral_{B(x,r)} g and Mf=sup_{r>0} A_r|f|, with centered Euclidean disks. The unchanged full target is:

    FOR EVERY real f,f_j in BV(R^2),
    ||f_j-f||_1 ->0 and |Df_j|(R^2)->|Df|(R^2)
    imply |D(Mf_j)|(R^2)->|D(Mf)|(R^2).                  (B)

BV inputs are globally integrable and have finite Euclidean derivative variation. There are NO sign, support, smoothness, jump, Cantor or strong derivative-measure restrictions. Output global L1 is not asserted. The pinned source gives outputs in L2 intersect BVloc with globally finite variation. The positive result sought throughout this report remains B; auxiliary deductions below are not replacement targets.

## Stage 0: scope and authenticated recovery

The full B of original-scope.md is unchanged. In particular every real globally integrable planar BV sequence converging in L1 and total Euclidean variation is included. Outputs have globally finite variation and are locally integrable; global L1 is not required. U-sharp remains the actual target. r3 supplies no new mathematics.

Read project AGENTS.md. Independently authenticated r2 seal SHA256 2084b4bf4268783bb0df3421887d9f7f08079a919cb80715283031d24691337d, its two manifests and all 94 inventoried files before executing any package code; copied its entire sealed package privately. This is byte authentication, not mathematical proof review.

Next stages: critically inspect tail/positive-radius arguments; study actual directional source interface; attempt full sharp calibration and adversarial signed layers. Any new claim below must distinguish proof from an attempted route.

## Stage 1: critical recheck of r2 support

R2 verifier replay passed (94 files, both receipts); not an independent mathematical PASS. The full candidate has been read.

The tail proof survives the following checks: radial W11 traces are continuous as L1(S1)-valued maps on compact positive annuli for each fixed center (polar change of variables and radial derivative integrability). Thus the circle integral has a continuous version and the radial stationarity identity extends to every positive optimizer. The spatial convolution with the disk of the L1 gradient is continuous, so touching is legitimate. On the cutoff equality set Sobolev locality applies, and the remaining optimizers exceed |x|/2; their contribution integrates as |x|^-3. The BV passage is LOWER semicontinuity on an open tail, so contains no hidden upper passage. Signed inputs enter only through |D|f|| <= |Df|. Strict input variation measures are tight. No gap found in U-tail.

The fixed-positive-radius proof also survives: a finite atomless planar measure charges at most countably many distinct circles, since different circles meet in at most two null points. A BV derivative has no atom by the curl test given in r2. Outside the countable exceptional centers, ALL radii have zero boundary mass simultaneously. Convolution gradients are differentiable at these centers by continuity of the measure of moving disks, and domination |D|f_j|| <= |Df_j| plus narrow convergence of |Df_j| gives convergence for moving disks. Optimizers have a positive lower and finite pointwise upper radius. Dominated convergence on compact sets plus the tail bound yields global L1 gradient convergence. The zero limit is handled by the pinned norm bound. No use of strictness of |f_j| is needed.

These rechecks are recorded proofs of the interface points, not a new result nomination. The fine signed polarization arguments of r2 concern Df_j, and remain inapplicable directly to D|f_j| at sign-crossing layers.

## Stage 2: source operations and attempted sharp calibration

Read local.tex lines 1–190, prices.tex lines 1–260, labels.tex lines 1–180, extension.tex lines 1–230, assembly.tex lines 1–190 from the frozen pinned source. The local unfavorable-direction estimate charges only discounted cancellation errors for locally maximizing radii. Its vectors need only have positive projection on the test direction; it is not intrinsically a fixed-width cone estimate. However the price decomposition has same-level bad-root charges, and the full assembly also has endpoints, baselines and spatial derivatives. Replacing their total C bound by coefficient 1 is not justified.

Attempt: if gradients at vanishing winners could be shown asymptotically aligned with the local input polar (or its appropriate signed-jump output polar), weak convergence of output vector derivatives would calibrate their variation without needing an input-to-output constant 1 estimate. At diffuse points with nonzero input value, the expected polar is sgn(f) times the input polar. At a sign-crossing jump it depends on the two absolute traces and the competing maximal baseline; the input polar alone cannot calibrate it. This is a route, not a proved transfer lemma.

Unpaid even for the unsigned cone route: summing bad-root mass over arbitrarily many scales is not bounded by its single-scale smallness. Fine scalar and neighboring deficits do not by themselves bound that sum for a FIXED prescribed calibration. An arbitrary small negative/transverse derivative remainder cannot simply be passed through a nonlinear maximal envelope with a claimed C times remainder bound: no such BV difference bound has been proved.

## Stage 3: one-valley rigidity and a varying-baseline estimate (proved auxiliary deduction)

This is NOT B, not a result nomination, and not a globally integrable planar input. It strengthens the exact model calculation to clarify, rather than assume away, a remaining obstruction.

Let q be any bounded nondecreasing real function with limits -A and B, where A,B>=0. Set h=|q| and

    k_r(s)=2/(pi*r)*sqrt(1-s^2/r^2)_+,
    u_t(s)=sup_{0<r<=t} (k_r*h)(s),       t>0.

No absolute continuity of q is assumed. Its jump and Cantor parts are included. Then u_t is quasiconvex: every sublevel set is an interval. Consequently it decreases and then increases, in the a.e./BV sense, with endpoints A,B. If m_t=ess inf u_t, then

    Var(max(c,u_t)) = max(c,A)+max(c,B)-2 max(c,m_t)       (3.1)

for every real constant c. In particular, if B>=A and c>=A, max(c,u_t) is nondecreasing and

    Var(max(c,u_t))=(B-c)_+.                             (3.2)

Thus the midpoint baseline used in r2 is stronger than needed for this exact model. This assertion uses log-concavity of the disk marginal; it does not assert this stronger threshold for every merely unimodal kernel.

Proof. Write Dh=P-N, where P=D(q_+) and N=-D((-q)_+). These are finite nonnegative measures of masses B,A, with supp N<=z<=supp P for a zero-crossing z. An atom in both P,N at z is permitted. For each r, F_r=k_r*h is C1 and

    F_r'=p_r-n_r,      p_r=k_r*P, n_r=k_r*N.

Continuity of k_r and finiteness of P,N imply continuity of its distributional derivative, hence C1. The kernel is log-concave on (-r,r):

    (log k_r)''(s)=-(r^2+s^2)/(r^2-s^2)^2 <0.

Extended by zero, it obeys the order-two kernel inequality, for s1<s2 and a<=b,

    k_r(s2-b) k_r(s1-a) >= k_r(s1-b) k_r(s2-a).         (3.3)

If the right side is positive, all points on the left lie in the support interval, and concavity of log k_r gives (3.3) by comparing increments over s2-s1. If the right side is zero the inequality is immediate. Integrating (3.3) against N(da)P(db) gives

    p_r(s2)n_r(s1) >= p_r(s1)n_r(s2).                    (3.4)

It is therefore impossible that F_r'(s1)>0 and F_r'(s2)<0: then p1>n1 and n2>p2, contradicting (3.4). Thus its continuous derivative has all strictly negative values before all strictly positive values, allowing zero intervals, and F_r is quasiconvex. This also covers a zero mass P or N. A supremum of quasiconvex functions is quasiconvex because its sublevel sets are intersections of intervals. Since radii are bounded by t, the endpoint limits of u_t are A,B uniformly over the radius family. A bounded quasiconvex function on the line is monotone on each side of a minimum interval; its distributional variation is the endpoint sum minus twice its essential minimum. Apply this to max(c,u_t) to obtain (3.1). If c>=A and B>=A its left endpoint is also its lower bound c, forcing nondecrease, which proves (3.2).

Here is an exact varying-baseline consequence. Assume B>=A. Let b be any bounded real BV function on R (finite distributional variation, finite limits b_-,b_+; global integrability is NOT required for this model). Let H=max(u_t,b), and ell=ess inf b. Then

    (DH)^-(R) <= (A-ell)_+ + (Db)^-(R),                  (3.5)
    Var H <= max(B,b_+)-max(A,b_-)
                +2(A-ell)_+ +2(Db)^-(R).                (3.6)

If b>=A a.e., the first term in (3.5) vanishes. If b>=A-epsilon, the model's unfavorable variation costs at most epsilon plus the unfavorable variation of the baseline. Reflection gives the A>=B version.

To prove (3.5) without an invalid BV equality-set chain rule at jumps, put c=min(A,ell) and v=max(c,u_t). The negative mass of Du_t carried ABOVE c on its decreasing branch is at most A-c. Precisely, Var^-(v)<=A-c, because u_t is quasiconvex with left endpoint A, and clamping below c truncates that single descending branch. Since b>=c, H=max(v,b). For arbitrary 1D BV functions v,b,

    Var^-(max(v,b)) <= Var^-(v)+Var^-(b).                 (3.7)

Indeed for any x<y, (max(v(x),b(x))-max(v(y),b(y)))_+ is at most (v(x)-v(y))_+ +(b(x)-b(y))_+. Sum along ordered partitions and take the supremum using one-sided representatives; this gives (3.7), including jumps and Cantor parts. Hence (DH)^-<=A-c+(Db)^-, which is (3.5). Finally Var H=H(+infinity)-H(-infinity)+2(DH)^-(R) gives (3.6). No derivative locality assumption is needed.

The relevance is exact: the old signed-valley model is robust to an arbitrary BV baseline bounded just below the lower absolute trace. The remaining planar problem is NOT solved by (3.5): strict planar sequences need not be one common monotone profile; controlling tangential geometry or reducing to such profiles through the maximal operation is still unpaid. In particular the estimate is not applied to a spatial slice of Mf_j without establishing that its disk averages have this one-dimensional convolution representation.

## Stage 4: a concentration localization for the ORIGINAL full sequence

Here is a further proved supporting deduction, with ALL input quantifiers of B retained. It is a constant-C localization, explicitly not U-sharp and not a substantial-result nomination.

Let f_j -> f strictly as in B, let mu=|Df|, and let nu be any vague cluster of nu_j=|D(Mf_j)|. Then, for every Borel Lebesgue-null set E,

    nu(E) <= C mu(E).                                    (4.1)

In particular the singular part satisfies nu^s <= C |D^s f|. When the original limit f is W11, every output-variation cluster is absolutely continuous. This does NOT give equiintegrability of the approximating output densities or coefficient one for their a.c. limits. Staircase oscillations can retain a.c. excess in a cluster; this deduction does not settle them.

First extend the source signed capped estimate to any real v in BV(R2):

    |D(S_t v)|(R2) <= C |Dv|(R2),
    S_t v=sup_{0<r<=t} A_r v.                            (4.2)

For a fixed band [a,t] with dyadic ratio, mollify v. Its derivative norms are at most |Dv| and its averages converge uniformly by the L1/(pi a^2) estimate. Variation lower semicontinuity proves the band bound; the limit is Lipschitz by the BV translation estimate. Then let a=2^-nt down to zero. Signed band absolute values are bounded by M|v| in L2 by planar BV embedding and the L2 maximal inequality, so monotone convergence of the envelopes gives local L1 convergence. Lower passage gives (4.2). This does not claim strict convergence of the band output variation.

For a square Q of side t, put c_Q=average_{5Q} v, v_Q=chi_Q(v-c_Q), where chi=1 on 3Q, compactly supported in 5Q, and |grad chi|<=C/t. The source square Poincare inequality extends by mollification and lower passage to

    |Dv_Q|(R2) <= C |Dv|(5Q).                            (4.3)

One may choose the grid offset so |Dv|(boundary 5Q)=0, then the smooth proof passes directly: c_Q and the functions converge in L1, and the integrated gradients on 5Q converge to its derivative mass. (The exceptional offsets are null, since a finite measure charges only countably many parallel lines.) Because every r<=t disk centered in Q lies in 3Q, S_t v_Q=S_t v-c_Q there. Hence (4.2) gives

    |D(S_t v)|(interior Q) <= C |Dv|(5Q).                 (4.4)

Apply this simultaneously to v=g_j=|f_j|. For each fixed dyadic t choose a single grid offset whose square boundaries have zero measure for all |D(S_t g_j)| and |Dg_j|, and whose 5Q boundaries have zero |Dg_j| mass. Countably many j and grid lines are involved, so such offsets exist. Let K be a compact Lebesgue-null set, and K_a={dist(x,K)<=a} its CLOSED a-neighborhood. If K subset O subset {dist(x,K)<t} and O is open, all squares meeting O have 5Q contained in K_{7t}; their 5Q overlap is bounded by an absolute constant. Using (4.4), |Dg_j|<=|Df_j|=mu_j, and the absence of output mass on grid boundaries, we get

    |D(S_t g_j)|(O) <= C mu_j(K_{7t}).                   (4.5)

The geometric constant 7 is sufficient: a point in 5Q is within 3 sqrt(2) t of any selected point of Q cap O, and that point is less than t from K.

The full output is max(S_t g_j,T_t g_j). The BV lattice inequality |D max(u,v)|<=|Du|+|Dv| holds as measures, including jumps; it follows by smooth approximation, the Sobolev maximum inequality, and local lower passage. The positive-radius term is Lipschitz with gradient at most mu_j(R2)/(pi t^2). Consequently

    nu_j(O) <= C mu_j(K_{7t})
                  + |O| mu_j(R2)/(pi t^2).              (4.6)

Portmanteau for vague convergence on relatively compact open O gives nu(O)<=liminf nu_j(O). Narrow mu_j -> mu and compactness of K_{7t} give limsup mu_j(K_{7t})<=mu(K_{7t}). Their total masses are bounded. Therefore

    nu(K) <= C mu(K_{7t}) + C0 |O|/t^2.                 (4.7)

For fixed t, compact nullity lets O shrink around K with arbitrarily small area and still contained in the open t-neighborhood. Thus nu(K)<=C mu(K_{7t}). Only now send t down to zero; finiteness of mu and continuity from above give nu(K)<=C mu(K). Inner regularity extends this to Borel null E, proving (4.1).

This uses the pinned signed localization operation at its actual constant C. Its additional content here is passage uniformly through the ORIGINAL strict sequence and localization of possible singular cluster excess. It does not identify the correct singular density, compare it with |D(Mf)|, or remove diffuse/Cantor/jump alternatives from B. In particular mu can charge a sign-crossing jump where |D(Mf)| vanishes, and (4.1) still allows nonzero nu there.

## Stage 5: an exact planar failure of the slice-transfer attempt, NOT a counterexample to B

It is false that monotonicity of f in the normal variable alone permits applying Stage 3 to a planar slice of its disk maximal envelope, even with a midpoint baseline. The following exact example records the unpaid geometry rather than hiding it in a model assumption.

Let A=1, B=2, t=1, a=1/20, L=32. Define the monotone profile

    q(s)=-1 (s<=-8),  q(s)=s/8 (-8<=s<=0),
         =s/4 (0<=s<=8),  q(s)=2 (s>=8).

Define the planar local model F(s,y)=q(s) when |y|<a and F(s,y)=q(s+L) when |y|>=a. Each normal slice is nondecreasing with signed endpoints -1,2. Put

    U(s)=sup_{0<r<=1} A_r |F|(s,0),
    H(s)=max(3/2,U(s)),
    p=(2/pi)(arcsin(a)+a sqrt(1-a^2)).                    (5.1)

Here p is the disk area fraction in |y|<a at radius 1. At general r it is p(r)=1 for r<=a and otherwise the same formula with a/r. It is nonincreasing in r, so p(r)>=p.

At s=-9 every tested disk sees |F|=1 in the strip and |F|=2 outside, up to null boundary points. Thus

    U(-9)=2-p.                                          (5.2)

At s=0 the outside-strip value is 2 on every tested disk, while within the strip |q(s')|<=1/4 for |s'|<=1. Hence for ALL 0<r<=1,

    A_r|F|(0,0) <= 2-(7/4)p(r) <= 2-(7/4)p,
    U(0)<=2-(7/4)p.                                     (5.3)

The radius-1 average also gives U(0)>=2(1-p). Since p<=4a/pi<1/4, U(0)>3/2, so the midpoint baseline does not remove the dip. At s=9 all tested values are 2, so U(9)=2. We have

    H(-9)-H(0) >= (3/4)p>0,  H(9)=2,                   (5.4)

whereas H has far-left endpoint 3/2 and far-right endpoint 2. Each normal slice of F is globally 1/4-Lipschitz in s, uniformly in y. Its averages, their supremum U, and H are therefore 1/4-Lipschitz in s. They are constant outside a finite interval, so H has finite variation. Its total variation is at least

    1/2 + (3/2)p > 1/2;                                (5.5)

as follows by the partition through -9, 0 and 9 and the two endpoint limits. This disproves the attempted universal planar analogue of (3.2) under the sole hypothesis that each normal slice is monotone. It is not a failure of the proved one-dimensional lemma: the disk intersects DIFFERENT profiles at different tangential coordinates, so there is no single q and disk marginal convolution representing this slice.

This is NOT a counterexample to B. The local model is not globally L1; it can be cut off outside a rectangle containing the displayed test disks to make a single compact BV input with the same local inequalities, but there is no strict sequence and no full maximal-output discontinuity here. More decisively, the tangential jump cost is large: at each of y=+/-a,

    integral_R |q(s+L)-q(s)| ds = L(A+B)=96.             (5.6)

Indeed q(s+L)-q(s)=Dq((s,s+L]) and Tonelli gives L Dq(R). Thus the two strip edges alone cost 192 in transverse variation. The normal variation in the window |y|<1 is just 2(A+B)=6. Scaling the whole example preserves this unfavorable ratio; tiling such cells at fixed mass does not make the transverse derivative cost vanish. Consequently this construction does not meet the polar alignment forced by strict convergence to a flat jump. Full M may select radii greater than 1; a capped-envelope slice calculation is not a computation of full-output variation. No counterexample claim is made for B, U-sharp, or near-aligned layers.

What it establishes about the attempted proof: arbitrary monotone normal slices and an exact varying baseline are still insufficient; one must quantitatively use the small transverse/polar defect of a strict planar sequence. Stage 3 pays exact common-profile valleys, while this example shows the missing stability cannot be omitted.

## Stage 6: exact remaining full-target obstruction and disposition

The original quantifiers have never changed. Write H_j=Mf_j, H=Mf and nu_j=|DH_j|. The pinned estimate bounds their masses. The paid local L1 convergence follows from |H_j-H|<=M(f_j-f), weak (1,1), uniform BV-to-L2 input embedding and the strong L2 maximal estimate: convergence in measure plus uniform L2 bounds gives local L1 convergence. Thus DH_j converges distributionally to DH, and every variation cluster nu satisfies |DH|<=nu. The rechecked tail estimate makes the nu_j tight.

The exact unpaid condition is still, for EVERY original real strict-BV sequence and EVERY cluster nu,

    nu <= |D(Mf)|,                                      (U-sharp)

or equivalently, for every nonnegative phi in C_c(R2),

    limsup_j integral phi d|D(Mf_j)|
                   <= integral phi d|D(Mf)|.             (6.1)

Together with tightness this is equivalent to full B, not a sufficient condition restricted to a smaller class. Conversely, full B plus local L1 output convergence forces equality of every cluster with |DH|. The standard proof is to take tight subsequential limits, use lower passage |DH|<=nu, and compare total masses. No alternative topology has been substituted.

A precise calibration formulation of the remaining task is as follows. For a fixed compact weight phi>=0, choose smooth compact vector fields N with |N|<=1 approximating the polar of DH in L1(phi |DH|). Then

    integral phi N dot dDH_j -> integral phi N dot dDH,

so U-sharp would follow if their nonnegative excesses

    integral phi (d|DH_j|-N dot dDH_j)                    (6.2)

could be made small in limsup by improving the calibration. This is a reformulation of the unpaid estimate, NOT a proved result. The fixed-positive-radius theorem controls gradients when winning radii stay bounded below; (6.2) must still be paid on arbitrary vanishing-radius winners. The source constant-C cone, endpoint, spatial and run charges cannot be replaced by that calibration without proof.

Stages 3–5 sharpen the account of the signed-jump obstruction. An exact common normal profile is now controlled even with a varying BV baseline bounded below by the lower absolute trace minus epsilon. Arbitrarily varying tangential profiles defeat a naive slice application, as Stage 5 explicitly proves. Strict convergence supplies a small transverse/polar defect that the example lacks; what is missing is a uniform quantitative transfer using that defect across ALL vanishing scales, with no lost coefficient or unbounded scale count. Normal monotonicity alone is not such a transfer. At diffuse/Cantor contact concentrations and strict staircase approximants, one likewise still needs output polar calibration, rather than a small strong derivative residual. Stage 4 only localizes singular cluster mass with C and leaves its correct density unpaid.

No full counterexample has been found. The capped planar example is explicitly NOT one. Failed summation and slice-transfer arguments have been recorded with their unpaid statements; they are not evidence that the full method or B fails. There is no literature-only completion, substantial nomination, manuscript, Lean file, acceptance/count change, or request to treat self-checks as independent review.

## Stage 7: bounded primary comparison and source contracts

All pinned premises refer to openai/math revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, accepted true by user stipulation. The exact URL prefix for manuscript files is

https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-Endpoint-Gradient-Bound-for-the-Centered-Disk-Maximal-Operator-September-26-2026/build/

The source `sections/introduction.tex`, thm:main and prop:finite-band, supplies the endpoint C bound and signed uniform finite-band bound; `sections/extension.tex`, lem:sobolev-band and cor:bv-input, supplies its Sobolev interface and exact BV output class. Its eq:localized-input–eq:null-localization already contains mean subtraction, square Poincare, lower-radius splitting and null-set localization. Stage 4 reuses precisely those operations with narrow convergence of the ORIGINAL input variation measures and careful BV grid boundaries; this is a supporting technical deduction, not an independent substantial contribution.

The source `sections/local.tex`, lem:local/eq:local-direction, controls unfavorable directional gradients without charging positive cone mass, but its hypotheses include a valid gradient decomposition and locally maximizing radii. `sections/prices.tex`, eq:prices-scalar-defects/eq:prices-scalar-defect-budget, has exact scalar telescoping with terminal density. `sections/labels.tex`, lem:labels-neighbors, has the per-scale neighboring-defect identity. `sections/assembly.tex`, eq:run-master and the following endpoint/baseline terms, makes clear why the total C estimate is not the desired coefficient-one comparison. R2's refined fine budgets survive for Df_j, not automatically for D|f_j|. No unpaid extension of source local analytic estimates to arbitrary BV decompositions is used in this report. `source-contracts.json` gives exact paths, URLs, labels and current reading extents separately from inherited ones.

González-Riquelme, [arXiv:2109.09691v1](https://arxiv.org/pdf/2109.09691v1), Theorem 1, assumes W11(R) norm convergence. Proposition 12 subtracts an affine function and estimates an L1 derivative residual; its displayed inequality explicitly includes ||f_j'-f'||_1. Strict BV staircases do not make that residual small. This remains the operation-level technical veto for the old A, not a source for B.

González-Riquelme–Kosz, [arXiv:2009.05729v1](https://arxiv.org/pdf/2009.05729v1), introduction §1.3 and Theorem 1, uses the one-dimensional UNCENTERED operator and the BV difference norm |f(-infinity)|+Var(f). Continuity for that norm is not strict convergence. The inherited r2 report describes its partition/optimizer proof operations; the exact norm and theorem were reread here. No ordered-interval proof is asserted to transfer to planar centered disks.

Lahti–Weigt, [arXiv:2510.01936v1](https://arxiv.org/pdf/2510.01936v1), Theorem 1.2 and Proposition 4.15, controls the individual jump part by one half, assuming BVloc regularity of the maximal function. Theorem 4.14 retains detachment at |D^c f|-almost every point. Its jump proof uses midpoint lower bounds, upper traces, small-radius exclusion and a continuous positive-radius truncation. Those operations do not control continuous variation accumulating at a jump along a strict sequence. The report's Stage 3 controls TOTAL variation of an exact normal model but cannot be applied to arbitrary planar slices, as Stage 5 demonstrates.

The log-concavity mechanism in Stage 3 is elementary order-two positivity/one-dimensional shape preservation, not asserted novel. Ibragimov's primary publisher page, [On the Composition of Unimodal Distributions](https://epubs.siam.org/doi/10.1137/1101021), states the classical characterization of strong unimodality by a log-concave density. Only the publisher abstract was read; the full original proof was not read or used. Our separated-measure inequality is proved directly, including nonintegrable endpoint profiles, so this historical comparison is not an extra mathematical premise or a claim that the displayed model lemma exactly equals the probability theorem.

The web screen was bounded to strict-BV maximal continuity and this log-concavity antecedent. An arXiv abstract-page request for 2510.01936 returned an internal error, so no new version-status assertion is made here. The pinned v1 PDF was accessible. No absence-of-hit, named-open-status, worldwide novelty, or independent contribution PASS is claimed.

## Stage 8: reproducibility, rights and handoff

`checks.py` tests the exact disk marginal's order-two inequality, derivatives of convolutions of 64 asymmetric monotone step profiles, finite-radius suprema, 192 varying-baseline partition inequalities, and the constants in Stage 5. It does NOT discretize arbitrary planar strict sequences or certify B. The proofs, not the samples, establish Stages 3–5. The Stage 4 measure localization is analytic and has no numerical certificate claim.

`assignment-and-history.md` preserves the current recovery instructions and the earlier full brief/history with the entire r2 report; `inputs/private/frozen-r2/` is an authenticated byte-for-byte r2 package. No r3 private reasoning was read. Private third-party copies retain their original rights and are excluded from original-prose/code licensing. Original work is by Myeongjin Kang, no affiliation; prose CC BY 4.0, code MIT.

The input/output manifests are frozen SHA256-and-size inventories; `seal.json` authenticates them and its detached hash is supplied in the terminal handoff. The read-only verifier authenticates all bytes and membership, including code and receipts, BEFORE replaying any stored checker or prior verifier. Replays use Python -B and cannot regenerate inventories or receipts. Mutation tests use disposable copies under this owned directory only and are deleted before the final freeze. Verification is authentication and reproducibility, not independent mathematical proof review.

All writes stayed in strict-bv-continuity-r4. No nested agents, shared/sibling edits, staging/commits, external messages/publication, counting, manuscript or formalization were performed. Recommended disposition: retain substantive unresolved research progress; full B and U-sharp remain UNRESOLVED, and no substantial complete theorem is nominated.
