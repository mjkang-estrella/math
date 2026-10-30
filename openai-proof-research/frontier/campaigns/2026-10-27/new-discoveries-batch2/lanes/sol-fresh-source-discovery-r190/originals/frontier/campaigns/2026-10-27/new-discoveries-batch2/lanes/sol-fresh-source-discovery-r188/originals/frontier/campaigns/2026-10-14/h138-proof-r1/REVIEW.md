# H138 first independent correctness review

**Full-scope correctness: PASS, relative to the expressly stipulated pinned source proof operations.** No frozen bytes were repaired, no local-uniformity claim was adopted as a new source axiom, and no quantifier was weakened. This is a correctness disposition only. Independent contribution is **UNREVIEWED**; acceptance/count assigned here is zero. Parent alone integrates, reviews, and counts. No other H138 gate's findings were read or used.

The object reviewed is the entire 333-line `AUTHOR-PROOF.md`, SHA256 `fc1228c5dc20b373fcba3b176ccb6b26e30bc099647e4dc8d5762a3833355258`, against the exact `H-SCOPE.md`, SHA256 `82e7f37c36205cc62e52fc6ad037072706405efb7302dafa395747a2c5b2ff53`. The preserved prefreeze derivation has SHA256 `948045c339782a0d46f1cd86eba05df10fef5c6f106e98b64393412fbe868a31`; freeze receipt is dated 2026-10-21T00:36:26.664416+00:00. Intake/author status and artifact results were not mathematical premises.

## Exact question and dependency boundary

For **every** real pair (4/9<v<1), (1<c<9v/4), the claim is that there exist **one** complete smooth metric (g) on (mathbb R^3), Euclidean in a neighborhood of zero, with (operatorname{Ric}_ggeq0) everywhere and normalized asymptotic volume ratio

\[
\lim_{R\to\infty}\frac{\operatorname{Vol}_g B_g(0,R)}{(4\pi/3)R^3}=v,
\]

and a strictly increasing sequence of positive integers (k_i\to\infty) such that

\[
\dim_{\mathbb R}\mathcal H_{k_i}(\mathbb R^3,g)\geq c(k_i+1)^2\qquad\text{for every }i.
\]

Here (mathcal H_k) consists of real smooth **entire** (g)-harmonic functions satisfying (|u(x)|\leq C_u(1+d_g(0,x))^k) at **every point**, for an individual finite (C_u). The same metric serves all (i). There is no unique tangent cone assumption, uniform (C_u), prescribed degree sequence, all-large-degree conclusion, optimal endpoint, extra curvature hypothesis, or allowance of quasimodes/degenerate limits.

The pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. As instructed, its operative proofs are true inputs at their actual scopes. In particular, September26 pays finite angular transversality/retained doubles, fixed-area gauge, whole-ball restriction facts, fixed-program freezing/graphs, signed matching and growth. It does **not** pay a theorem at infinite angular cutoff. I independently checked the new composition, especially §§3–6, using the actual source proofs to identify what their estimates use. The tests below are analytic; packet verification and any finite controls do not prove them.

## C1 — finite programs, bands, bases, connectors, activation: PASS

Set (a=\sqrt v). The interval (\sqrt c<\theta<3a/2) is nonempty exactly because of the retained strict bound on (c). Then (C_*>1) sufficiently close to one gives (2\theta\sqrt{C_*}/(3a)<1), and (a^2<\kappa_*<1) leaves geometric slack. A single small conformal (C^2) neighborhood provides all the rank-wise min–max upper bounds and a common tensor comparison; the fixed-area gauge's (C^0) bound does not require higher derivatives uniform over that neighborhood.

The rank convention includes the constant at position 1: (B_l=(l+1)^2), so ((B_{L_i},B_{M_i}]) contains precisely round blocks (L_i+1,\ldots,M_i), of dimension (D_i=(M_i+1)^2-(L_i+1)^2). The independent recursive requirements are cofinite: (L_i>M_{i-1}), (D_i>c(k_i+1)^2), (m_i^*<k_i), and (\beta_i<k_i). The limits are respectively (D_i/k_i^2\to\theta^2>c), (m_i^*/k_i\to2\theta\sqrt{C_*}/(3a)<1), and (\beta_i/k_i\to0). Thus one unbounded numerical degree sequence is selected once, with strict margins for each band, and without excluding any admitted (v,c).

For each **finite** stage (n), the actual retained-double lemma allows the larger cutoff (P_n+1) even for an earlier band's prescribed adjacent double. The avoidance lemma connects simple endpoints through that finite cutoff. Therefore each loop has its sole intended double, and all partial permutations preserve each selected band and both its boundary cuts. Concatenating each band's adjacent swaps produces its single cycle. At a fixed phase of the complete basic concatenation, repeated returns send a label through all the ranks of its own band equally often, including phases spent in other bands' loops. Averaging over a common multiple of all finite cycle lengths gives exactly the ordered-rank average; loop durations need not agree. Doubling accounts for real frame signs. Every pair in a selected band crosses in a full label period; return of the ordered frame makes the number of its sign reversals even.

The old base is simple through (P_n+1), and so is the new base, because simplicity through the higher cutoff implies the lower one. Avoidance therefore supplies (C_n) preserving **all old** gaps, and ordered old labels continue without crossing along it. No condition on new modes during older stages is used. New graphs and matching coordinates begin only at an integer (J_i) deep in their new constant base collar. The initial round-to-first-base path is separately provided before first activation. No graph is requested across a past uncontrolled high degeneracy.

## C2 — one radial factor, full Ricci tensor, core, completeness, volume: PASS

For a fixed finite collection, the smooth controlled parameter formula gives (H_t=O(C_n\eta)), (H_{tt}=O(C_n\eta^2)) and the spatial derivatives needed for curvature. Here (\eta=t^{-3/4}), and over a bounded phase interval (t) changes by (O(C_n t^{3/4})=o(t)); hence the bump amplitude at its center is comparable to the local (\delta=\eta^{3/4}). Squared speed and squared divergence are (O(C_n t^{-3/2})). A smooth envelope can dominate them over the whole control box, with transitions in constant collars. Its entire future cost from entry (T) is at most (2C_n/\sqrt T), regardless of how many repetitions are later used. This is the crucial compatibility with long repetitions, not an assumption of summable angular variation.

With (\delta_0=\int E<1-a), the stated equation

\[
f''=-(1-a-\delta_0)\beta-r^{-1}E(\log r),\quad f(0)=0,\ f'(0)=1
\]

has total slope drop (1-a), so (a\leq f'\leq1), (f'\to a), (f=r) near zero, and (a\leq b=f/r\leq1), (b\to a). This is one (f), independent of **all** controls. Defining it after the schedule and envelope is legitimate: the thresholds use bounds valid for every (b\in[a,1]) with the established local derivative estimates, not the value of an unknown control-dependent (f).

For (r\geq2), (b\leq a+\delta_0+2/r). Choose the permitted total mass small and first motion late; this gives fixed tangential slack from (\kappa_*>a^2). With (A=H^{-1}H_t), (B=A/2), (q=1+b_t/b), the exact stipulated identities give the **whole** scaled Ricci matrix, with tangential block at least (\tau I). Its Schur complement is nonnegative because the envelope dominates

\[
\frac{2E}{b}\ \geq\ \frac{\operatorname{tr}A^2}{4}+\frac{|\operatorname{div}_H B|^2}{b^2\tau}.
\]

The fixed constants (a\leq b\leq1), (\tau>0) allow one multiplier of the squared finite-family norms; no linear-in-speed integrability is needed. The mixed block is included with the factor (b^{-1}). Angular acceleration enters the tangential slack and is made small, rather than charged incorrectly as a radial square-speed term. On the stationary round compact core, concavity and (f'\leq1) give the ordinary round-warped Ricci inequalities. In stationary nonround collars at late radii, the same tangential slack and the nonnegative radial block apply.

Smoothness is local: only finitely many pieces and controls occur on a compact set, joins are smooth, and both angular and radial data equal the Euclidean polar data near zero. No convergence of all angular derivatives at infinity is required. Radial projection bounds any curve's length from below by its radial displacement, while the radial segment has length (r). Thus (d_g(0,(r,\omega))=r), balls are compact, and the smooth metric is complete. Fixed angular area gives (operatorname{Vol} B(0,R)=4\pi\int_0^R f^2); (f/r\to a) yields exactly (\operatorname{AVR}=a^2=v), independently of controls.

## C3 — arbitrary admitted past, freezing, joins and (b_t): PASS

The dependence on an arbitrarily long earlier ball can be eliminated with the actual whole-ball source argument, rather than postulated away. For every provisional metric, the fixed area form gives ((f^2\bar u_r)'=0); Euclidean center regularity forces (ar u) constant in (r). Positivity, preservation of constants, and Jensen then make every whole-ball restriction an (L^2(\mu)) contraction. The maximum principle also bounds extension of any fixed smooth frame vector by that vector's sup norm throughout the whole earlier ball. Neither bound grows with the earlier history's length or derivatives.

The radial memory estimate is also independent of earlier repetitions. Since (|b_t|\leq1-a), split (4.3) at (u=t-K\log t). Its initial term is at most ((1-a)t^{-K}). On the logarithmic window, all envelope pieces lie in the promised finite collection and have bound (C t^{-3/2}). Therefore (|b_t|\leq C't^{-3/2}+O(t^{-K})), and (b_{tt}=-E-b_t) has the same bound. This applies on either side of a join using the combined constants. In particular it does not assume the old fixed-program estimate (b-a=O(t^{-1/2})) for the new entire schedule.

For finite-frame freezing, the bounded-backward frozen solution has uniform needed derivatives on the fixed finite smooth collection and (b\in[a,1]). On the backward slab of length (\ell=4\log(1/\eta)=3\log t), coefficient variation is (O(C\eta\ell)), drift error (O(C\eta^2)+O(t^{-K})). The left discrepancy has a uniform sup bound from the preceding maximum principle, even if everything earlier in the ball changes. The source barrier (C\epsilon(j+1-t)+C\exp[-(t-j+\ell)/2]) suppresses that discrepancy at the inner target section by (O(\eta^2)). Thus the frame error is (O(C[\eta\log(1/\eta)+\eta^2])+O(t^{-K})=o(\delta)). This computation needs finite local smooth norms, not global bounds on the earlier metric.

For full-operator freezing only absolute (o(1)) is available and only that is used. To test the asserted finite-family uniform threshold, suppose it fails with the local speeds tending to zero while the earlier admissible histories vary. Translate the outer section to zero, take weakly convergent unit boundary data, and extract a convergent reference link and a scalar (b_*\in[a,1]). Every fixed-width past cylinder is eventually inside the finite collection and its coefficients tend to the corresponding constant-cylinder coefficients. Sectional (L^2\leq1) and interior compactness give strong inner trace convergence. Testing against a fixed smooth angular function, its scalar ODE bounds the derivative up to the outer section, identifying the weak boundary trace. Boundedness on the whole negative half-cylinder removes every negative radial root, including the constant mode's root (-1). The exact limit is uniquely the frozen bounded-backward extension of that weak trace. The frozen maps have the same limit. This contradicts an operator-norm discrepancy. All estimates involving the arbitrary past are just the contraction and maximum-principle bounds above. Thus the claimed uniformity over pasts follows; it is not a new axiom.

At a join, the two neighboring full periods, connector and collars are a fixed finite smooth collection before timing is chosen. Logarithmic windows are (o(t^{3/4})), and a fixed positive phase collar or period takes time comparable to (t^{3/4}). Delaying the join makes the backward slab fit. A new activation is placed more than the required logarithmic depth inside its collar, which also tends to infinity in time. The source boundary-limit argument then has arbitrarily long fixed-width slabs available. There is no use of an absolute operator error as an (o(\delta)) error.

## C4 — admissible graph balls, terminal limits, inclusion, continuity: PASS

For each **fixed** active cutoff (d), the uniform rank-wise spectral bound gives a positive lower bound (\tau_d) on the low inward multipliers over every future stage. It is allowed to be extremely small as (d) grows. On an individual finite collection the protected outer frequency gap has positive minimum, hence a reference contraction ratio (\kappa_{d,n}<1). Finite-frame freezing gives (T_{LL}=D+O(C_n\delta)), (T_{QL}=O(C_n\delta)); absolute operator freezing gives (T_{LQ}=o(1)) and the required relative (QQ) bound after choosing accuracy below a multiple of (\tau_d(1-\kappa_{d,n})).

For (M(V)=T_{LL}+T_{LQ}V), the inverse-difference identity in the source yields, on a fixed ball of radius (\rho_i<1/100), an inverse bound (2/\tau_d) and Lipschitz bound for (F(V)=(T_{QL}+T_{QQ}V)M(V)^{-1}) strictly below one. By delaying this finite collection, its error can be made less than half the reference deficit and (\|F(0)\|) less than the deficit times the ball radius. This supplies a **common fixed ball** for that cutoff over all its later collections; the radius is not successively shrunk. The finitely many active cutoffs at a stage can all be treated together.

Take a positive lower contraction deficit on each such piece. A full period at sufficiently large (t) contains enough integer steps that the sum of deficits for each active cutoff is at least one. At least one such period in every stage implies divergence of the sum for each cutoff, even if the per-step deficits tend to zero with the stage index. Consequently terminal iterates differ at a fixed (j) by at most (2\rho\exp[-\sum_{j\leq l<N}a_i(l)]\to0), uniformly in every control. This proves existence and uniqueness in the common ball first.

For the sharper estimate, **after** existence, retain the terminal graph merely by its ball bound. On a future window (K\log j), the combined local collection has some positive lower deficit (a_0). Iteration bounds the local forcing sum by (C\delta_j/a_0) and the unknown terminal contribution by (\rho\exp(-a_0K\log j)). Choosing (K) after (a_0) makes the latter (o(\delta_j)). All constants are determined by finite data. The window can meet a connector and its next period, but cannot require a second connector: two full periods and positive collars separate joins by much more than any of these fixed logarithmic lengths after the chosen entry thresholds. If the window starts just before a join, use the combined constants including the next program. Thus the estimate is uniform over arbitrary future control tails, without a uniform global spectral gap or tail derivative bound.

Finite terminal iterates depend continuously on controls. For each finite ball only finitely many controls are relevant; smooth Dirichlet dependence gives strong continuity of (T_j). Applied to maps from a fixed finite-dimensional domain, strong continuity plus (|T_j|\leq1) gives norm continuity by testing a finite basis. Finite low inverses are continuous. Uniform terminal convergence over the control product then proves actual coordinate continuity of the limiting graphs and matrices. This does not claim operator-norm continuity of the entire infinite-dimensional (T_j).

At a common terminal section (N), the two ordered low subspaces satisfy (E_q(N)\subset E_p(N)). Their images under the **same** whole-ball restrictions retain inclusion. Both are graphs with invertible low-coordinate maps by the bounds already proved. At fixed (j), their graph projections converge in norm; applying the projection relation to convergent approximations of a vector in the smaller graph proves inclusion of the limits. This establishes the flag's compatibility, rather than choosing unrelated invariant spaces and calling them nested.

## C5 — quotient coordinates and crossing sign: PASS

The small space inside the (p) low coordinates is exactly ((x,W_jx)), with (W_j=\Pi_{(q,p]}V_j^q). Its norm is bounded by the small graph bound, and is locally (O(C_n\delta_j)). For (S_j=\begin{pmatrix}I&0\\W_j&I\end{pmatrix}), direct multiplication gives

\[
S_{j+1}^{-1}A_j^pS_j=
\begin{pmatrix}
 A_{LL}+A_{LB}W_j&A_{LB}\\
 A_{BL}+A_{BB}W_j-W_{j+1}(A_{LL}+A_{LB}W_j)&A_{BB}-W_{j+1}A_{LB}
\end{pmatrix}.
\]

The lower left block is exactly zero by invariance of the smaller space. The quotient correction has the stated **minus** sign, with (W) at (j+1). The reference (A_{LB}) is zero, so its actual value is (O(C_n\delta_j)); multiplying by (W_{j+1}) costs (O(C_n'\delta_j^2)), on that finite collection. There is no additional term linear in (\delta).

The source divided-difference calculation uses the whole finite spectral cluster, remaining smooth through the internal double. If (q_\beta(x)=\exp d(\beta x)), the first-order outward entry is (q_\beta[\lambda_h,\lambda_l]\langle e_h,\dot L e_l\rangle). At equality its value is (\exp d(\beta\lambda)\,\beta d'(\beta\lambda)\langle e_h,\dot L e_l\rangle). The factor (\beta=b^{-2}) occurs once. The inverse derivative has the sign of this expression because (-q(x)q(y)p[x,y]=q[x,y]). The coefficient is nonzero on a sufficiently small fixed plateau, with sign uniform in the compact positive (b)-range. Finite-frame error and (T_{LQ}V=o(\delta)), followed by finite inversion, preserve this expansion. The quadratic quotient correction cannot cancel it. No uniformly bounded inverse across all (p_i) is used.

## C6 — scalar cuts, joins, Gaussian weights, all free faces: PASS

The expanded force (4.10) follows by dividing the (h) coordinate of (B_jv_l) by its (l) coordinate and subtracting (r_{hl}u_{hl}). The diagonal reference cancels exactly, and the denominator is uniformly positive on the finite quotient boxes after its thresholds. Thus (|F|\leq C_n\delta); every term involving an auxiliary coordinate contributes (O(C_n\delta\eta^{1/8})). On a crossing plateau the leading force is (z_\nu\eta_\nu^{3/4}m_{hl}/\alpha_l+o(\delta)), uniformly with all other controls and column coordinates free. The reference ratios use the same (b), so their zeros and signs are those of the reference eigenvalue differences.

When (\log r_{hl}) changes (+\to-), the stable directions point **away** from the cut; prescribing zero there determines both outward stable propagations. When it changes (-\to+), stable directions point **toward** the cut; their two incoming values must match. Reversing (h,l) exchanges these roles, giving one obstruction, not two, at the double. The ceiling convention uses the pre-crossing ratio for the step beginning before the crossing, with a possible single neutral step if the crossing is an integer. This changes only a bounded factor in the stable estimates. Activation truncates the initial interval; the start is a positive phase distance from its first crossing, so the central mismatch window is retained.

An old pair has both sign reversals in every full returning label period. A stable sign interval touching a connector is contained in the final old period, that connector/collars and the first new period; the same finite union covers the incoming sides of a matching cut. Repetition counts do not enlarge this interval. The old connector has no crossings, and each complete period has the required pair crossings. The two-period requirement prevents an interval from crossing two joins. Simple endpoint splitting and compactness away from zeros give (4.12) with finite constants for this union. A truncated activation interval does not need an artificial zero or a linear upper bound at activation; the upper bound used for central weights is only near the actual double.

On these bounded phase intervals the speed is comparable to (eta_\nu). Summing the linearly vanishing gap along (m) mesh steps gives stable weights (W(m)\leq C\exp(-c\eta_\nu m^2)) (and damping in the interior), whence the Green sum is (O(\eta_\nu^{-1/2})). Multiplying force size (\eta_\nu^{3/4}) gives (O(\eta_\nu^{1/4})<\eta^{1/8}) after a finite late threshold. These are the required box estimates even when the interval straddles a join.

At a mismatch, the backward solution is a **negative** force sum; subtracting it from the forward value therefore makes both sets of weights positive. In a window of (\theta\eta_\nu^{-1/2}) steps about the cut there are (\asymp\eta_\nu^{-1/2}) terms whose weights are bounded below and whose forces have the oriented control sign and magnitude (\asymp\eta_\nu^{3/4}). This gives a signed contribution (\asymp\eta_\nu^{1/4}). Plateau terms farther out have that same sign. Outside the fixed plateau, weights have already crossed a fixed phase separation and are bounded by (C\exp(-c/\eta_\nu)); at most (O(\eta_\nu^{-1})) forces give (O(\eta_\nu^{-1/4}\exp(-c/\eta_\nu))), negligible against the central contribution. Thus both face signs hold **uniformly with every other variable free**, as required for one coupled product fixed point.

Each actual crossing belongs to one disjoint band and produces exactly one obstruction in its quotient. Other quotients feel that control through their matrices, but have no additional crossing obstruction assigned to it at that time. Their forces and signs were estimated with that coordinate free. This verifies consistency of the single control's use across all equations; independent per-band control choices are not being combined afterwards.

## C7 — one product fixed point and exact finite quotient lines: PASS

The coordinate set is countable: countably many bands, each with finite rows, at integer times after activation, together with countably many crossings. Each force at a fixed step has finitely many auxiliary coordinates, while its matrix has the product continuity proved in C4. Each stable propagation between cuts is finite. Its interval may be very long, but is fixed for that output coordinate; product continuity needs no uniform bound on all such interval lengths. Hence every output coordinate is genuinely continuous. The only future-tail dependence is already in the uniformly convergent graph limit.

The trial map takes the compact product of intervals into itself by C6. Freezing later coordinates at their centers and applying Brouwer to the first (N) coordinates gives partial fixed points. A diagonal subsequence converges coordinatewise; continuity passes every fixed coordinate's equation to the limit. At the resulting fixed point, the strict face signs exclude endpoint controls. The clamp equation at an interior control forces zero mismatch. Thus all scalar recurrences hold exactly, including both sides of cuts, and (B_jv_l(j)=\sigma_l(j)v_l(j+1)) with (sigma_l>0). The finite column matrix differs from the identity by norm at most (D_i\eta^{1/8}<1/2). All bands use this **one** fixed point and therefore the same provisional-metric parameter sequence. Compactness has not been used to assert an infinite column inverse.

## C8 — every prefix, mesh, errors, strict rates and lift: PASS

For each label and fixed program (n), subtract its own phase mean. The periodic primitive has a finite bound (A_{i,n}) independent of how many periods are repeated. With (s'=t^{-3/4}), integration by parts gives the stated (O(A_{i,n}t^{3/4})) bound on **any** stage prefix. Entry can be chosen so this is at most (2^{-n}t), for every active label. A connector/collar of fixed phase length has total time (O(C_nt^{3/4})), and bounded old-band frequencies; its whole contribution and every prefix can likewise be bounded by (2^{-n}t) at late entry. At each stage only finitely many such requirements occur.

For any fixed (N), all earlier completed stages and connectors have a finite total contribution, however enormous. Later discrepancies are bounded by (Ct\sum_{n\geq N}2^{-n}), since their endpoint times do not exceed the current (t). First let (t\to\infty), then (N\to\infty); the normalized discrepancy is zero. Thus endpoint averages are not being substituted for prefix bounds. Mesh errors on each later finite collection and the logarithmic multiplier errors can be required to be at most (1/n) per unit time, so their total is (o(t)) by the same finite-early/tail argument. The small number of mesh steps straddling joins uses the adjacent finite collection; endpoints constant in phase introduce no jump, and its bounded-step errors can be covered by the same entry thresholds. Nothing in this argument bounds a stage's duration from above.

Because (b\geq a), (d(b^{-2}\lambda)\leq d(a^{-2}\lambda)). An **upper** growth bound therefore needs no global rate for (b-a\to0). Combining the prefix mean estimate and the (o(t)) errors gives limsup quotient rate at most (m_i^*<\gamma_i), hence (|z_l(j)|\leq C_{i,l}e^{\gamma_i j}) for every integer (j\geq J_i).

The first (Q_i) ordered ranks have reference frequencies at most (sqrt{C_*}(L_i+1)/a) at all later stages, including connectors. The finite local errors may be made smaller than the fixed margin to (eta_i=sqrt{C_*}(L_i+1)/a+1). Thus (|L_j|\leq e^{\beta_i}) holds uniformly in time for this fixed band. The reference off-diagonal (R_j) vanishes, and local errors can be bounded by one on every later collection; finite initial errors can also be absorbed. Hence a fixed-in-time bound (K_i) for (R_j) is justified without any uniformity in (i).

For the **exact** upper triangular recurrence, set (x(J_i)=0). Variation of constants gives

\[
\|x(j)\|\leq K_iC_{i,l}\sum_{m=J_i}^{j-1}e^{\beta_i(j-1-m)}e^{\gamma_i m}
\leq C'_{i,l}e^{\gamma_i j},
\]

because (eta_i<\gamma_i<k_i). This is a forward finite-dimensional lift; it neither inverts a lower block on an infinite future interval nor relies on cancellation of fast components. The two graph embeddings and (S_j,S_j^{-1}) have bounded norms for fixed (i) from their fixed balls. They produce actual full-Hilbert-space traces with exact inward consistency and the same rate.

The simultaneous timing requirements are compatible. Fix all finite programs and connectors first. For each interior/join, take the maximum of its finitely many control, operator, graph, sign, prefix, multiplier, mesh and low-block thresholds; include the neighboring window constants before timing the join. Repeat the preceding program by full periods until the next entry/join threshold is reached. Since (int^\infty\eta\,dt=\infty), a finite number of repetitions reaches every prescribed finite threshold. Their square-speed cost is still bounded by the entire tail integral used in C2. Delaying an outgoing join never invalidates the preceding stage's already imposed bounds. Assign summable mass budgets separately to interiors/connectors. This gives an inductive schedule satisfying all these conditions, with no finite accumulation and no dependence on controls. Arbitrarily large finite derivative constants and arbitrarily small finite gaps are allowed; they require larger thresholds, not an added uniformity hypothesis.

## C9 — entire functions, independence and all-point growth: PASS

Let (w_l(j)) be the lifted exact trace. Invariance gives (T_jw_l(j+1)=w_l(j)). Although initially only in (L^2), each is the restriction from the next larger whole ball and hence is smooth on its inner sphere. Dirichlet extensions on all these nested **whole** balls agree by uniqueness, including the Euclidean center. Their union is one real smooth entire harmonic function on the chosen metric. At activation, the quotient traces of the (D_i) lifted functions form the invertible finite column matrix. Any linear relation among these functions would restrict to that sphere and then project to a relation among those columns. Thus each band independently supplies (D_i) functions; independence between different bands is unnecessary for the stated inequalities.

For (j\leq t\leq j+1), the all-radius whole-ball contraction gives (|u_l(t,\cdot)|_2\leq\|w_l(j+1)\|_2\leq C_{i,l}e^{\gamma_i(t+1)}). This covers noninteger spheres, not just a subsequence.

The final sup estimate does **not** require uniform Schauder constants at infinity. In fixed angular charts the logarithmic equation is

\[
\partial_t(e^tb^2\partial_tu)+e^t\Delta_{H_z(t)}u=0
\]

with respect to the fixed angular density. On a cylinder centered at (t_0) of width four, divide by (e^{t_0}). Its principal divergence coefficients have common upper and positive lower bounds from (a\leq b\leq1), (e^{t-t_0}\in[e^{-2},e^2]), and the common (C^0) tensor comparison of (H) to round. The finite atlas and fixed smooth density have fixed comparison constants. For a weak solution, testing with a cutoff times (|u|^{p-2}u) gives the Caccioppoli estimate for (|u|^{p/2}) with constant depending only on ellipticity and (p). The fixed-chart Sobolev inequality and the iteration (p=2\cdot3^m) on nested cylinders give (|u|_{L^\infty(\text{inner})}\leq C|u|_{L^2(\text{outer})}). Products of the iteration constants converge after the (1/p) powers; no derivative of a principal coefficient is used. Apply to positive/negative parts or the usual regularized absolute value. Thus the constant is uniform from precisely the claimed (C^0) data. Smooth elliptic regularity is used only separately on compact sets to know the functions are smooth, where its constants may depend on that compact set.

Integrating the sectional bound over the width-four cylinder and applying this estimate yields (sup_\omega|u_l(e^t,\omega)|\leq C'_{i,l}e^{\gamma_it}). Since (d_g(0,x)=r=e^t) and (gamma_i<k_i), enlarging the individual constant over the compact core gives the required bound at **every** point. Therefore (D_i>c(k_i+1)^2) gives every required dimension inequality on the **same** metric. This completes the full frozen statement, retaining every admitted parameter pair and infinitely many strictly increasing degrees.

## Original context and primary restrictions

I130's selected H and full H1/H2 operations, I133 in full (including its actual PARKED conclusion, fixed-cutoff forgetting, every-prefix discussion and common-core/uniform-AVR obstruction), the actual decoded FINAL PARENT I130/I133 responses in the two named original task JSONs, and r33/report.md were read. They remain at their old dispositions. Their exhaustion example disproves an inference from local/volume convergence to normalized growth constants; it is not an impossibility proof against this direct compatible program. This review does not regrade old partials or unrelated targets.

September25's **actual** finite spectral selection and full-leg normalization were checked, not merely its headline. Counting chooses finite (k,L,M_l); the full fixed round (V_l) are invariant even if a selected prefix cuts a multiplicity. Its exact identity is (D^{-1}\mathcal T=[I+K(P_e-\theta I)]\mathcal B), with (0\leq K\leq\theta^{-1}I), followed by determinant normalization and uniform-in-past finite-dimensional inversion. Thus a naive unfactored error over a long anisotropic leg is already overcome by a compatible classical operation. It supplies no infinite-degree assertion and is not an obstruction used against H138.

Huang `2109.07534v1`'s counting theorem and three-circles/counting proof retain a **unique tangent cone**, discreteness of its spectral degree set, normalization and Gram preservation. Its (n=3) dimension asymptotic has coefficient (v); uniqueness is not a Ricci-only conclusion. Xu `1601.02066v1`'s weighted sequence lemma and three-circles proof use the exponent's exclusion from the **union** of spectral degrees over all relevant conic tangent measures; equality in the weighted inequality is exactly where exclusion is used. No such exclusion is proved here, nor needed for this construction. Colding–Naber `1108.3244v3` supplies the actual slow-link lemma including mixed terms and its global realization/gluing mechanism, with fixed volume forms, slowed derivative bounds and closability; it does not supply the harmonic flags. Greilhuber–Kepplinger `2312.16939v4` supplies the actual round two-sphere conformal-stability proof and the local spectral submersion/transversality mechanism. Its general high-multiplicity pathology and noncrossing results do not grant an infinite-cutoff modulus. Source361's own finite-cutoff proofs, read through their endings, are the operative stipulated angular inputs.

No sectional-curvature or locally-conformally-flat comparison theorem was used as a Ricci-only contradiction. No literature-wide priority, current-open status, latest-version assertion or contribution verdict follows from these bounded reads. Unused transitive proofs are listed in READING-LIMITS.md rather than claimed read.

## Disposition

No unresolved mathematical objection was found in the unchanged full H138 argument relative to the stated source stipulation. **PASS** applies to C1–C9 together, not just to a finite prefix, quotient model, or conditional list of new local estimates. The explanations above verify the author’s composition; they do not replace frozen formulas or add hypotheses. Reading/isolation/artifact limitations remain as disclosed in the separate ledgers and READING-LIMITS.md. Independent contribution remains **UNREVIEWED**, and this packet assigns **zero** acceptance/count.
