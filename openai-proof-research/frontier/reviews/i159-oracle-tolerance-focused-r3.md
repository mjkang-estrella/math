# I159 — Independent focused review of ORIGINAL R154

**Verdict: PASS without substantive repairs for the unchanged ORIGINAL R154 theorem and proof, under the stipulated pinned OpenAI theorems and lower proof operations.** This is a mathematical review judgment, not formal certification. No acceptance or substantiality decision is made. Eight accepted findings remain eight; two remain.

**The broader historical I157 recursive audit remains INCOMPLETE, with its original unresolved verdict intact.** This round uses the user's explicit R154-only scope. Torus, weighted-bin, trace-decoder, PDE, older parked branches and unrelated comparator chains are not mathematical premises of R154. They have not been promoted to PASS by removing them from this gate. The historical blanket internal-reserve independence assertion remains **FAIL**.

The original R154 report is `frontier/iterations/i154-dimension-independent-oracle-tolerance.md`, SHA-256 `1878b68a5482aba8807f4d910465f83b43d86d401af1a53d038cfebc40b08be1`. The mandatory unchanged I157 task has SHA-256 `b6975be60991316c0d845e3f3e4541f8c3fb66addca871f7d109a5ee423a0940`; the I154 and I152 original tasks respectively have hashes `0fa43c233f6032d38f3b905cac2253321303e3a300342112ae8716e504897d97` and `f13a8eb19fe9ee8cdd1a6fbeb6618529a48c0599f08a84272be5b68570bf7379`. None was edited. Original reports, finalized responses, clarifications and failures are bound as context, not substituted for this independent derivation.

## Exact statement and dependency boundary

The gate covers exactly: for each fixed epsilon>0, there exist positive c_epsilon,C_epsilon and one measurable randomized real-query algorithm, for every integer d>=2, every C2 potential with supplied minimizer 0, V(0)=0 and I<=Hessian V<=2I, and every admissible measurable causal stateful oracle with absolute value error and Euclidean gradient error at most c_epsilon, the output is within TV 1/10 of pi_V and every execution uses at most C_epsilon d^epsilon queries. Between-query real computation is unrestricted. The order is not one c for all epsilon; there is no finite-bit or arbitrary-accuracy claim.

All source results and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated. I check their hypotheses and their use, without auditing their truth or drawing contradiction/ex-falso inferences. The mathematical source closure for this theorem is the upper-bound construction in the pinned *Subpolynomial query complexity for well-conditioned log-concave sampling* manuscript. The following files were newly read completely, including their proof endings: `introduction.tex` 1–269, `preliminaries.tex` 1–275, `jets.tex` 1–317, `divergence.tex` 1–535, `centering.tex` 1–414, `numerics.tex` 1–779, `implementation.tex` 1–729 and `sampling.tex` 1–435. These names below refer to that manuscript's `build/sections/` directory. Exact new display ranges, endings and passage hashes are in `read-log.json`; full-file SHA-256 and pinned Git-blob bindings are in `dependencies.json`.

The dependency chain is explicit. Preliminaries supplies C2 bounded-Hessian comparison, moments and conditional coupling. Jets supplies smooth conditional means at center x+r rho y and scale r sqrt(1-rho^2), all-split derivatives and probability transport. Divergence supplies material-derivative bounds and the final vector RMS estimate. Centering supplies the stationary product-law path integral, with s=sigma/2, and its derivative bounds. Numerics supplies finite scalar circuits with ideal-anchor accuracy. Implementation supplies their actual finite-query realization, exact-only absorption, standalone pre-reserve accuracy, size descent and deterministic counts. Sampling supplies physical rescaling, ideal proximal contraction, ideal-prefix moments, descent and mode-Gaussian termination. Each invocation here satisfies the declared parameter, scale, smoothness and ideal-law hypotheses. No lower-bound theorem from `lower.tex` is used.

References in those source proofs to Picard, stochastic interpolants, Stein kernels and skew dynamics are historical comparisons: the precise lower operations applied here are themselves stipulated and proved in the pinned source. No separate external theorem is silently imported from those comparisons. The one external operation discussed in R154's actual proof is shifted composition. I newly read the local primary *Shifted Composition I* text through the relevant statements and endings: Theorem 3.1, Theorem 3.2 and its entire proof, Remark 3.4, Lemma 3.6 and Theorem 3.7, with the KL conventions/chain rule. The W2 relaxation is explicitly for KL. The sharper shift optimization in its appendix is not needed: R154 supplies and I check its own finite schedule below. Shifted Composition III, inaccurate-gradient LMC, stochastic-oracle sampling, Picard and Gaussian-cloud results are not premises of (1)–(19); full comparator/contribution auditing is deferred, without issuing new verdicts on their claims. Live arXiv metadata for [Shifted Composition I](https://arxiv.org/abs/2311.14520) identifies v1, submitted November 24, 2023; immutable local PDF/text bytes, rather than mutable metadata, bind the proof read.

## Equations (1)–(4): full compiler stability

The scalar setup is delta=d^(-e), declared lambda=delta, l=lambda r^2, L=lambda r. F need not be convex in the primitive interface; it is C2 with Lip(g)<=delta, and all centers and 0<r<=1 are allowed. For R154, F_y(z)=V(y+sqrt(h)z), h=delta/2, so Lip(g_y)<=2h=delta. The query error in this primitive is u=sqrt(h)eta.

The actual terminal calls (`implementation` 228–236) are M=g(x+rZ)+sigma G and S_pre=Z-rg(x+rZ)+(sqrt(3)s/2)G1. With identical seeds their center sensitivities are lambda and r lambda and their oracle perturbations are u and ru. These are deterministic estimates, valid for arbitrary seed magnitudes and errors of either sign.

The actual nonterminal data (`numerics` 590–665, derivation 667–772) are

    b_i=x+r(ell_i y+m_i G), |ell_i|,|m_i|<=1,
    r_i=r tau_i, R/sqrt(5)<=tau_i<=1,
    A_M=C1(1+log d)^C1[(r/sigma)delta^(-4t-10w)+r^2],
    A_S=C1 r^2, A_f,M=C1, A_f,S=C1 r.

M's final direct term is sigma G/2, independent of its position anchor. S's final direct term is y/rho_e, rho_e>=2/sqrt(5); here y is a fixed Gaussian anchor, so it has zero center sensitivity and zero noisy/exact discrepancy. No momentum-anchor discrepancy is present. The mean output nodes have scale exactly rR. Positive declared bounds A and A_f remain available if an actual row has zero coefficients. In the no-term case the implementation returns b0+nG_E, so the zero-row case needs neither division by the actual row sum nor an oracle error term.

The Eval rule (`implementation` 242–286) assigns sigma_i=n/(2A') with declared A'=A or A_f and center noise r_i/(2D_s). Residual noise coefficients and P_i are deterministic scalar data, independent of the center, seed values and replies. Their contributions cancel exactly in a same-seed comparison. No uncounted sensitivity of a variance, square root or seed transformation is present. The residual radicand is nonnegative by the absolute row-sum bound, regardless of the oracle values.

Routine height H is fixed by labels (b+t,p), (b,p), (b-10t,p-1/4), whereas expression depth is D0=3N^2+1. Expanding an uncached expression duplicates the center-supplying subtree, but those occurrences are still direct children of the same routine (`implementation` 160–209). An induction over routine height therefore applies to each occurrence; an inner acyclic ordering treats the expression dependencies. There is no induction once per terminal query.

For final mean children, the scale rR and sigma_i comparable to sigma give the b+t label. For final sampling children sigma_i is comparable to s/r, giving the unchanged label. For nonfinal terms, sigma_i=r tau_prev/(4D_s A), and L_i/sigma_i<=C D_s lambda A/R. With D_s/R=delta^(-2t), c1w<t and b>1/2, the b-10t allowance pays all scale losses. The M anchor has s=R/b_* in [R,1] above the same scalar threshold. Thus `implementation` 469–521 gives, at every reachable scale and label,

    lambda A <= B_d delta^(1/3),                                  (1)

including arbitrarily small top descent radii. This estimate involves no centers or seeds. It is uniform over the finitely bounded label tree; all accumulated polylogarithmic factors have fixed exponents.

Here is a direct check of R154's simultaneous constants. Let C>=max(2,C1) cover fixed direct coefficients, L=L_(k-1), P=P_(k-1), and alpha=L lambda A<=1/2. For exact runs at fixed anchors, the supplied-center discrepancy satisfies

    E_i <= v+alpha max_(earlier occurrences) E_j,
    v=|Delta x|+Cr|Delta a|.

Induction gives E_i<=v sum_(q>=0)alpha^q<=2v. This is a maximum of deterministic discrepancies, never an expected maximum of seeds. It remains true for any finite expression depth or number of duplicated nodes. At the output the sensitivity is <=2 A_f L lambda v. Therefore S has center sensitivity <=2CL r lambda. M has fixed-anchor center sensitivity <=2CL lambda and anchor sensitivity <=2C^2L lambda r. Its anchor b_*S(x,r,R/b_*) contributes at most Lr lambda per unit center displacement, giving additional sensitivity <=2C^2 L^2 lambda^2 r^2. Since lambda r^2<=1, all are dominated by

    L_k=8C^2 L(1+L), L_0=1.                                      (2a)

For perturbations, first compare an erroneous child with the exact child at the erroneous center, then compare the exact child at the two centers. The first comparison allows an arbitrary bounded error at each occurrence and each query, conditional on any preceding history; the second uses only the true-child Lipschitz estimate just established. Hence

    E_i <= Cr|Delta a|+APu+alpha max E_previous,
    output error <= A_f Pu+2A_f L lambda(Cr|Delta a|+APu).          (3)

For S, Delta a=0, and the result is <=2CrPu. For M, |Delta a|<=Pr u because b_*<=1, giving <=CP(2+2CL lambda r^2)u. Both fit

    P_k=8C^2P(1+L), P_0=1,                                       (2b)
    |Mhat-M|<=P_H u, |Shat_pre-S_pre|<=P_H r u.                  (4)

Choose all height constants before making max_k L_k lambda A<=1/2 by increasing d. C1 depends on the fixed numerical orders; it does not depend on d. H is fixed before the interpolation order, and the constants are fixed after that order. This ordering is consistent with the source construction.

The worst local signed alignment, epsilon_i=u sign(a_i)v for a fixed unit vector v, can realize sum_i |a_i|u at a directly weighted error row. Thus one cannot replace an absolute sum by cancellation or by the largest coefficient. The displayed proof already charges this worst alignment. Any amplification inside a supplied center pays lambda at the next exact-child comparison, and alpha bounds its accumulated propagation. It also covers history-dependent alternating errors at duplicate points, discontinuous errors at arbitrarily nearby queries and errors aligned with moved query points. At a terminal moved point x+rZ the true-gradient change is <=lambda|Delta x|, already charged above. Extreme seeds affect output magnitude but not these discrepancy constants or the query count. These universal inequalities, rather than any finite examples, are the reason no missing coefficient case defeats (4).

## Reserves and equations (5)–(8)

The internal independence failure is literal. For a transformed mean child the seed covariance is PP^T=I-vv^T/(4D_s^2). Its shift construction (`implementation` 300–314) adds -2R/b_* to the coefficient of its anchor-sampler reserve; query-affecting slots also have nonzero shift coefficients. Their off-diagonal covariance is -v_i v_j/(4D_s^2), generally nonzero. Drawing that coordinate later with its correct conditional law preserves this dependence. Replacing it by an independent Gaussian would change the compiler. No erroneous-run absorption identity is justified or used.

For a **standalone top sampling call**, its final sG/2 is a separate untouched slot (`implementation` 714–726). It occurs in no query. The algorithm can and R154 explicitly does draw it after the entire finite query block. The permitted oracle observes past/current queries and replies and has private randomization; it cannot observe a future private draw. Delaying this unused top slot changes no observed prefix or reply kernel, even for a stateful strategy. This does not assume the adversary is oblivious, or that the internally transformed slots are independent. Allowing disclosure or anticipation of the future reserve would change the specified model.

Given an incoming state s, let W contain every pre-reserve random seed and the reply-kernel randomization for this call. It has a common law zeta_s for the two comparison experiments. The exact computation ignores the erroneous replies but uses the same earlier algorithm seeds; its marginal is the exact compiler at the given center. It need not have the same transcript. For pre-reserve centers a_s(W),b_s(W), Gaussian translation followed by projection gives

    KL(Law(a+sqrt(v)G)||Law(b+sqrt(v)G))
       <= integral |a-b|^2/(2v) dzeta_s <= D^2/(2v).              (5)

This is the RN/chain-rule computation on (W,output), not a density calculation for an inconsistent potential. In physical coordinates D<=C_*h eta and v=h/4, so

    KL(noisy compiler || exact compiler)<=2C_*^2h eta^2.          (6)

The two factors sqrt(h) are respectively the normalization of the gradient and the final spatial rescaling. The ideal proximal law is not the denominator here.

For completeness, a causal strategy is a sequence of measurable reply kernels on finite real observation histories, as R154 states. Fixed d gives a deterministic finite query horizon; finite unions of products of real spaces, with discrete counters, are standard Borel. Kernel randomization can be represented by independent uniform variables. One need not disintegrate a hypothetical nonstandard hidden memory space: the strategy is represented by its real-valued conditional replies. Carried algorithm variables and relevant prior histories can be included in this Borel state, while future algorithm seeds remain fresh. On unsupported histories, define an admissible reply kernel, e.g. the exact reply. Alternatively project each reply to the closed permitted value interval and gradient ball about the true oracle. This projection is measurable for fixed V, fixes every admissible realized reply, and gives a globally bounded extension. This is only an analytical definition of hypothetical histories, not free computational access to V in the actual algorithm.

There is a concrete all-history version of the disintegration in (7). If T_s(W,z) encodes the completed carried state (including a recovered reserve if retained), the actual density

    k_s(z)=integral phi_v(z-a_s(w)) zeta_s(dw)

is finite, strictly positive and jointly measurable for every s,z. Define L_s(z) by weighting zeta_s(dw) with phi_v(z-a_s(w))/k_s(z) and mapping w to T_s(w,z). Then K_s(dz,ds')=k_s(z)dz L_s(z,ds') for every s. This also proves there is no unhandled exceptional history in the Gaussian application. General Borel disintegrations suffice for the incoming-y replacement; arbitrary measurable probability extensions on null sets are legitimate there. The visible variable is stored separately from a possibly inconsistent synthetic transcript, so no computational consistency of the replacement transcript is presumed.

For any replacement marginal e_s and E_s=e_s L_s, if k_s<<e_s the RN derivative is dk_s/de_s evaluated at z: integrating against rectangles verifies it. Thus KL(K_s||E_s)=KL(k_s||e_s). Applying the same kernel gives TV<=TV(k_s,e_s), and projecting onto z gives the reverse inequality. This proves (7), with TV equality even without absolute continuity. Gaussian-mixture marginals are equivalent to Lebesgue measure; k_s-null and e_s-null exceptional sets coincide in the KL application.

Starting with the identical joint law after warm-up, use E_s with exact-compiler visible marginal at each step. Integrating L_s over its probability space gives that marginal conditional on the entire **preceding** enlarged history. Thus the visible replacement chain is exactly the exact-compiler Markov chain. It is not the transcript of a physical exact-oracle run. Chain rule in the direction actual||replacement sums (6) under actual prefixes, where the bound is uniform. Projection and Pinsker yield

    KL(actual path||replacement path)<=2C_*^2mh eta^2,
    TV(actual endpoint, exact-compiler endpoint)<=C_*eta sqrt(mh). (8)

No conditioning on future states, future success or future private seeds occurs. No regularity of erroneous replies or full-transcript closeness is required.

## Equations (9)–(12): fixed physical-time smoothing

`sampling` 31–66 gives P_h(y)=kappa_y*N(0,hI), invariant law pi_tilde=pi_V*N(0,hI), and W2(kappa_y,kappa_z)<=q|y-z|, q=(1+h)^(-1). Its entrance follows from curvature 1+1/h of the conditional potential and gradient difference (y-z)/h, using `preliminaries` 106–195. The joint law pi_V(dx)N(x,hI)(dy) proves invariance directly. Coupling the conditional draws and applying (5) with v=h gives

    KL(P_h(y)||P_h(z))<=q^2|y-z|^2/(2h).                          (9)

Every finite-second-moment input remains such: conditional moments follow from the same strongly convex laws, and Gaussian convolution preserves them. For mu_j=mu P_h^j, nu_j=nu P_h^j, start rho_0=nu. At each j<m choose an optimal W2 coupling (X,Y) of the deterministic laws mu_j,rho_j; existence follows by tightness and lower semicontinuity of squared distance. No global selection over all pairs of measures or algorithmic transport oracle is required. Define theta_j=1/(m-j), Z=(1-theta_j)Y+theta_j X, rho_(j+1)=Law(Z)P_h. Contraction and this coupling give

    a_(j+1)<=q(1-theta_j)a_j,
    a_j<=q^j(m-j)a_0/m, rho_m=mu_m.                              (11)

The endpoint is exact because theta_(m-1)=1. It is not a limiting approximation. Disintegrate the coupling with respect to Y and let K_j(y) be the resulting mixture of P_h(Z). Compare rho_j(dy)K_j(y,dz) with nu_j(dy)P_h(y,dz). Chain rule and projection, followed by conditional mixture convexity in the orientation P_h(Z)||P_h(y), give

    KL(rho_(j+1)||nu_(j+1))
      <=KL(rho_j||nu_j)+(q^2/(2h))theta_j^2 a_j^2.                (12)

Initially KL(rho_0||nu_0)=0, including when mu and nu are singular. Positive Gaussian transition densities ensure the conditional absolute continuity, and the finite integrated bound inductively ensures rho_j<<nu_j and finite KL. An arbitrary extension of the disintegration off rho_j's support does not change this inequality. Summing the exact schedule gives

    KL(mu P_h^m||nu P_h^m)
      <=q^2 a_0^2/(2hm^2) sum_(j=0)^(m-1)q^(2j)
      <=a_0^2/(2hm),
    TV(mu P_h^m,nu P_h^m)<=a_0/(2sqrt(hm)).                      (10)

The case m=1 is included. Taking m=ceil(1/h) gives hm>=1 and avoids the one-step h^(-1/2) loss. This derivation closes the actual regularization premise without the stronger Renyi, W-infinity, continuous-time or optimized-shift claims. It is the known shifted-composition mechanism, with no novelty decision here.

## Equations (13)–(19): complete uniform error budget

Let a_j=W2(actual visible law,pi_tilde). The supplied mode gives RMS(pi_V)<=sqrt(d), hence RMS(pi_tilde)<=C sqrt(d). At each actual incoming state, (4) costs C_*h eta in physical W2. Source `sampling` 88–99 supplies exact-compiler/ideal local W2 error sqrt(h)B_d delta^K0(sqrt(d)+2sqrt(h)|y|). Conditional couplings and Minkowski, with RMS(y)<=a_j+C sqrt(d), give exactly

    a_(j+1)<=(q+2hB_d delta^K0)a_j
              +C sqrt(h)B_d delta^K0 sqrt(d)+C_*h eta.           (13)

This is valid with arbitrary carried state. Finiteness of moments can be proved before solving the recurrence: exact compiler moments are finite for each incoming center by the source bound, and the noisy output is within a uniformly bounded same-seed displacement. Induction and the at-most-linear conditional moment bound propagate finite moments from zero. No expectation of a nonlinear adversarial error is differentiated.

For large d the coefficient is <=1-c0h. With T=ceil(C h^(-1)log d), sum the geometric recurrence to get

    a_T<=C sqrt(d)exp(-c0hT)
           +C h^(-1/2)B_d delta^K0 sqrt(d)+C_*'eta.              (14)

K0>2+1/e implies e(K0-1)>e+1>1/2. Thus the intrinsic term is o(sqrt(h)); a fixed sufficiently large warm-up constant makes the transient so too. All estimates are uniform over V, state and eta<=1.

For the next m=ceil(1/h) calls, first apply (8) with the actual warm-up joint law as common initialization. Its cost is <=C_*eta sqrt(1+h). Only then compare exact compiler and ideal kernels, using their source TV interface

    TV(Phat_h(y),P_h(y))<=B_d delta^K0(sqrt(d)+2sqrt(h)|y|).       (15)

Use hybrids mu P_h^j Phat_h^(m-j). The prefix before the differing step is ideal, with RMS bounded by C sqrt(d)+a_T via contraction. Consequently

    sum intrinsic TV<=B_d delta^(K0-1)(C sqrt(d)+C_*'eta)=o(1).   (16)

An enlarged B_d covers the uniform transient remainder. This telescoping does not use moments under an uncontrolled erroneous or exact-compiler prefix. Apply (10) to mu and invariant pi_tilde and combine with (14). This yields

    TV(actual window endpoint,pi_tilde)<=C_*''eta+o(1).           (17)

There is no noisy-to-ideal KL assertion and no accumulation of the noisy one-step TV bound over m steps.

For descent, first disintegrate the actual incoming law given y and replace its marginal by pi_tilde, retaining the conditional carried state. Identity (7) pays exactly (17); applying the remaining actual algorithm contracts TV. Fix this y and keep the same true normalized F_y throughout descent. At each radius r_j=2^(-j/2), noisy/exact TV is <=C_*r_j sqrt(h)eta by (4), the standalone reserve and Pinsker. Exact/ideal TV is <=B_d delta^K0(sqrt(d)+|g_y(x_j)|). These two costs can be charged together at a single joint-state replacement. At each compared step the prefix is ideal; the later algorithm is the same kernel. Therefore the source ideal-prefix moments, rather than actual-prefix moments, are the relevant ones.

Indeed, conditional ideal observations satisfy RMS(Y_j|history)<=C(sqrt(d)+r_j|g_y(x_j)|). Updating x_(j+1)=x_j+r_jY_j/2 gives b_(j+1)<=(1+C delta r_j^2)b_j+C delta r_j sqrt(d). Since both geometric radius sums converge, b_j<=C sqrt(d) uniformly, starting from y~pi_tilde. Thus intrinsic cost is CJ B_d delta^K0 sqrt(d)=o(1), while the noisy cost is <=C sqrt(h)eta sum_j r_j. There is no hidden J factor multiplying eta.

At the terminal scale let l=delta r_J^2. Comparing the erroneous and true fixed-point iterations, both starting at zero, gives d_(k+1)<=l d_k+r_J sqrt(h)eta. This proves the finite-iteration bound

    d_m0<=(1-l^m0)r_J sqrt(h)eta/(1-l)
          <=r_J sqrt(h)eta/(1-delta r_J^2).                      (18)

No erroneous derivative is used. The fresh standard Gaussian at termination pays this displacement in TV. The two exact source base remainders (`sampling` 280–355) are

    C delta 2^(-J)sqrt(d)
    +C(delta 2^(-J))^m0 2^(-J/2)sqrt(d)/(1-delta 2^(-J)).

The source's fixed J=ceil(C1 log d), m0=ceil(C2 log d) make them vanish. The mode-Gaussian comparison assumes only l<=1/2 and the C2 bounded-Hessian primitive, which hold here.

Finally, the conditional identity Z=Y/2+Z_new/sqrt(2) and the center update show x_j+r_jZ_j=x_(j+1)+r_(j+1)Z_(j+1). Thus the fully ideal descent returns a draw from kappa_y, and averaging over y~pi_tilde returns **pi_V**, not pi_tilde. Data processing through the final affine map pays all the preceding conditional errors. This gives (19), TV(output,pi_V)<=C_e eta+o(1), for the unnoised target.

One explicit simultaneous envelope for the o(1) terms, after fixed constants are enlarged, is

    R(d)=C sqrt(d)exp(-c0hT)
       +C h^(-1/2)B_d delta^K0 sqrt(d)
       +B_d delta^(K0-1)(sqrt(d)+1)
       +CJ B_d delta^K0 sqrt(d)
       +C delta 2^(-J)sqrt(d)
       +C(delta 2^(-J))^m0 2^(-J/2)sqrt(d)/(1-delta 2^(-J)).

Every summand tends to zero. The remaining coefficients of eta are bounded independently of d since mh<=1+h, sum r_j<infinity and 1-l is uniformly positive. This envelope is valid simultaneously for eta<=1, all admissible potentials and all causal strategies. Select provisional c<=1 with C_e c<=1/40, then a uniform integer threshold d0 with R(d)<=1/40 and all source/absorption conditions for d>=d0. Reducing c later does not change d0.

For 2<=d<d0, use R154's unchanged downward-slack acceptance. With a(x)=exp(-V(x)+|x|^2/2),

    exp(-2c)a(x)<=ahat(x)=exp(-Vhat(x)+|x|^2/2-c)<=a(x)<=1.

The exact capped algorithm with L_d=ceil(4*2^(d/2)) has target-law accepted proposals and failure <=exp(-4). Couple the noisy and exact capped algorithms with common fresh Gaussian proposals and accept uniforms, exposing each uniform only after the value reply. Conditional on any common prefix and proposal the disagreement probability is <=1-exp(-2c)<=2c. A first-disagreement union bound gives

    TV(noisy capped output,pi_V)<=exp(-4)+2L_d c.

This does not claim that the noisy accepted law is pi_V or that its own failure probability is exp(-4). R154 explicitly invokes the exact capped comparison at original line 196, so I157's clarification is already an available reading of the unchanged proof. Decrease c to at most 1/(80 max_(2<=d<d0)L_d), with the empty case omitted. This is positive and makes fallback TV<1/10; the large-d bound remains <=1/20.

Every top primitive has <=B_d delta^(-t) queries regardless of center, replies or seeds. Warm-up plus window has O(delta^(-1)log d) calls; descent and mode iteration have fixed O(log d) lengths. Their total is <=B_d delta^(-(1+t)). Choose 0<e<min(1,epsilon/2), integer K0>2+1/e, then t satisfying 40(K0+2)t<1/4. Set the Picard depths, H and expression depth; choose w with the source count inequalities; finally choose fixed interpolation orders and the constants above. Then e(1+t)<epsilon, so the polylogarithm fits C_epsilon d^epsilon. Increasing C_epsilon covers the finitely many L_d. Residual square roots, circuits and labels are prescribed before replies; no seed-magnitude cutoff, convergence-based stopping or exceptional execution evades the cap.

## Original-proof ruling, historical failures and evidence limits

I157's three clarifications survive independent challenge without changing R154: original lines 84 and 108–116 already require fresh standalone reserves and a synthetic state-retaining process; original line 196 already compares to the exact capped sampler. The explicit posterior and first-disagreement arguments above justify those existing steps. They do not replace the algorithm or add a hypothesis. No separate repaired theorem is needed or supplied, and no old file is rewritten.

The internal-reserve blanket claim in original I152 and its selective parent response stays FAIL. Standalone R2 and its R3/R4 uses survive because they need only top-call reserves, as already restricted in R154. Original dimension-independent R152 stays unresolved at its original scope. Historical I133 I.5, I124 arbitrary-Q cutoff, I112 standalone G112 and I112 zero-lambda scale-fixing failures, and all parked-branch restrictions, remain preserved in the bound reports; this is not a new audit of them.

Evidence is scoped to original records and actual R154 dependencies. `dependencies.json` records every source edge and the stipulated boundary; `immutable.json` binds their bytes; `context-coverage.json` distinguishes newly displayed passages from the complete context supplied in this task and from older material retained only by reference. There is no claim of a new semantic read of the 7,800-line older stream or the full corpus. Four live ledgers have immutable snapshots and are the only explicitly permitted live drift. Active I158 and unrelated-project files are not bindings. Failed/truncated attempts, including a wrong working-directory read and an out-of-range read, are preserved in `attempts.json`, with recoveries or nonreliance stated.

One canonical owned inventory is prevalidated and sealed once by exclusive creation. Replay checks immutable bytes, exact decoded-field regeneration, embedded original occurrences, new read ranges, pinned source Git blobs, source closure, status and owned inventory. It denies filesystem mutation, network, subprocesses and bytecode writes and cannot repair or reseal. No ancestor verifier, diagnostic or converter is run; no corpus is copied. No finite numerical tests are used to certify the universal claims. Run from the project root:

    python3 -B frontier/experiments/i159_oracle_tolerance_focused_r3/verify.py

A successful replay establishes evidence consistency only. The correctness PASS above rests on the mathematical argument under the stated premises. Contribution and acceptance remain for a separate gate; the broad I157 review remains incomplete.
