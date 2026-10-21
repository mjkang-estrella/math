# Source223 prefreeze derivations

This is a discovery notebook, not a frozen theorem or an author-proof nominee. Constants below are allowed to depend on a fixed mass and a fixed square; no uniformity in mass, disorder strength, or q approaching 4 is asserted. Source names, exact operative labels, primary versions and original-history comparisons are in private/COMPARISON.md and the private reading records. N denotes the authenticated natural-occupation source, T the thermal source, and Q the quenched source. All pinned source proofs are stipulated true.

## 1. The full-horizon continuum operation is already paid

Use the positive-mass thermal law in a fixed square, with its prescribed opposite corners and wired/free banks. Write kappa=16/3, b_t=(2pi/3)C_t, and u_t=b_t/sqrt(kappa). The actual T energy proposition, together with its deterministic potential bound C_t<=K J_t, gives

    A := E_P integral_0^infinity u_t^2 dt < infinity.

This is an expectation on the entire capacity half-line, not merely almost-sure finite energy on each finite interval. Its constants can be obtained using the standard uniformly bounded square approximations; universality then identifies the same continuum law. There is no need to transfer a diameter estimate from an arbitrary large approximating domain.

On the probability space of the weak solution, X=W/sqrt(kappa)=B+U, where U_t=integral_0^t u_s ds. The full-half-line entropy inequality for an adapted Brownian shift gives

    H(Law(X) | Wiener) <= A/2.                         (1)

For completeness, the localization operation is short. Stop U when its accumulated squared derivative reaches n. For this stopped drift the inverse stochastic exponential is a uniformly integrable martingale by the deterministic energy bound n. Girsanov and data processing bound the entropy of Law(B+U^n) by (1/2)E||U^n||_H^2. Almost surely U^n=U eventually, since ||U||_H^2 is finite; in particular B+U^n converges to B+U in the compact-open path topology. Lower semicontinuity of relative entropy and monotone convergence give (1). This is exactly a classical primary operation, independently read; it does not require a new global Novikov estimate, a solution of the SDE under the critical law, or a reverse change of measure.

The Loewner trace, completed at its terminal prime end, is a measurable function of its driver on the full-measure trace set. Scaling the driver and taking this function in (1) gives

    H(P_curve | Q_SLE) <= A/2, hence P_curve << Q_SLE.  (2)

Only this direction is established here. The initial exploratory suggestion of proving equivalence by repeating the energy proof under the critical law is unnecessary for (2) and was not developed. Negative mass can be treated relative to the reversal of the opposite-end critical law by the exact dual/reversal prescription; no orientation-sensitive reversal claim beyond that prescription is needed.

Consequently all measurable almost-sure properties of the critical curve transfer: existence of interior Minkowski content, additivity along the ordered trace, strict increase and local continuity of its natural clock, and the whole-square finite measure and zero boundary mass supplied by N. This is a continuum construction. It contains no assertion about lattice traversal counts.

The quantitative event estimate following from data processing to {E,E^c} is useful later. Set a=P(E), z=Q(E). For 0<z<1,

    H(P|Q) >= a log(1/z)-log 2,
    P(E) <= min(1,(H(P|Q)+log 2)/log(1/Q(E))).        (3)

Indeed, the binary entropy a log a+(1-a)log(1-a) is at least -log 2, and the remaining term -(1-a)log(1-z) is nonnegative. The z=0 case is absolute continuity. In particular reference convergence in probability transfers. Finite entropy by itself does not transfer first or second moments. The next argument supplies actual second-moment control through arms.

## 2. A paid near-critical upper-bound construction

Here only regular square approximations are considered, with nearest-neighbor spacing h, q=2, and the thermal parameters of T. The isoradial circumradius is h/sqrt(2), a distinction required when comparing the natural counting constant. No equality of these two mesh conventions is used.

Choose a fixed physical length ell>0, small enough that all annuli of diameter at most 100ell are below the characteristic length for the given mass. This is possible uniformly along the mesh sequence by the near-critical rectangle/characteristic-length inputs. The finitely many initial meshes can be ignored. The primary two-arm stability theorem and N's sharp critical two-arm estimate imply, in the full plane, for fixed-size inner starts and r<=ell,

    P_thermal(A_2(O(h),r)) <= C (h/r)^x,
    P_thermal(A_2(epsilon,r)) <= C (epsilon/r)^x,
    x=1/3, d=2-x=5/3.                                (4)

Only an upper bound is needed here. No exact rooted amplitude is inferred from (4).

The same upper bound, with another constant, holds for these arm events in a ball protected by a fixed-ratio bulk annular collar, uniformly over the boundary partition outside the collar. This particular extension uses no arbitrary jagged-quad crossing theorem. The proof of the source's bounded-density collar comparison uses one primal and one dual circuit in a full annulus, the domain Markov property, FKG, bounded rank costs for the fixed through wires, and the extrema of the remote likelihood ratio. Both circuits are obtained from finitely many rectangles. The near-critical rectangle bounds are uniform at the chosen scales, and all the other operations are finite FK identities at the same p. Thus the full-annulus instance of that proof applies verbatim with constants depending on the chosen characteristic-length fraction. Comparing the inside marginal with the infinite-plane law proves the assertion for every nonnegative inside event. This does NOT extend the source's two-arm outward coupling with arbitrary jagged exposed walls; that separate issue appears in Section 5.

Let z_e be a counted medial edge midpoint, and s_e its distance from the square boundary. If the Dobrushin interface traverses e and a ball around e lies inside the square, it has a primal and a dual arm out of this ball. Hence (4), with a protected collar, gives

    P(e traversed) <= C [h/max(h,min(s_e,ell))]^x.     (5)

Boundary-edge points and terminal connectors are handled separately: connectors have no mass by the convention, and there are O(h^-1) edges within O(h) of the boundary. A countable multiplicity of visits to a vertex is irrelevant: the readout counts the specified medial edge traversals, and each edge has the bounded multiplicity in that convention.

For distinct e,f, take two disjoint protected balls of radius a small fixed multiple of

    r_ef=min(s_e,s_f,|z_e-z_f|,ell).

When r_ef>=C_0 h, the necessary two-arm events have disjoint supports. Condition on the configuration outside the first protected ball and use its uniform conditional upper bound, then do the same for the second. This proves

    P(e and f traversed) <= C(h/r_ef)^(2x).           (6)

If r_ef<C_0 h, the trivial upper bound 1 gives the same formula with r_ef replaced by max(h,r_ef), after changing C. No independence of FK edges, no independent-environment resampling, and no increasing-event property of the two-arm event was invoked.

Define M_h=h^d times the number of counted traversals. Equations (5)-(6) yield

    sup_h E M_h < infinity,
    sup_h E M_h^2 < infinity.                         (7)

Here is the summation rather than just a dimensional slogan. The off-diagonal contribution is bounded by

    C h^4 sum_{e!=f} [max(h,min(s_e,s_f,|z_e-z_f|,ell))]^(-2x).

The integrand is at most a constant times

    ell^(-2x) + max(h,s_e)^(-2x) + max(h,s_f)^(-2x)
                 + max(h,|z_e-z_f|)^(-2x).

For 2x=2/3 the boundary-normal integral is finite, since integral_0^1 t^(-2/3)dt=3, and the planar diagonal integral is finite, since integral_0^1 t^(1-2/3)dt=3/4. The corresponding lattice sums have the same uniform bounds by dyadic boundary strips and distance shells. The diagonal e=f contributes at most C h^(2d-2)=C h^(4/3), even using probability 1. This proves (7). The single-point calculation also gives, for a physical boundary strip of width a,

    E[h^d # traversals in strip(a)]
        <= C(a^(1-x)+h^(1-x)) = C(a^(2/3)+h^(2/3)).  (8)

For a fixed eps>=C_0 h, a hit of the eps-ball around a bulk point forces two arms from scale eps to any smaller protected outer scale. The same disjoint-ball argument gives

    P(hit B(z,eps), hit B(w,eps))
      <= C min(1,[eps/min(s_z,s_w,|z-w|,ell)]^(2x)).  (9)

In the regime where the denominator is O(eps), use the trivial bound, not the displayed power without its minimum. At points within O(eps) of the boundary this is also the correct trivial bound.

Let T_eps(gamma)=eps^(-x) 1{dist(z,gamma)<=eps} dz on the square. The curve convergence of T, using open disk hits and Portmanteau followed by radius approximation, passes (9) to its continuum law. Integration with the same boundary/diagonal estimates proves

    sup_{eps small} E_P[T_eps(gamma)(square)^2] <= C. (10)

The physical and disc curve topologies agree for these fixed square approximations through the uniformly continuous boundary uniformizations; the arbitrary-domain localization theorem alone would not justify this assertion for Euclidean mass in long narrow appendages.

By (2), the critical whole-square tube convergence transfers in P-probability. Select an almost-surely convergent subsequence of tube radii and apply Fatou to (10). The thermal continuum natural mass Theta therefore satisfies

    E_P Theta^2 <= C.                                (11)

This is actual occupation moment control, obtained through discrete near-critical arms plus the source energy operation. It is stronger than simply identifying the thermal curve as a Loewner trace. It still does not prove that the lattice count converges to c(2)^(-1)Theta: (7)-(8) give tightness and boundary control but leave identification of subsequential measures unpaid. No contribution grade is assigned to (7)-(11); their operations are explicit compatible source/primary upper-bound compositions, so they are not offered as the requested substantial nominee.

## 3. A complete entropy-transfer reduction for marked curve laws

This abstract reduction is proved here to make the exact discrete obligation testable. It is not a conditional research finding. Let E be a Polish curve space and F the space of finite positive measures on a compact metric domain with a bounded metric inducing weak convergence. Let gamma_h be a discrete curve and nu_h its actual traversal readout on one finite sample space. Let Q_h be the reference critical law and P_h the perturbed law on that same sample space, or on a deterministic exploration record sufficient to determine both readouts. Assume:

(a) gamma_h under Q_h converges to Q and under P_h converges to P;
(b) T_eps:E->F are Borel maps, continuous at Q-almost every curve for a sequence eps decreasing to zero;
(c) T_eps(gamma) converges in Q-probability to a Borel measure map M(gamma);
(d) for every a>0, lim_{eps->0} limsup_{h->0} Q_h[d_F(nu_h,T_eps(gamma_h))>a]=0;
(e) H(P_h|Q_h)<=K, uniformly in h.

Then

    (gamma_h,nu_h) under P_h => (gamma,M(gamma)) under P. (12)

Proof. Relative entropy decreases under gamma_h. The variational formula and weak convergence of both curve marginals imply H(P|Q)<=K: for bounded continuous f, pass to the limit in integral f dP_h-log integral exp(f)dQ_h, then take the supremum. Thus P<<Q. For each fixed selected eps, T_eps is P-almost surely continuous, and the continuous mapping theorem gives convergence of (gamma_h,T_eps(gamma_h)) to (gamma,T_eps(gamma)) under P. Equation (3) with the same K transfers (d) to P_h, with the two limits in exactly the same order. It also transfers (c) to P. The converging-together argument in the product metric proves (12): for a bounded 1-Lipschitz test, replace nu_h by T_eps(gamma_h), discard a discrepancy event, take h to zero, and finally let eps and then the discrepancy threshold go to zero. This proves joint convergence including total mass because F is the finite-measure space on a compact domain, not merely the vague topology in the interior.

One can avoid the continuity qualification for sharp tubes by using smooth distance cutoffs. If F(t) is continuous, equals 1 on [0,1] and 0 on [2,infinity), then

    T_eps^F(gamma)(dz)=c_F eps^(-x) F(dist(z,gamma)/eps) dz

is continuous for each eps under uniform curve convergence. Writing a monotone F as a mixture of disk indicators, choose c_F=[integral t^x(-dF(t))]^(-1), so its mixture has the same limiting content. Critical replacement for these mixtures follows from N's disk replacements, a fixed finite approximation to the mixture, and its uniform first/second-moment bounds. This avoids any claim that every sharp distance level is automatically a continuity set for every curve.

Finite entropy is sufficient; entropy tending to zero is unnecessary. Conversely, bounded entropy of the limiting law P relative to Q does not imply (e). As a simple check, partition [0,1] into n equal cells and in each retain a subinterval of relative width exp(-n). Let Q_n be Lebesgue measure and P_n uniform on the retained union. Then P_n and Q_n both converge weakly to Lebesgue measure, while H(P_n|Q_n)=n. An unbounded mark can distinguish the retained sets. Thus continuum drift identification and even continuum entropy cannot be used backwards to pay (e).

For the thermal occupation problem, take nu_h=c(2)h^(5/3) times the specified traversal counting measure. Conditions (a)-(d) follow from the actual critical joint natural-occupation theorem and the thermal curve theorem, after using the fixed square mesh convention. In particular, the critical joint limit itself gives (d) for each continuous tube map followed by eps tending to zero; no new uniform microscopic rate is inferred. Hypothesis (e) for the thermal exploration record has not been proved here. This is a sufficient route which bypasses a direct thermal calibration, not an extra unproved premise smuggled into a theorem.

## 4. Exact discrete information identity and where the estimate must enter

Choose a deterministic adaptive exploration algorithm which reveals enough information to determine the ordered medial interface and the count. Pad the record after it stops with a deterministic symbol, giving a common finite maximum length. For a live nonforced binary query e_i and a history H_i having positive probability under both laws, let p_i^m(H_i),p_i^0(H_i) be the two conditional open probabilities. Because these are FK laws with the same graph and q=2 and edge weights bounded away from 0,1, all such probabilities lie in a common [a,1-a]. Forced steps have equal deterministic answers and zero entropy cost. Factorization of the history probabilities gives the exact chain rule

    H(P_h^record|Q_h^record)
       = E_m sum_i D_Ber(p_i^m(H_i) || p_i^0(H_i)).   (13)

The elementary log t<=t-1 inequality gives

    D_Ber(p||q) <= (p-q)^2/[q(1-q)].                 (14)

Hence the concrete sufficient estimate for (e) is

    sup_h E_m sum_i |p_i^m(H_i)-p_i^0(H_i)|^2 < infinity. (15)

There is an exact response formula for each summand. Use uniform log-odds parameter lambda, so the FK weight is exp(lambda N)2^k. For the SAME fixed history H, let rho_lambda^H be the conditional law of the still-unqueried edges, with its induced graph and partition. Differentiating its finite partition function gives

    d/dlambda E_lambda^H omega_e
       = Cov_lambda^H(omega_e,N_unrevealed).

Therefore

    p_i^m(H)-p_i^0(H)
      = integral_{lambda_0}^{lambda_m}
          Cov_lambda^H(omega_ei,N_unrevealed) dlambda. (16)

Cauchy-Schwarz gives a second explicit sufficient budget:

    C |lambda_m-lambda_0| E_m sum_i
       integral_{lambda_0}^{lambda_m}
          |Cov_lambda^{H_i}(omega_ei,N_unrevealed)|^2 |dlambda|.
                                                               (17)

For reversed limits, integrate over the unoriented interval. The outside expectation remains the thermal record law; the intermediate conditional law is a separate evaluation on the SAME fixed record. One cannot silently average it under the critical exploration or replace an explored disordered environment by fresh iid disorder.

The square thermal parametrization has |lambda_m-lambda_0|=O_m(h). To check the normalization directly, expanding U_k(A)=2K(k)theta/pi gives A=theta+(k^2/8)sin(2theta)+O(k^4); k^2=16r+O(r^2). At theta=pi/4, A-pi/4=2r+O(r^2). The FK log-odds is log sqrt(2)+log sin(A/2)-log sin(pi/4-A/2), whose derivative at pi/4 is cot(pi/8)=1+sqrt(2). Since r/delta->|m|/2 and delta=h/sqrt(2), the shift is of order mh, with the sign set by duality. This calculation establishes the scale, not (15).

As an exponent diagnostic only, if a path-length exploration satisfies E_m number_of_queries<=C h^(-5/3), then a uniform bound |p_i^m-p_i^0|<=C h^(5/6) would pay (15). A weaker averaged square estimate also suffices. It is not enough to note that the local edge weight changes by O(h): the conditional probability includes the response of the entire unresolved FK graph through (16). The fully conditioned single-edge FK probability is local only when every other edge has already been fixed. Interface exploration does not reveal all those edges.

The primary near-critical derivative estimates apply to buffered regular quads/annuli and include contributions of edges as far away as the characteristic length. They do not directly bound (16) at every random moving slit tip with the needed summed square. The source continuum potential energy is the limiting analogue of such a budget, but no uniform discrete version or uniform-integrability passage of that information budget was found in the read operative proofs. Formulae (13)-(17) exhibit the exact missing estimate, including its quantifiers and measure, rather than just naming 'uniform integrability'.

## 5. Direct replacement after the strongest annular comparison

The published primary relative arm stability is stronger than up-to-constant RSW. For two alternating arms below the characteristic length it gives

    exp[-C(R/L)^zeta] <= pi_2(p;R)/pi_2(pc;R)
                        <= exp[C(R/L)^zeta],         (18)

with zeta>0. Its proof integrates an ABSOLUTE upper bound on the logarithmic derivative. The published version corrects a misleading stronger-looking derivative display in the old preprint. The statement explicitly does not claim half-plane arm stability with boundary conditions imposed on the half-plane.

At physical outer radius rho, (18) supplies an error tending to zero with rho. It is compatible with, and must be inserted into, the critical replacement mechanism. It does not by itself identify the relative probabilities of the exact rooted medial-edge event and the disk event, nor does it give an exact match of their transmitting outer partitions.

Suppose these two specific extensions were established at the thermal parameter:

(i) relative microscopic-edge/disk calibration for the N starts, with the SAME critical coefficient and an extra error O((|m|rho)^zeta);
(ii) the N outward two-arm coupling, keeping the original transmitting primal/dual regions and arbitrary positive exterior reweighting, at all scales up to rho, with failure C(s/rho)^c_out.

These are hypotheses of this calculation only. Conditional on them, set rho=eps^b. The normalizations in N's separated-pair proof are at most C rho^-x. The continuation probability is at most C rho^x by (4), which cancels this factor for the calibration and collar-mixing errors. The mismatch in the continuation coupling costs at most C rho^-x(eps/rho)^c_out. Thus the separated-pair error is bounded by

    C[eps^((1-b)c_out-bx) + eps^c_cal
          + eps^(b c_mix) + (|m|eps^b)^zeta] + o_h(1). (19)

For example, choose b=c_out/[2(c_out+x)]; the first exponent is exactly c_out/2, and every other displayed exponent is positive. At near pairs, N's integrable bound gives the diagonal budget g^(2-2x)+eps^(2-x), and at the square boundary (8) gives a^(1-x)+h^(1-x). Here x=1/3, so the exponents are respectively 4/3,5/3,2/3. First take h to zero, then eps to zero at fixed g,a, then g,a to zero. This closes the entire L2/first-moment replacement algebra with no loss at fixed nonzero mass, IF (i)-(ii) are paid. There is no claimed quantitative rate in h because the source uses ordered limits.

The bounded-density full-annulus comparison used in Section 2 is not (ii). N's proof of (ii) has an extra wall-to-wall reference band and a common transmitting partition even under conditioned two arms. The primary general-quad proof at criticality pays boundary contact using a first-moment parafermionic argument followed by renormalization. The near-critical rectangle bounds alone do not instantiate that critical first-moment proof. Conversely, nothing here proves that another published flower-coupling argument cannot supply the same reference band. This notebook leaves that operation unproved rather than claiming it is impossible or inherently substantial.

For (i), finite-energy comparisons between a fixed rooted start and a round annular start only give multiplicative constants; these constants do not tend to one. A plausible route is to adapt the signed covariance/pivotal-box proof of (18) to the exact rooted two-arm event with its finite local connectivity pattern. The finite root cost is harmless for comparability, but a full normalized derivative estimate for that event and its conditional matching data has not been established here. No unproved 'standard adaptation' is used to infer the critical calibration constant.

## 6. Scope decision

There is no frozen result and no full author-proof nominee. The work has produced full compatible reductions, actual near-critical count and continuum-content moment bounds, and two concrete alternative remaining mechanisms, (15) or (i)-(ii). Neither alternative was completed at the actual thermal lattice scope. The fixed-disorder occupation target already present in operative original history is not renamed or retried. Q's common scalar cancellation for fixed terminal-scale partition ratios gives no summable microscopic marked error; its fixed-disorder curve convergence cannot substitute for (15), (i), or (ii).

The endpoint q=4 curve theorem was read as a separate source scope, not as a limit of N. The necessary wall crossing and calibrated occupation estimates are not asserted there by the statements used here. No endpoint occupation theorem, q<1 theorem, arbitrary-domain Euclidean-mass theorem, or variable-disorder/thermal theorem is frozen. This is a bounded discovery conclusion, not an exhaustion or worldwide-priority claim.
