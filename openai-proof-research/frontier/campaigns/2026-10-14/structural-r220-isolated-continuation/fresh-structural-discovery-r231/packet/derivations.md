# Source355 — prefreeze integrated calculations

No discovery-level statement is frozen here. These are exploratory derivations, with all upstream operations at the required pin treated as true. Nothing here assigns a mathematical grade or count. The aim is an extension retaining original ambient axes at the first singularity; the scalar calculations below are not a substitute nominee.

## 1. Exact nonautonomous equation and energy

Use vector mean curvature H, with normal velocity X_t^perp=H+F(t,X)^perp. Fix (x0,T), put h=T-t=e^{-tau}, Y=h^{-1/2}(X-x0), and Sigma_tau=h^{-1/2}(M_t-x0). Since dt/dtau=h and H_Sigma=h^{1/2}H_M,

    (Y_tau)^perp = H_Sigma + Y^perp/2 + g(tau,Y)^perp,
    g(tau,y)=e^{-tau/2} F(T-e^{-tau},x0+e^{-tau/2}y).

This is nonautonomous; even for a fixed spatial ambient field the argument of F changes. The force is not F(e^{+tau/2}y). With rho=exp(-|y|^2/4), Phi=H+Y^perp/2, A(tau)=integral_Sigma rho, d^2=integral|Phi|^2 rho and f^2=integral|g^perp|^2 rho, the first variation of weighted area gives the EXACT identity

    A'=-d^2-integral<Phi,g^perp>rho.

Indeed (d/dtau)dmu=-<H,V>dmu and D rho=-Y rho/2, and tangential motion contributes only a divergence. Each surface is compact, so this divergence has no boundary. For a noncompact replacement this equality requires cutoff convergence, not just a local smooth limit.

Suppose integral_{tau0}^infty f^2 is finite and a subsequence has A(tau_i)->A_S. Then A has a limit: A'+(d^2)/2 <= f^2/2, A>=0, and integration gives integral d^2<infty. Equivalently A+one-half integral_tau^infty f^2 is decreasing and bounded below; its limit is A_S. Define

    H(tau)=integral_tau^infty f(s)^2 ds,
    E(tau)=A(tau)-A_S+H(tau).

Then E->0, E>=0, and

    -E'=d^2+<Phi,g>_rho+f^2 >= (d^2+f^2)/2.       (1)

The tail correction has coefficient ONE. Using one-half would control d but would not give the simultaneous lower bound in (1). This matters because physical chart motion has speed bounded by d+f, not by d alone. Also A-A_S need not be nonnegative.

For unit-time drops a_j^2=E(tau0+j)-E(tau0+j+1), Cauchy–Schwarz and (1) give

    integral_{tau0+j}^{tau0+j+1}(d+f) <= 2 a_j.   (2)

The source's compact observation estimates consequently become |b'|+|x'| <= C(d+f), provided its chart/domain hypotheses really hold. Summability gives convergence of these physical observations. It is not legitimate to infer a convergent rotation merely from graphical convergence after arbitrary changing rotations.

## 2. Gaussian tails and the actual localization defect

Assume a uniform area-ratio bound mu_tau(B_r(z))<=Lambda r^2 for all z,r. For b>0, integration in annuli (or layer cake) yields

    integral_{|y|>R} exp(-b|y|^2/4)dmu
       <= Lambda (R^2+4/b) exp(-b R^2/4).

For example integrate w=-w' over the region outside B_R, use mu(B_s\B_R)<=Lambda s^2, and integrate (b/2) s^3 exp(-b s^2/4). Polynomial losses absorb into an arbitrarily small decrease of b, with constants depending on the decrease. Thus local smooth multiplicity-one convergence plus this bound gives convergence of A by fixing R first, passing to the limit there, then taking R to infinity. Entropy gives the area bound directly: evaluate the Gaussian defining entropy at (z,r^2), where its weight on B_r(z) is at least e^{-1/4}; hence mu(B_r(z))<=4*pi*e^{1/4} lambda r^2 for surfaces. These are classical operations, not new contributions.

For a space-time cutoff chi, the exact identity is

    (integral chi^2 rho)' = -integral chi^2<Phi,Phi+g>rho
       + integral (2chi partial_tau chi + 2chi Dchi . V)rho,
    V=Phi+g^perp,

when partial_tau is at fixed ambient y and the chosen parametrization is normal. In a parametrization with additional tangential speed one replaces partial_tau+Dchi.V by the material derivative and integrates its associated divergence consistently. Young bounds the Dchi.Phi term by a small fraction of integral chi^2|Phi|^2 plus C integral|Dchi|^2 rho. The terms with partial_tau chi and g must also be retained. If chi is supported between R and 2R and has |Dchi|<=C/R, |partial_tau chi|<=C |R'|/R, these errors are bounded using the preceding tail estimate and a bound on g on the annulus. Weighted f alone gives no pointwise annular force bound. A moving cutoff is therefore an extra error, not an autonomous-gradient identity.

## 3. A completed scalar reduction with delayed radii and forcing tails

Here is a fully specified exploratory lemma. Let 0<eta<c<theta<1/2, q>1, a_j in [0,delta], and E_j decrease to zero with a_j^2=E_j-E_{j+1}. Set

    p=(theta-c)/(1-c), nu=(1-c)/(1-theta),
    kappa=(1-eta)/(1-c)>1, h=kappa/8.

For R0>0 and a nonnegative sequence B_j define

    T_j=max{exp(-(1-eta)q^j R0^2/8),
             max_{0<=i<=j} a_i^{(1-eta)q^{j-i}}}.

Zero powers of a zero a_i are zero. Suppose the actual estimate supplied by a geometric argument is

    E_{j+1}^{1-theta} <= C (a_j+T_j+B_j).          (3)

If sum B_j^{1/(1-c)}<infty, then, for delta sufficiently small depending only on q,kappa,

    sum a_j <= 2 C_g E_0^p
            + 2 exp(-h R0^2)/(1-exp(-h(q-1)R0^2))
            + 2 sum B_j^{1/(1-c)},               (4)

where C_g depends only on C,c,theta.

Proof. Call j good when max(T_j,B_j)<=a_j^{1-c}. At a good j with a_j>0 and a_j<=1, (3) gives E_{j+1}<=C_1 a_j^nu. Since 1<nu<2, E_j<=C_2 a_j^nu. Concavity, with p in (0,1/2) and nu(1-p)=1, gives

    E_j^p-E_{j+1}^p >= p E_j^{p-1}a_j^2
                        >= p C_2^{p-1} a_j.

For a_j=0 there is nothing to prove. Thus the good contributions telescope to C_g E_0^p, without incorrectly evaluating the concavity derivative at E_{j+1}.

At a bad j, the current-index term a_j^{1-eta} cannot realize a value larger than a_j^{1-c}, since eta<c and a_j<1. Taking the (1-c)-th root of the remaining maximum yields

    a_j <= exp(-h q^j R0^2)
           + sum_{i<j} a_i^{kappa q^{j-i}} + B_j^{1/(1-c)}.

The sum over j of the first term is at most the displayed geometric bound, since q^j>=1+j(q-1). For finite N, the memory terms are at most

    rho(delta) sum_{i=0}^N a_i,
    rho(delta)=sum_{k>=1} delta^{kappa q^k-1}
       <= delta^{kappa q-1}/(1-delta^{kappa q(q-1)}).

Choose delta with rho(delta)<=1/2, combine good and bad indices up to N, absorb, and let N increase. This proves (4). It adapts the already paid source memory argument; it is not an independently substantial nominee.

To connect (3) to (1), select a time in [j+1/5,j+2/5] with d<=sqrt(10)a_j. Suppose the Source355 STATIC localized inequality is applicable there on an actual complete inner graph of radius R_j:

    |A-A_S|^{1-theta} <= C(d+exp(-(1-eta)R_j^2/8)).

Monotonicity of E, E=A-A_S+H, and H(selected time)<=H(j) give (3), with B_j containing H(j)^{1-theta}. If the geometric graph radius is additionally capped by L_j, then B_j also contains exp(-(1-eta)L_j^2/8). This is an implication conditional on graphical domains and their propagation, not a proof of them.

## 4. Nonempty scalar regimes, including all polynomial integrable powers

Suppose f(tau)<=epsilon (1+tau)^{-alpha}, alpha>1, with tau0>=0. Then

    H(tau)<=epsilon^2/(2alpha-1) (1+tau)^{1-2alpha}.

The tail term in (4) is summable exactly under the sufficient inequality

    (2alpha-1)(1-theta)/(1-c)>1.                 (5)

For EVERY alpha>1 and fixed theta in (0,1/2), choose c<theta close enough that

    theta-c < 2(alpha-1)(1-theta),

then choose eta in (0,c). These hypotheses are compatible; no extra free exponent is silently forced to equal another. For example theta=1/4, alpha=11/10, c=1/5, eta=1/10 gives the exponent 9/8>1 and kappa=9/8. This is a scalar example of the hypothesis regime, not an example of an arbitrary singular geometric flow.

Choose L_j^2=8 log(2+tau0+j). Then its contribution to (4) is (2+tau0+j)^{-kappa}, summable because kappa>1. For every fixed derivative loss m and alpha>1,

    (1+L_j)^m (1+tau0+j)^{-alpha}
       = o((1+tau0+j)^{-1})
       = o(exp(-L_j^2/8)).                     (6)

Thus polynomial spatial losses on these logarithmically growing balls do not contradict the forcing cutoff. This explicitly executes the stronger growing-radius alternative to stopping at failure of a fixed-radius estimate. It does NOT yet prove that no extra sheets enter, that the normal reach stays uniform, or that the graph propagates on those balls.

For genuinely bounded physical F, |g|<=C exp(-tau/2); a bounded Gaussian area implies f<=C exp(-tau/2), H<=C exp(-tau). Every scalar series above then converges with considerable room. This is the regime already treated for compact and cylindrical models by Hirsch–Zhu; relabelling it as new would ignore the strongest comparison.

## 5. What L1 forcing does not automatically give this reduction

The sufficient condition is a power-summability condition on the L2 tail H, not merely integral f<infty. For a concrete smooth decreasing model for large tau,

    f(tau)=1/(tau (log tau)^2),

integral f<infty whereas H(tau) is asymptotic to 1/(tau(log tau)^4). For every fixed c<theta the exponent beta=(1-theta)/(1-c)<1, so integral H(tau)^beta diverges. Indeed tau^{-beta}(log tau)^{-4beta} is not integrable. This disproves ONLY the implication from L1 forcing to our sufficient tail hypothesis; it does not disprove convergence of such flows. A more refined varying-threshold argument might close this logarithmic endpoint, and no obstruction theorem is asserted.

The first attempted bound keeping c fixed far below theta would exclude alpha close to one. Optimizing c as in (5) repairs that failure. Thus the remaining issue cannot honestly be stated as a missing elementary polynomial summability estimate.

## 6. Correct center/time and physical-scale bookkeeping

Suppose the source conclusion gives N_lambda(s)=lambda(M_{T+lambda^{-2}s}-x0)->sqrt(-s)S for s<0. For x_lambda=x0+lambda^{-1}a_lambda and T_lambda=T+lambda^{-2}b_lambda, the SAME spatial scale gives

    lambda(M_{T_lambda+lambda^{-2}s}-x_lambda)
      = N_lambda(s+b_lambda)-a_lambda
      -> sqrt(-(s+b))S-a,

provided a_lambda->a, b_lambda->b and the chosen compact s-interval satisfies s+b<0 with a fixed margin. This uses uniform smooth convergence on a larger compact negative-time interval. If a_lambda or b_lambda is unbounded, or s+b reaches zero, this conclusion does not apply. A separate spatial scale mu_lambda=c_lambda lambda with c_lambda->c>0 and time parameter s in its own scale yields c sqrt(-(b+s/c^2))S-c a, wherever b+s/c^2<0. Type-II scales and arbitrary spacetime sequences are not thereby identified.

If a normalized compact-graph estimate is C^k <=C (tau-tau0)^{-sigma}, then tau=2 log lambda-log(-s). On s in [-B,-A], A>0, it becomes a logarithmic scale rate with the full shift 2 log lambda-log(-s)-tau0; spatial multiplication by sqrt(-s) and its k-th derivative scaling contribute (-s)^{(1-k)/2} to physical graph derivatives after identifying the dilated domains. These factors are uniformly bounded only because A>0 and B<infty. An existential tau0 or model-dependent sigma is not a computable or uniform rate.

## 7. Exact compact embedded realizations of the forcing/gauge regimes

The following construction uses an actual compact embedded nonspherical shrinker, not a formal Jacobi mode. Angenent's author-hosted *Shrinking Doughnuts* was read through its complete rotational shooting existence argument (the specific extents and limits are in the private reading record). Its n=2 embedded torus, normalized by its shrinking-solution time scale, supplies a compact connected embedded S satisfying H_S+Y^perp/2=0. The author's time-dilation convention is normalized here from the shrinking solution itself; no coefficient is inferred from a possibly ambiguous OCR line. The proof rotates a simple closed positive-radius profile obtained by a shooting threshold, with positive lower radius and bounded excursion, then orthogonal reflection closes it. Thus it really supplies an embedded torus, not an immersed planar mode.

Choose coordinates so S is invariant under rotations around e3. Let A be the skew-symmetric generator of rotations around e1, and Q(tau)=exp(beta(tau)A), beta'=w(tau), beta(0)=0. For 0<=t<1 define

    M_t=sqrt(1-t) Q(-log(1-t)) S,
    F(t,x)=w(-log(1-t))/(1-t) A x.              (7)

Direct differentiation of the parametrization gives

    X_t = -(2(1-t))^{-1} X + w(tau)/(1-t) AX.

The normal projection of the first term is exactly H_{M_t}; hence (7) is an EXACT forced MCF. It is compact, connected and smoothly embedded at every t<1. Its curvature scales as (1-t)^{-1/2}; since S is not a plane, the curvature supremum tends to infinity. There is no earlier loss of smoothness, so 1 is the first singular time. The entire surface collapses to the fixed point 0.

For this family Sigma_tau=Q(tau)S is an exact shrinker at each tau. Consequently

    Phi=0, d=0, A(tau)=A_S,
    g(tau,y)=w(tau)Ay,
    f(tau)=c_S |w(tau)|,
    c_S^2=integral_S |(Ay)^perp|^2 rho >0.        (8)

To prove positivity, if Ay were everywhere tangent to S, its complete ambient rotation flow would preserve S. Invariance under both e1 and e3 rotations implies invariance under the group they generate, SO(3). A connected compact embedded two-dimensional SO(3)-invariant surface is a centered round sphere: each nonzero orbit is a full sphere, and the local dimension permits only isolated radii; connectedness permits one. This contradicts the torus topology. Rotations Q commute with A, so the integral defining c_S is independent of tau. This verifies nontrivial physical axis motion and all joint geometric hypotheses for these examples.

(a) Vanishing, square-integrable rescaled forcing without uniqueness. Take w(tau)=(1+tau)^{-1}, beta=log(1+tau). Then g tends to zero in every C^k norm on every fixed ambient compact set, and f is in L2 but not L1. For each lambda,

    lambda M_{1+lambda^{-2}s}
      =sqrt(-s) exp(beta(2log lambda-log(-s))A) S.

On a compact interval [-B,-a], 0<a<B, beta(tau-log(-s))-beta(tau)->0 uniformly with all time derivatives of fixed order. Choose tau_n=exp(2*pi*n+b)-1, lambda_n=exp(tau_n/2). Then the rescalings converge smoothly with multiplicity one to sqrt(-s)exp(bA)S. At least two such limits are different by c_S>0. These are different FIXED-CENTER backward tangent flows in the original ambient frame. This example proves that a perturbation merely vanishing at each scale, even with finite squared Gaussian forcing energy and d identically zero, is insufficient for a forced extension. It does not contradict Source355, which is unforced. Physical F is smooth for t<1 but unbounded as t approaches 1; bounded physical forcing is explicitly outside this example.

(b) Actual compatible flows for every polynomial integrable envelope. Take w(tau)=epsilon(1+tau)^{-alpha}, alpha>1. Then

    beta_infty-beta(tau)=epsilon/(alpha-1)(1+tau)^{1-alpha}.

The normalized surfaces converge to exp(beta_infty A)S in the original frame. The normal-graph C^k error is bounded by C_{S,k} times this angle difference for all sufficiently late tau. It also has a lower C^0 normal displacement bound by c times the angle difference: choose a point where (Ay)^perp is nonzero, use the tubular projection and differentiate the rotation action there. This establishes a real trajectory rate, with nonzero leading physical displacement. No universal sharpness theorem for all source models is asserted. Uniform Gaussian area and local C^m bounds for g follow immediately from compactness of S and linearity of Ay. This shows the scalar alpha>1 regimes are not empty under the compact embedded first-singularity constraints.

(c) A stronger alternative at the logarithmic endpoint. Take w(tau)=1/((tau+e)(log(tau+e))^2). The same exact compact family converges, with remaining physical rotation angle 1/log(tau+e), even though the sufficient tail criterion in Section 5 fails for every fixed c<theta. Thus that failed scalar estimate cannot honestly be promoted into a geometric obstruction or a sharp Dini threshold. It is a limitation of the particular absorption argument. No second source family is developed; this is a compatibility test within the Source355 perturbation direction.

These constructions are elementary once the classical torus is supplied. They are useful diagnostics and nonemptiness witnesses, but the task explicitly excludes a coordinate rotation alone as a substantial finding.

## 8. Completing the compatible compact-model alternative

It is possible to go beyond a formal scalar inequality in the compact-model case. This paragraph records the actual trapping argument and its restricted hypotheses; it does not freeze a new full-scope finding.

Assume S is a fixed compact embedded shrinker, Sigma_tau is a smooth connected compact rescaled forced flow for all finite tau>=tau0, the force in a fixed tubular neighborhood has uniform parabolic smooth bounds decaying like epsilon(1+tau)^(-alpha), alpha>1, the Gaussian area bound is uniform, the GLOBAL weighted force obeys f(tau)<=C epsilon(1+tau)^(-alpha) (not merely a bound valid until a possible graph exit), and a subsequence converges locally smoothly with multiplicity one to S. At sufficiently late subsequence times the whole Sigma_tau is a small normal graph over S: the local single sheet over the compact boundaryless S is itself a closed component; connectedness excludes an additional component or a tube attached outside that sheet. This argument uses compactness of S and fails for a noncompact shrinker.

Fix the classical compact Lojasiewicz neighborhood from Schulze Section 3. In that neighborhood the normal graph equation is uniformly parabolic. On any maximal interval remaining in a fixed small C^{2,beta} neighborhood, positive-delay local parabolic estimates give uniform higher spatial derivatives, with the number of derivatives of the ambient force increased accordingly (HZ Appendix C uses m+l+2 spatial derivatives for m+l curvature derivatives). The finitely many compact coordinate charts and a slightly larger tube fix the constants. Initial high norms at the starting subsequence time are controlled by its smooth convergence. Thus the graph speed obeys

    ||u_tau||_{L2(S)} <= C_S(d+f).

The static compact inequality is |A-A_S|^{1-theta}<=C d. While d<=delta<1, it and the corrected energy give

    E^{1-theta}<=C_1(d+H^{1-theta}).

On the set where H^{1-theta}<=d^{1-c}, E<=C_2 d^nu, and (1), nu(1-p)=1 imply

    -(E^p)' = p E^{p-1}(-E') >= C_3 d.

On the complementary set d<H^{(1-theta)/(1-c)}. Consequently, for any end time of the maximal graphical interval,

    integral d <= C E(tau0)^p
        + integral_{tau0}^infty H^{(1-theta)/(1-c)},
    integral(d+f) <= C E(tau0)^p
        + integral_{tau0}^infty H^{(1-theta)/(1-c)}
        + integral_{tau0}^infty f.                       (9)

If E becomes zero, (1) forces d=f=0 afterwards; thus no division-by-zero ambiguity is needed in this argument (otherwise work on E>0 and pass to the endpoint). The high graph norms give d<=delta after choosing the initial neighborhood sufficiently small; a bounded-d variant changes constants. For alpha>1 choose c as in (5). All three right-hand terms in (9) tend to zero along sufficiently late initial subsequence times. L2 displacement plus uniform higher-derivative bounds implies C^{2,beta} displacement tends to zero on the compact S, by interpolation. Choosing it less than half the neighborhood margin contradicts a finite first exit. Uniform parabolic continuation in the fixed tube excludes loss of the graph before that exit.

Hence the graphical interval is infinite. The finite L2 variation gives a limit; interpolation gives convergence in each fixed spatial C^k norm when the corresponding force derivatives are controlled. The original subsequence identifies the limit as S, in its original coordinates. The normalized equation also gives smooth space-time convergence on bounded tau windows under the stated parabolic derivative control. This closes the compact-model construction without assuming spectral nondegeneracy, integrability of a Jacobi field, or a varying gauge that removes a physical axis. It is the classical trapping method with the explicitly modified energy and optimized threshold, not evidence of a nonroutine full-scope advance.

## 9. Executing the growing-domain alternative and isolating the remaining work

For a general source model S with its finite separated cylindrical/conical ends, the static finite-jet and localized-gradient machinery is already paid. Neither an autonomous graph equation nor a new finite-dimensional reduction is needed. The candidate geometric implementation would use

    R_j^2=min(q^j R_in^2, min_{i<=j} q^{j-i}8log(1/a_i),
              8log(2+tau0+j)).

The last cap grows more slowly than q^j; for sufficiently late tau0 its successive-radius ratio is below the same Q=sqrt(q) used by the source. Therefore it is compatible with the source's forward expansion factor, rather than forcing a fixed domain forever. Assume, for the purpose of this calculation, rescaled ambient derivatives through the needed finite order obey

    |D_y^k g| + [appropriate time Holder bound]
       <= epsilon (1+tau)^(-alpha) (1+|y|)^m,

on the doubled balls, with fixed m and alpha>1. The global weighted-force envelope from Sections 1 and 4 is a separate hypothesis: a bound only on these balls does not control the force in the Gaussian tail. Equation (6) makes the force and any fixed polynomial spatial losses smaller than the source's cutoff threshold there. If chi is the doubled-ball cutoff, the annular terms from Section 2 have the bounds

    C Lambda (1+L)^M e^{-L^2/4}
       * (1+|L'|/L + epsilon(1+tau)^(-alpha)(1+L)^m),

with fixed M determined by the derivative/order used. With L^2=8log(2+tau), these are integrable (a polynomial in log tau times tau^{-2}, or smaller). They can be included in the corrected tail H by adding their absolute integrals. Such tails behave at worst like tau^{-1}(log tau)^M: raising them to beta=(1-theta)/(1-c)<1 is NOT automatically integrable. Thus using this crude cutoff energy as the main corrected energy would reintroduce a failure. The strongest compatible repair is to retain the GLOBAL Gaussian energy of the actual compact surfaces (Section 1), which has NO cutoff boundary flux, and use cutoffs only in the static localized estimate. There their Gaussian defect enters directly as the summable cap term (kappa>1), not as a squared-energy tail. This distinction is essential.

At a selected time, the global drop controls d and f as in (2). The source's static localization would then give exactly (3). Its memory lemma plus our external term gives finite total motion and compact observation drift. Its all-time completion could be reused only after verifying that every selected graph really covers all sheets in the claimed inner ball, that the normal tube/derivative estimates persist at positive delay, and that the regraphing cost includes the forcing speed as well as Phi. The force derivative bounds above make a compactness-based one-step comparison plausible: after undoing rescaling on a fixed time horizon, the force tends to zero on each relevant local patch. White's forced local regularity proof and HZ Appendix C do provide the relevant local regularity estimates ONCE density/curvature hypotheses are supplied. They do not, by themselves, furnish the global entire-inner-graph/no-extra-sheet assertion on an increasing collection of end patches.

Two precise obligations remain for a full-scope forced first-singularity statement, and neither is claimed to be a new hard theorem merely because it is unfinished here:

1. From compact embedded initial data and the proposed singular-in-time forcing class, produce a multiplicity-one smooth shrinker tangent with the full finite separated end/tube geometry used by Source355, at every chosen first-singularity point. BK Theorem 1.7's proof uses its unforced logarithmic local-scale estimate (Theorem 1.5), uniform genus and weak-set-flow structure; it is not an estimate for arbitrary forced flows as stated. Source355 truth pays that operation in its own unforced setting, not its unproved forced analogue. Assuming this geometry would explicitly restrict the extension.
2. Even assuming one such model and uniform area ratios, establish a forced version of Source355's whole-sheet positive-delay propagation/regraphing proposition with constants uniform on the capped growing domains and with the error in physical observations bounded by integral(d+f). The local inputs and compatible scales have been worked out above, but their complete nonlinear patching/no-extra-sheet proof is not written here. An argument that merely passes to a local unforced limit and asserts the global covering property would skip exactly this obligation.

No convergence at time zero, uniform global end convergence, parametrization convergence, model persistence for a varying initial-data family, or effective model-independent exponent follows from these notes. A fixed-source statement with all rates/constants and the geometric propagation simply postulated would be a conditional bridge, not a substantial full-scope result. Accordingly no discovery-level theorem is frozen.
