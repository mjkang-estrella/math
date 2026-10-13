# I231 — viscous anisotropic Liouville: early mathematical record

Status: investigation, no theorem claimed at this stage. All pinned lower operations are stipulated; applicability to the changed equation is being checked.

For m>=1 and tau>0, write

    G_tau[V] = V_tt + 2 DxV·DxV_t + DxxV[DxV,DxV] + tau Delta_x V.

The exact fit contract is: one C0<infinity, every z=(x,t), every R>0, some p in R^m and a in R, with

    |V(x+h,t+l)-V(x,t)-p·h-(a-|p|²/2)l| <= C0 R
    for |l|<=R and |h-pl|<=R.

No global gradient bound is assumed. Equation-free comparisons in source 04 yield logarithmic fit-parameter control after centering and growth O(R(1+log R)^2), not a global Lipschitz estimate.

## Route A: extremal envelopes — first changed input

In source 04's forward quadratic-envelope upper test, the test has horizontal Hessian I/l. Thus G_tau[test]>=0 gives

    psi''(l) + (|d|²+tau m)/l >= 0,

not the homogeneous inequality psi''+|d|²/l>=0. At a fixed center the corrected convex quantity is P_l V + tau m l log l. This correction has derivative tending to minus infinity at l=0. The source's monotone finite Hamiltonian-slope and contact arguments cannot yet be invoked. This is a precise failed input, not a disproof of rigidity.

The source shear/scale change preserves G_tau=0 with the SAME tau: Dyy(bar V)=R Dxx V and F[bar V]=R F[V]. Hence changing scale cannot make this trace disappear.

## Route B: growth and divergence structure

For smooth V set H=V_t+|DxV|²/2 and rho=exp(H/tau). Direct differentiation gives

    tau rho^{-1}(partial_t rho + div_x(rho DxV)) = G_tau[V].

The associated strictly convex integrand is tau exp((q+|p|²/2)/tau). This may support a genuinely different growth/Liouville argument, but ellipticity constants depend on the unknown gradient/Hamiltonian and cannot be declared uniform.

## Active obstruction checks

The coefficient matrix is A_tau(p)=[[p p^T+tau I,p],[p^T,1]], with quadratic form (p·xi+s)^2+tau|xi|². It is positive definite for each p, but has no p-independent ellipticity ratio.

If V=f(t), finite-tau equation is f''=0. The divided tau->infinity equation is only Delta_x V=0. V=sin t satisfies that equation and the exact fit with p=a=0 and C0=1, since |sin(t+l)-sin t|<=|l|<=R. Thus the naive infinite-tau Liouville statement is false, even for smooth bounded global-Lipschitz functions. This example alone does not show it is a locally uniform limit of finite-tau exact solutions under common fits.

## Mid-investigation update: a surviving envelope and a warning from primary literature

The barycentric envelope, unlike the forward quadratic envelope, DOES preserve G_tau-subsolutions. In the source common-time theorem of sums, in addition to the vector zeta=((q_i,1))_i use, for each horizontal coordinate k, the vector E_k=((e_k,0))_i. Summing the individual jet inequalities and testing the block matrix bound on zeta and all E_k gives

    D²Phi[((q_i)_i,1)] + tau sum_k D²Phi[((e_k)_i,0)] >= 0.

The synchronization penalty vanishes on all these vectors. For Phi=phi(sum theta_i y_i,t)+ct+sum theta_i|y_i-sum theta_j y_j|²/(2t), the first variance second variation is zero along q_i=p+(y_i-x)/t; all common spatial translations leave the variance exactly unchanged. Thus the right side is G_tau[phi]. This supplies a genuinely checked changed-PDE input to the extremal-contact construction.

A tempting shortcut is strong comparison for continuous G_tau-sub/supersolutions. It is NOT being used as an established input. Ohnuma's 2006 note states a theorem for locally strictly elliptic gradient-dependent operators that appears to cover G_tau. However Ohnuma–Sakaguchi, arXiv:1806.03587v1, introduction, explicitly report that the underlying Giga–Ohnuma proof does not work for nonuniformly elliptic F(Du,D²u). Their replacement theorem is for prescribed mean curvature with its own classical Dirichlet replacement and gradient estimates. It has not been checked for G_tau. This prevents declaring the finite-tau bridge proved merely by quoting that older theorem.

There is direct pre-existing literature on the displayed viscous equation: Sanchez Morgado, arXiv:1712.10275v1, equation (4), specializes to G_(1/k) with H(p)=|p|²/2. Porretta, arXiv:2203.04856v1, equation (1.7), becomes G_epsilon after replacing his potential u by -V. Their periodic/smooth or positive-marginal boundary problems do not immediately imply a local estimate for every continuous entire fitted viscosity solution. Thus neither the PDE nor its exponential variational formulation is claimed new.

# Final analysis and verdict

**Finite positive tau: NOT PROVED and NOT DISPROVED here.** The paid reduction below leaves a precise contact-propagation statement (SC_tau), or alternatively the local estimate (REG_tau). No unconditional viscous Liouville theorem is submitted and no tenth finding is nominated. **Formal infinite tau: the corresponding Liouville assertion is false.**

## 1. Exact target, signs, parameters and invariances

Let m>=1, 0<tau<infinity, 0<=C0<infinity. The target L(m,tau,C0) says that every continuous V on R^m x R which has the exact fits written above and solves G_tau[V]=0 is affine. At every upper C² test phi the sign is G_tau[phi]>=0; at every lower test it is <=0. The operator is continuous on all jets; there is no omitted zero-gradient convention. C0=0 is immediately rigid without a PDE, since every fitted open box agrees with one affine function, and overlapping boxes identify all coefficients.

For C0>0 one may enlarge it to max(C0,1) in the source fit estimates. This loses no hypothesis needed for a qualitative Liouville conclusion. For |p|<=M an explicit ellipticity bound is

    lambda(tau,M) = 1 / max((1+2M²)/tau, 2),
    Lambda(tau,M) = M²+1+tau,
    lambda(|xi|²+s²) <= (p·xi+s)²+tau|xi|² <= Lambda(|xi|²+s²).

The lower bound follows from s²<=2(s+p·xi)²+2M²|xi|². No uniform-in-M lower bound follows. Taking xi parallel to p and s=-p·xi exhibits the loss. The time derivative itself does not enter A_tau, but this does not bound the horizontal test gradients.

The source change of frame is exactly valid with tau retained:

    U(y,s)=[V(x0+R(y+p0 s),t0+Rs)-V(x0,t0)]/R
            -p0·y-(a0+|p0|²/2)s.

Here G_tau[U]=R G_tau[V] at corresponding smooth jets, and the pullback of tests proves the viscosity statement. DxU=DxV-p0, DyyU=R DxxV. Fits become (p-p0,a-a0), with C0 unchanged. In particular tau does NOT become small when R tends to zero or infinity.

A fixed drift b is treated by the natural version

    G_(tau,b)[V]=D²V[(DxV+b,1)]+tau Delta_x V,
    |h-(p+b)l|<=R,
    affine time coefficient a-|p|²/2-b·p.

Then U(y,t)=V(y+bt,t) solves the standard equation and has the standard fits with identical C0 and a. Thus a theorem for b=0 would give the natural drift theorem with identical fit constant. Ordinary Euclidean local estimates may depend on |b| through this shear. This does not assert invariance of a drift theorem with an incorrectly unchanged fit shear.

One can also set tau=1: W(y,t)=V(sqrt(tau)y,t)/tau satisfies G_1[W]=0. Using the old radius max(1,sqrt(tau))R gives standard fits for W with constant C0 max(1,sqrt(tau))/tau. This rescales the fit constant as well and supplies no uniform original-variable conclusion at tau=infinity.

### 1.1 Actual compact-jet limit from the supplied p-equation scaling

Write kappa_j=epsilon_j/lambda_j and

    S_lambda(Dphi)=lambda|Dxphi|²+(1+lambda phi_t)².

The supplied stretched equation is

    D²phi[(Dxphi,1+lambda phi_t)]
      +kappa S_lambda(Dphi)(Delta_x phi+lambda phi_tt)=0.

For lambda_j->0 and kappa_j->tau in (0,infinity), its operator converges on every compact set of jets to G_tau. Thus any already obtained locally uniform limit solves the precise new equation by strict-contact stability. For kappa_j->infinity, division by kappa_j instead converges on compact jet sets to Delta_x. This justifies the two PDEs being investigated, conditional on the needed local uniform convergence. Neither passage proves the upstream p-family fit/compactness inputs or the other asymptotic regimes.

## 2. What the fits alone pay, and what they do not

Source 04 lem:fit-compactness, through its displayed geometric proof, uses only fits for its estimates. Its PDE invocation is solely strict-test stability for the limit. Replacing that invocation by continuity of G_tau is valid when tau is fixed, or varies to a finite positive value. Thus centered viscous classes have

    |V(x,t)| <= C K(1+log K)² on |x|,|t|<=K,
    |p|+|a| <= C(1+log K+|log r|)

for every radius-r fit centered in that box, and the source spatial/time logarithmic moduli and uniform subquadratic spatial tails. Here C depends on m,C0; an initial prescribed fit changes only the centering data. All-center/all-radius passage is done separately at every fixed center/radius, choosing a converging coefficient subsequence; local uniform convergence of the function is already fixed. No countable replacement of the actual fit quantifiers is used.

These estimates do not imply differentiability or a globally bounded gradient. For an explicit fit-only example set V(x,t)=g(t), g(t)=t log|t| for t!=0 and g(0)=0. If |t0|<=2R, take p=0, q=log R, a=q. With s=t0/R and u=l/R, the error is R[g(s+u)-g(s)]; |s|<=2, |u|<=1 bounds it by 6 log(3) R <7R. If |t0|>2R take q=g'(t0); |g''|<=1/(|t0|-R) on the interval gives error <=R/2. Hence the exact fits hold with C0=7, but g' is unbounded at zero and at infinity. This example is not a G_tau solution: g''=1/t off zero.

### 2.1 An exact-fit example with unbounded horizontal gradient

The issue is not confined to time derivatives. Set

    f(s)=s sqrt(log(e+s²)),     V(x,t)=f(x1),

with natural logarithm and e the exponential constant. This smooth function has unbounded horizontal derivative and satisfies the exact sheared fits with C0=10. Here is an explicit all-center/all-radius verification.

Fix the first center coordinate x0 and R>0. Choose T>|x0| solving

    T=|x0|+(1+p)R,     p=sqrt(log(e+T²))>=1.

A solution exists by continuity because T-sqrt(log(e+T²))R tends to infinity with T. Use vector slope (p,0,...,0), ordinary time coefficient q=0, and a=p²/2. Every point in the sheared box has |h1|<=(1+p)R=:L. Write q_s=sqrt(log(e+s²)). For |s|<=T,

    |f(s)-p s| <= (2|s|/p)log(T/|s|) <= 2T/(e p),

with the continuous value zero at s=0. The first inequality uses log((e+T²)/(e+s²))<=2log(T/|s|) and p+q_s>=p.

If |x0|<=2L, then T<=3L. Subtracting the two approximation errors at x0+h1 and x0 gives a remainder <=4T/(e p)<=24R/e<9R.

If |x0|>2L, every intervening s has |x0|/2<|s|<=T<3|x0|/2. Therefore p²-q_s²<=2log3, and

    |f'(s)-p|
      <= [2log3+sqrt(1+2log3)]/p <4/p.

Here f'(s)=q_s+s²/((e+s²)q_s) and p/q_s<=sqrt(1+2log3). Integration over |h1|<=L gives remainder <=8R. The other horizontal coordinates and time cause no change. This proves one C0=10 for every center and radius, while f' grows without bound. It is not a viscous solution: the stationary one-variable equation would be (f'²+tau)f''=0 and would force f affine.

## 3. Route A, paid part: viscous barycentric contact

Define, for s>0,

    C_s f(x,t)=sup_{sum theta_i y_i=x}
        {sum theta_i f(y_i,t) - sum theta_i|y_i-x|²/(2s)},

where the supremum is over finite positive-weight probability configurations. The finite attainment, duality, spatial semiconcavity and convergence portions of source 05 lem:barycentric-envelope are entirely geometric and apply under the paid subquadratic tails.

### 3.1 Full changed-operator verification

Suppose f is a continuous G_tau-subsolution. In source 05 lem:common-time-subsolution synchronize the independent times with its penalty chi, and apply the stipulated theorem of sums to theta_i f(y_i,t_i). For the resulting matrices X_i and horizontal gradients q_i=theta_i^{-1}D_yi Phi, division by theta_i gives

    X_i[(q_i,1)]+tau sum_(k=1)^m X_i[(e_k,0)] >=0.

There is no extra theta_i on the right: the jet Hessian is divided by theta_i at the same time as the horizontal gradient. Multiply its nonnegative inequality by theta_i to obtain the display above. Test the block matrix inequality on zeta=((q_i,1))_i and E_k=((e_k,0))_i and add the results, with coefficient tau on each E_k. For fixed synchronization parameter, let the theorem-of-sums parameter tend to zero; then let the synchronization parameter tend to infinity. D²chi vanishes on zeta and every E_k. Its time-gradient components need no bound, since G_tau does not depend on them. The result is

    D²Phi[((q_i)_i,1)] + tau sum_k D²Phi[((e_k)_i,0)] >=0.       (CT_tau)

For an upper test phi of W=C_t f-ct choose an attaining configuration at the contact and put

    Phi(Y,t)=phi(X(Y),t)+ct+sum theta_i|y_i-X(Y)|²/(2t),
    X(Y)=sum theta_i y_i.

Then q_i=Dxphi+(y_i-X)/t. Along (q_i,1), the mean velocity is Dxphi, while each centered offset scales by (1+h/t). The variance divided by 2(t+h) is affine in h, so its second variation is zero. Along each E_k all points translate together, the offsets are unchanged, and the mean moves by e_k. Thus (CT_tau) gives exactly

    D²phi[(Dxphi,1)]+tau Delta_x phi >=0.

Therefore C_t f-ct is a G_tau-subsolution for every constant c, with no assumed derivative of f. This verifies the changed PDE input rather than reusing the homogeneous corollary verbatim.

### 3.2 A replacement for the source's horizontal-affine preliminary case

The original proof uses quadratic-envelope convexity to show that a nonaffine member has a nonaffine horizontal slice; that convexity is unavailable here. There is a fit-only replacement.

Suppose V(x,t)=P(t)·x+c(t) on every slice. P,c are continuous by evaluations at 0 and the coordinate vectors. Fix t and R>=l>0. The horizontal part of any radius-R fit centered at (x,t) gives |p-P(t)|<=C0, independently of x. Evaluate this same fit at increments (pl,l) and (-pl,-l), and add. Their fitted affine increments cancel. It follows that

    |[P(t+l)+P(t-l)-2P(t)]·x
        + l p·[P(t+l)-P(t-l)]
        + c(t+l)+c(t-l)-2c(t)| <=2C0 R.

All terms except the first are uniformly bounded as x varies, since |p-P(t)|<=C0. Letting x tend to infinity in any fixed direction forces P(t+l)+P(t-l)=2P(t). Hence P(t)=b t+d. The centered fit growth bound, evaluated at x=+-K e and |t|<=K, gives |P(t)|<=C(1+log K)². Letting K grow forces b=0. For constant P, the test phi(x,t)=P·x+psi(t) reduces the viscosity equation to psi''=0 for c; thus c is affine. So any nonaffine viscous member has a nonaffine horizontal slice.

### 3.3 Exact extremal contact without a finite-Hamiltonian claim

The reflection V(x,t)->-V(x,-t) preserves G_tau=0 and the fits, and reverses the sign of a horizontal Jensen defect. For a nonaffine member choose this sign so some defect is positive. Set

    kappa=sup { [sum theta_i V(y_i,t)-V(sum theta_i y_i,t)]/r },
    r²=sum theta_i|y_i-sum theta_j y_j|², r>0.

The centered growth estimate, after normalizing a radius-r fit, bounds kappa above solely in terms of m,C0; positivity gives 0<kappa<infinity. Normalize configurations approaching kappa to mean zero and second moment one. Source 05's probability-measure compactness argument applies: tails of the value integrals vanish by uniform subquadratic growth, first moments are uniformly integrable, and second moments can only decrease. It gives a centered fixed-tau solution Vhat and a mean-zero measure mu with second moment <=1 and value defect kappa.

The measure competitor gives

    C_(1/kappa) Vhat(0,0)-Vhat(0,0) >=kappa/2.

The global Jensen bound gives the reverse inequality and forces equality and second moment one. Apply the invariant frame with radius 1/kappa and translate time to center at (0,1). The result is a continuous fixed-tau solution V with global Jensen constant kappa and

    W=C_t V-kappa²t/2,
    V-kappa²t/2 <= W <= V on t>0,
    W(0,1)=V(0,1)=0,
    C_1 V(0,1)-V(0,1)=kappa²/2>0.                   (CONTACT_tau)

Section 3.1 proves W is a G_tau-subsolution. Finite attainment and semiconcavity remain paid. Unlike source prop:envelope-contact, NO finite Hamiltonian/envelope slope at the contact is asserted.

### 3.4 The precise unpaid step and the conditional contradiction

The following restricted statement would suffice:

**(SC_tau)** For every m,C0 and finite tau>0, every extremal pair (V,W) satisfying (CONTACT_tau), the contact set of W<=V is the whole connected half-space R^m x (0,infinity).

A standard-looking stronger sufficient claim is strong comparison for arbitrary continuous G_tau-subsolutions and supersolutions on connected open sets. Neither version is proved here. Horizontal semiconcavity of W alone does not establish a full space-time Lipschitz bound on W or V.

If SC_tau were paid, fix t>0. The function y->V(y,t)-|y|²/(2t) attains its global maximum at some y*. Its supporting paraboloid gives, for every finite configuration of mean y*,

    sum theta_i V(y_i,t) - sum theta_i|y_i-y*|²/(2t) <= V(y*,t).

The singleton attains equality, so C_t V(y*,t)=V(y*,t). But W=V would require this gap to equal kappa²t/2>0 everywhere. This contradiction proves L(m,tau,C0) CONDITIONAL ON SC_tau. All the other steps in this route above have been paid.

The tempting 2006 strong-comparison statement has local gradient-ball ellipticity hypotheses matching A_tau, but the later primary correction explicitly rules out using that argument for the present gradient-dependent nonuniform setting. The newer theorem concerns a different operator and requires its own smooth Dirichlet replacement machinery. It is not a ready-made justification of SC_tau.

## 4. Why source 04/06/07/08 do not finish Route A

For P_l f along x(l)=x0+dl, the lifted upper test has Dxx²=I/l. Thus

    (P_l f(x(l),t))'' >=-(|d|²+tau m)/l

in the viscosity sense, and P_l f+(|d|²+tau m)l log l is convex. The sign-reflected statement holds for M_l. For d=0, the correction is still present. Its slope at zero is unbounded. The unchanged monotonicity and equality of finite limits in source lem:envelope-slopes are therefore not available from this argument.

There is also an explicit nonvanishing loss in the source's discrete propagation step. The midpoint quantities in source 06 now obey only

    D>=-2tau m epsilon log 2,
    Dtilde>=-2tau m epsilon log 2.

The moving-center midpoint estimate acquires the same first loss. Repeating its algebra gives, at best from these inputs,

    E[J_epsilon(z_next)|z]-J_epsilon(z)
      >= c(|Q_+-Q0|²+|Q_--Q0|²)-tau m log 2,
    c=1/[16(1+log 2)].

The geometric competitor gaps e,etilde stay nonnegative and the drift identity itself remains exact. But a constant loss per discrete step is not a bounded forcing error after summing the fair time walk: its expected number of steps across fixed time levels is of order epsilon^(-2). Source 07's uniform stopped expectations do not follow. Source 08 requires the finite-slope/constant-slope input and unchanged directed comparisons, so its rigidity lemma is not applied to G_tau.

This is a failure of these particular transferred inequalities, not proof that every alternative viscous stochastic envelope must fail.

## 5. Route B: an independent local regularity/growth reduction

The divergence identity in the early note is exact for C² solutions. For L(p,q)=tau exp((q+|p|²/2)/tau),

    D_(p,q)L = exp(H/tau)(p,1),
    D²_(p,q)L = exp(H/tau)/tau A_tau(p).

It is strictly convex at every finite jet. Nevertheless q+|p|²/2 is not coercive in all (p,q), and the fit moduli do not give exponential energy integrability. A continuous viscosity solution has not been shown to be a finite-energy local minimizer. Integration by parts, differentiation and a priori gradient estimates therefore remain unavailable without a separate bridge. The same operator in the primary weak-KAM/transport literature does not itself supply that bridge.

Here is an alternative exact sufficient estimate:

**(REG_tau)** For each m,C0,tau>0 there are alpha>0 and M<infinity such that every entire G_tau-solution centered by a zero radius-one fit belongs to C^(1,alpha)(B_(1/2)^(m+1)) with gradient norm and seminorm <=M.

It would be enough to prove this on a slightly larger fixed box for solutions with the local bounds furnished by the fits. The constants must be uniform over the centered class; they may depend on m,C0,tau. No uniformity as tau tends to infinity or zero is asserted.

To see that REG_tau implies the target, fix a radius-one fit at the origin of V, and for each R>=2 choose a radius-R fit (p_R,a_R). Geometric dyadic comparison gives |p_R|<=C(1+log R), with C also depending on the initial fit. Center and rescale using this radius-R fit. The resulting U_R lies in the normalized class. For a fixed physical point z=(x,t), its new coordinate is

    z_R=((x-p_R t)/R,t/R),

which tends to zero. For any two fixed points z,z', their new distance is at most C_(z,z')(1+log R)/R. The derivative identities are

    Dx U_R(z_R)=Dx V(z)-p_R,
    (U_R)_t(z_R)=V_t(z)+p_R·Dx V(z)-a_R-|p_R|²/2.

Differentiability of V itself follows from any one rescaled REG_tau assertion. Its Hölder bound therefore gives

    |DxV(z)-DxV(z')| <= C [ (1+log R)/R ]^alpha,
    |V_t(z)-V_t(z')| <= C(1+log R)[ (1+log R)/R ]^alpha.

Let R tend to infinity. All derivatives agree at any two points and V is affine. This pays the large-scale/logarithmic-growth part completely; REG_tau is the unpaid local analytic estimate. The ellipticity bounds in section 1 do not prove it unless a horizontal gradient bound is first obtained.

## 6. Infinite tau and explicit failed examples

Let tau_j->infinity, and suppose a sequence of exact G_(tau_j)-solutions converges locally uniformly with the same fit constant and centering. Dividing their equations by tau_j and testing at strict contacts gives only

    Delta_x V=0.

The term F/tau_j tends to zero on compact jet sets. No assertion about V_tt survives. V(x,t)=sin t is smooth, nonaffine, solves Delta_x V=0, and satisfies the original exact fits with p=a=0 and C0=1 at every center and every radius. All fixed affine drifts are covered as well. Hence this limiting PDE plus precisely the inherited fit contract is NOT an affine Liouville package.

Indeed every continuous solution of Delta_x V=0 with these fits has the form b·x+c(t), where b is constant, but c need not be affine. To check this stronger classification: the restriction to any fixed time is harmonic (localize a spatial viscosity test using a vanishing time penalty; the operator has no time derivatives). For each fixed t, the growth O(R log²R) and the harmonic interior derivative bound |DxxV(x,t)|<=C R^(-2) sup_(B_R(x))|V(.,t)| force DxxV=0 as R->infinity. Thus V=P(t)·x+c(t); the fit-only midpoint argument in section 3.2 then makes P affine in t, and the joint growth bound makes it constant. The time-only example shows the classification is sharp. It does not upgrade to c''=0 because the limiting PDE has no time derivative.

This is NOT a construction of nonaffine exact finite-tau solutions or of a sequence of such entire fitted solutions converging to sin t. If the finite-tau theorem were true, every such sequence would consist of affine functions and every locally uniform limit would be affine. Thus extra information from the approximating equations, if proved and retained uniformly, could still exclude the counterexample. The naive PDE-plus-fit limit alone cannot do so.

Other tested analytic ansatzes: for V=P·x+c(t), G_tau=c''; for V=f(e·x+at)+an affine function (with unit e), its scalar coefficient is [(f'+e·P+a)²+tau]f'', so every C² profile in this form is affine. For a quadratic V(z)=z^T Bz/2+d·z+c, horizontal large-radius fits force B_xx=0; the fit-only slice argument forces B_xt=0; then G_tau= B_tt=0. Separated one-dimensional V=f(x1)+g(t) solves (f'²+tau)f''+g''=0, so g'' is constant; the fit/growth condition forces that constant zero. None produces a finite-tau counterexample. These hand calculations are not a classification of all solutions.

## 7. Scope and contribution decision

The paid outputs are the trace-aware common-time/barycentric subsolution lemma, the fit-only horizontal-affine argument, the conditional extremal-contact reduction with its exact missing step, the separate conditional local-regularity reduction, and the explicit infinite-tau obstruction/classification. The proposed finite positive viscous Liouville theorem remains open in this investigation. No uniform p-harmonic gradient theorem, acceptance-count change, or new-to-literature theorem is claimed. This does not dispute I224 R/S, I228's stipulated PASS, or any pinned homogeneous lower operation.
