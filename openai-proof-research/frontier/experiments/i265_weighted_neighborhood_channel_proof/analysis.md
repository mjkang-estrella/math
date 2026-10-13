# I265 independent derivation and pressure checks

Verdict: PASS, correctness only, for I264 SHA256 `a0080234eacf4d410917e426222e3e89b24f9eba968cc815c4b46c5b59957395`. This is a mathematical analysis artifact, not executable research or a numerical experiment. The review contains the complete proof chain and primary contracts. The following calculations were independently derived rather than taken as valid from I264's experiment file or I260's verdict.

## Domains and ground-state transform

All vector norms are Euclidean. Potentials are bounded measurable and tend to zero in operator norm at infinity, being dominated by w. Therefore H, H0, h and Kf are self-adjoint on H² with H¹ forms. The compressed space QL² is closed; Q preserves H¹ and H² because psi belongs to those spaces. Compressions below are associated closed forms on H¹ intersect QL². There is no derivative of v, f or g in an operator definition.

Set t0(x)=a tanh(ra x). The identities t0²-t0'=a²-w and t0²+t0'=a²+(r-1)a² sech²(ra x) give the factorizations. A has domain H¹, kernel span(phi), and AA*>=a². Its inverse is bounded and ran(A*)=phi-perp. For u in H¹ intersect phi-perp, y=(AA*)^-1 Au is H² and A*y=u. Consequently

    q_h[u]=a²<y,Lplus y>+||Lplus y||².

The weighted coercivity constant is the inverse of

    2w0/a²+2(r+1)/(r-1)
      =2(r+1)+2(r+1)/(r-1)=2r(r+1)/(r-1).

Its reciprocal is c_w. In particular h is nonnegative on phi-perp, not strictly bounded below there by a positive unweighted constant.

The ground-state transformed domain consists of k with phi k in H¹. It equals the weighted domain k,k' in L²(rho), since phi'/phi=-t0 is bounded. Integration by parts on a core, then closure, gives

    q_h[phi k]+a²||phi k||²=integral rho|k'|²,
    ||(phi k)'||²+a²||phi k||²
        =integral rho|k'|²+integral w rho|k|².

Subtracting the rho mean and using h>=0 on phi-perp proves the stated Poincare inequality. Constants belong to the transformed domain. The minimization against bounded measurable g is thus a minimization over F=phi k in the ordinary H¹ space, with minimizer F=(-d²+a²)^-1(w g phi). It gives the exact Qform identity without smoothing the orientation.

## Nonlinear source and exact inverse estimates

Principal covariance, followed by a measurable sign change, gives alpha>=0 and integral w rho g=0 with g=alpha f. Write s=|f| and dmu=w rho dx. Then

    J=integral s² dmu, Tg=integral (1-s²)s² dmu,
    J-Tg=integral s^4 dmu.

The variance coercivity Qform(g)>=Tg/(r+2) implies

    J-B2=J-Tg+Qform(g)
          >=J-(r+1)Tg/(r+2)>=J/(r+2).

For orthogonal defects s=1, g=0, so this term is exactly J. This is why discarding large-angle information or substituting a pointwise Taylor error would be inadequate.

For B0 on Q, the free derivative-plus-mass energy is <=(r+2) times the B0 form. Scalar evaluation at any x has squared norm 1/(2a) in that free energy. Summing the squared component estimates proves the vector estimate with the same constant K=(r+2)/(2a). Thus the relative form perturbation is <=K integral ||U||<=K C1 sqrt(J)=epsilon.

Let R=Q(H-lambda1)Q. Its conjugated perturbation has norm at most epsilon+delta/a²<=t, with t=epsilon+J/a². The positive inverse inequalities are

    (1+t)^-1 B0^-1<=R^-1<=(1-t)^-1 B0^-1.

The exact Feshbach equation has both source components:

    delta=J-<b,R^-1b>,
    b=(Q_scalar(w s² phi),-w g phi).

The dual evaluation estimate is a bound on the functional paired against u perpendicular to phi. It does not estimate the L¹ norm after projection. Cauchy–Schwarz gives

    (integral w s² phi)²
       <=(integral w rho s²)(integral w s²)=J L2.

Therefore B1<=K J L2<=epsilon J. In particular B1/J->0 uniformly as J->0, while integral s^4 dmu/J need not vanish. The exact inverse order then proves the linear lower bound as follows:

    delta>=J-(B1+B2)/(1-t)
          >=J/(r+2)-epsilon J-t(1+epsilon)J/(1-t).

Since epsilon<=t<1/4, the error coefficient is <=2t/(1-t)<3t. With t<=1/[6(r+2)], it is <=1/[2(r+2)]. The displacement is between J/[2(r+2)] and J. No analytic perturbation branch is needed.

## Min–max ordering and full moments

The compressed lower comparison is S=(h/2 on phi-perp) direct-sum Kf. If mu_j denotes compressed negative variational levels, the two inequalities run in the directions

    lambda_(j+1)(H)>=mu_j>=lambda_j(S)=lambda_j(Kf)

whenever the last expression is negative, with zero padding after negative lists end. Larger negative eigenvalues have smaller absolute moments, so H's tail is bounded above by the full Kf moments. The removed test vector is psi, not the perturbed ground eigenvector; codimension-one interlacing still applies.

HLW is applied to the nonpositive potential V=-B_w w ff^T. Its negative trace is B_w w|f|², not a normalized matrix trace. Finite m and L2<infinity verify pointwise trace-class and trace integrability. For q=2gamma>1, HLW and sum t_j^q<=(sum t_j)^q yield a tail bound (B_w/2)^q L2^q.

Put Ahalf=integral sqrt(w)s². The critical factorization uses exponent 1/q:

    w s²=(w^p s²)^(1/q)(sqrt(w)s²)^(1-1/q),
    p/q+(1-1/q)/2=1.

This gives L2^q<=(w0^(1/r)/c²) J Ahalf^(q-1). The second Holder step uses the distinct theta=r/[4(r+1)]:

    sqrt(w)s²=(w rho s²)^theta
       [(sqrt(w)/(w rho)^theta)^(1/(1-theta))s²]^(1-theta).

Both exponents are strictly between zero and one; the two different interpolation exponents must not be conflated. Using s²<=1 gives Ahalf<=Ctheta J^theta. Hence the tail is <=N J^(1+beta), where beta=theta(q-1)=1/[2(r+1)]>0.

## Closed constants, convergence and scaling

For s>0 define the beta integral

    S(s)=integral_R sech^s(y) dy
        =sqrt(pi) Gamma(s/2)/Gamma((s+1)/2).

It supplies optional fully explicit versions of all profile integrals:

    c²=ra/S(2/r),
    Z=w0 S(2+2/r)/S(2/r)=2(r+1)a²/(r+2),
    C1²=w0 S(2-2/r)/(c² ra).

For the chosen theta, sqrt(w)/(w rho)^theta equals

    w0^(1/2-theta)c^(-2theta) sech^(1/2)(ra x).

Thus

    Ctheta=w0^(1/2-theta)c^(-2theta)
             [S(1/[2(1-theta)])/(ra)]^(1-theta).

Every S argument here is positive precisely in the stated range where needed: 2-2/r>0 requires r>1; the Ctheta argument is positive for theta<1. The displayed decay rates in I264 follow immediately.

Under varying a, J and Z scale as a², C1 is independent of a, K scales as a^-1, Ctheta as a^(-2theta), and m_gamma,M_gamma as a^(2gamma-2). With beta=theta(2gamma-1), N scales as a^(2gamma-2-2beta). Consequently all four terms defining tau scale as a², and N J^(1+beta) scales as a^(2gamma). The coefficients c_-,c_+ times J scale as the desired moment. This checks the exponents in the last tau term as well as the tail estimate.

Since delta<=J<=a²/[12(r+2)]<a²/8, the derivative of s^gamma is sampled in [7a²/8,a²]. The min/max formulas for m_gamma,M_gamma cover all three cases gamma<1, gamma=1, gamma>1. The last tau term is exactly the condition N J^beta<=m_gamma/[4(r+2)]. The first two lower-bound contributions therefore leave c_-=m_gamma/[4(r+2)]. Dropping the tail gives c_+=M_gamma.

For completeness, the exact constants validated in this review are

    B_w=1+2/c_w,
    N=(B_w/2)^(2gamma)(w0^(1/r)/c²)Ctheta^(2gamma-1),
    m_gamma=gamma a^(2gamma-2)min{1,(7/8)^(gamma-1)},
    M_gamma=gamma a^(2gamma-2)max{1,(7/8)^(gamma-1)},
    tau=min{Z/4, a²/[12(r+2)],
            [12(r+2)K C1]^(-2),
            [m_gamma/(4(r+2)N)]^(1/beta)},
    c_-=m_gamma/[4(r+2)], c_+=M_gamma.

Here beta=theta(2gamma-1), so 1/beta is exactly the exponent printed in I264, not a different threshold.

## Adversarial derivations

Take v=e2 on A and e1 off A. For integral_A w rho<Z/2, the covariance is diagonal and e1 is principal. Then J=integral_A w rho, f=1_A e2 and g=0. The operator is block diagonal. The branch correction satisfies

    0<=J-delta<=K J L_A/(1-t), L_A=integral_A w.

The first block h+w1_A has at most one negative eigenvalue because it is above h; the transverse block's moments are <=(L_A/2)^(2gamma) by the endpoint theorem. For A=[0,ell], J~w(0)rho(0)ell and L_A~w(0)ell, so this tail divided by J tends to zero as ell^(2gamma-1). For A=[R,R+1], J~c_J exp(-2a(r+1)R), L_A~c_L exp(-2raR), and L_A^(2gamma)/J=O(exp(-2aR)). Both imply delta/J->1 and

    D/J->gamma a^(2gamma-2).

More generally, for arbitrary measurable purely orthogonal defect sets with J->0, L_A<=C1 sqrt(J)->0, and the two weighted Holder bounds uniformly give a tail/J tending to zero. Thus this limit does not rely on interval regularity. It demonstrates that a uniformly o(J) deficit estimate would be false, while the proposed two-sided linear control survives.

Distribute many disjoint defect sets among e2,...,em. If their total weighted mass is <Z/2, e1 remains the principal covariance direction; total J and total unnormalized trace enter all estimates. No summation over channel-specific constants occurs. A sequence of rapidly oscillating or infinitely oscillatory measurable orientations presents no new domain issue because only the potential multiplier is used. Sign changes in v, however frequent, do not change P at all. Arbitrary finite m preserves all evaluation and form constants, so the argument has no hidden dimension loss.

## Decision boundary

No mathematical repair was identified. The candidate's optional missing form-domain notation and short min–max explanation are expanded here; they do not change a hypothesis, coefficient, or conclusion. The proof is still limited to real rank-one orientation fields with a fixed scalar soliton, small weighted J, finite m, and the open exponent range. It does not establish any converse, arbitrary-matrix stability, endpoint extension, or contribution/acceptance verdict.
