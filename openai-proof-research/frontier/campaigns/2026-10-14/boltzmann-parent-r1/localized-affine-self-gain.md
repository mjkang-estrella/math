# A spatially localized affine-packet self-gain barrier

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Status: parent author derivation, using analytic r52's same-width gain identity. The analytic author independently checked the square completions and weighted propagator below. Neither check is an independent campaign review. This is a single-scale supersolution, not a nonuniqueness theorem or nominee. The proposed full L² direction remains pre-freeze.

## Input inequality and parameters

Write G_D(vbar)=(pi D²)^(-1)exp(-|vbar|²/D²). Analytic r52's `same-width-gain.md`, read in full, proves

    P(G_D tensor n,G_D tensor n) <= G_D tensor B_D(n,n),
    M_D(B_D(n,n))=c D M_D(n)^2,
    c=2 pi^(3/2),    M_D(n)=integral exp(w²/D²)n(w)dw,

where B_D is a nonnegative axial density. The parent independently rederived its transverse square completion. This uses ordinary sphere area and the three-dimensional hard-sphere normalization of the pinned source.

Fix alpha,K,s,d,epsilon>0, sigma real, a bounded transverse set E, and C0>0. Set

    H=s+alpha t, h=H/s, D=d h^epsilon,
    U=(sigma+alpha z/s)/h, lambda=alpha/H,
    tau=(z-sigma t)/h, w=v3-U,
    A=K h^(2epsilon)/H.

Take beta>=1/[4epsilon(1+epsilon)] and let

    Ly=sqrt(beta) D H/alpha,
    Ltau=sqrt(beta) D s/alpha,
    dy=dist(y,E), dtau=dist(tau,[-C0s,C0s]),
    Phi=exp(-dy²/Ly²-dtau²/Ltau²).

All widths are strictly positive at t=0. In particular Phi(0)=1 on the initial spatial support, without differentiating its indicator.

## Transport computation

Let transport be partial_t+v dot grad_x. The affine profile satisfies

    transport U=lambda w,  transport w=-lambda w,
    transport tau=w/h.

Distance functions are Lipschitz. Almost everywhere along flights, completing a square gives

    transport log exp(-dy²/Ly²)
      >= -|vbar|²/(2 Ly Ly')
      = -alpha |vbar|²/[2beta(1+epsilon)D²H],

    transport log exp(-dtau²/Ltau²)
      >= -w²/(2h² Ltau Ltau')
      = -alpha w²/[2beta epsilon D²H].

For example the first expression before minimization is
2 Ly' dy²/Ly³-2dy(transport dy)/Ly², with |transport dy|<=|vbar|. This proves the bound even for a nonconvex E, in the almost-everywhere sense needed for path integration.

Put q(t)=alpha/[2beta epsilon H]. Choose a nonnegative axial density n_t solving

    partial_t n-lambda partial_w(w n)
       = A B_D(n,n)+q(t) w²/D² n.                      (1)

Define F(t,x,v)=A Phi G_D(vbar)n_t(w). Since

    A'/A-2D'/D=-lambda,

the transverse Gaussian derivative supplies +2epsilon alpha |vbar|²/(D²H). Our beta bound pays the negative transverse square-completion term exactly. The axial potential in (1) pays the other negative term. Consequently

    transport F >= A² Phi G_D B_D(n,n)
                >= P(F,F),                            (2)

where the last inequality uses Phi²<=Phi and the input gain bound. The statement can be read distributionally or along flights; n need not be classically smooth. It is a gain-only supersolution and does not incorporate interactions with another cold packet.

## Existence of the weighted axial majorant

The linear part of (1) has a positive propagator: contract w by h(u)/h(t) and multiply by the exponential of the integrated quadratic potential. Along this characteristic,

    d/dt [w(t)²/D(t)²]
       = -2(1+epsilon)lambda(t) w(t)²/D(t)².

Thus the potential integral is exactly

    delta [w(u)²/D(u)²-w(t)²/D(t)²],
    delta=1/[4beta epsilon(1+epsilon)]<=1.

It follows that this propagator contracts M_{D(u)} to M_{D(t)}. Positive Picard iteration for (1), dominated by the scalar Riccati inequality, gives a mild solution on every interval with

    c M0 integral_0^T A(u)D(u)du <1,
    integral_0^T A D = K d [h(T)^(3epsilon)-1]/(3epsilon alpha).

Here M0=M_d(n0). Its weighted mass satisfies

    M_{D(t)}(n_t) <= M0/[1-c M0 integral_0^t A D].       (3)

The nonlinear remainder has the corresponding Riccati difference bound. Positivity and the bilinear weighted estimate justify monotone convergence; bounded weighted balls also give uniqueness by Gronwall. For d=d0 s^a, fixed T and 0<3epsilon<a, the clock tends to zero with s. Hence (2) is uniform over all sufficiently small retained scales with a fixed safety margin in (3).

For the compact linear-drift datum from r52,

    1_E(y)1_{|z|<=C0s}(K/s)d^(-3)
         J((v-(sigma+alpha z/s)e3)/d),

take n0(w)=pi e ||J||_infinity d^(-1)1_{|w|<=d}. Its M0 is independent of d, and F(0) dominates the datum. Comparison with a particular colored evolution still requires the relevant mild comparison framework. Neither a global periodic solution nor its conservation properties follows solely from the displayed barrier.

## Unpaid obligations and a specific failure of summation

This argument controls repeated gains of one affine packet with its spatial tails. It does not control different packet widths, same-sign cross-scale gains, periodic copies, source branching after changing the drift, the full flat hot-source estimate, or global continuation. The original tanh first-gain estimate is a separate calculation; (1) does not establish the same closure for tanh drift.

Crucially, these barriers cannot simply be summed to obtain a finite pointwise cold-density bound. At fixed t>0,

    A_s(t) is of order s^(-2epsilon),
    Ly_s(t) is of order s^(a-epsilon).

For masks in annuli of radius comparable to s and 0<a<1/3, this transverse width eventually exceeds the annulus radius, so Phi's transverse factor approaches one on the axis. At z=sigma t its axial factor is also one. The resulting sum of the displayed upper bounds is divergent. This is a failure of these upper bounds to control a sum, not a lower bound or blow-up claim for the actual solution. Recovering transverse dilution, or a different summable control of cold density, remains necessary. Opposite-sign Gaussian tails alone do not resolve this same-sign problem.

The calculation supplies an intermediate construction mechanism only. It changes neither the campaign count nor the unchanged acceptance gates.
