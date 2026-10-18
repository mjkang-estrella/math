# Same-width transverse gain and an affine-flow envelope

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Status: author calculations, before any target freeze. These are single-packet analytic estimates, not a nonuniqueness theorem, a nonlinear spatial localization result, or a campaign nominee. Parent author assistance is credited below. All collision formulas use the hard-sphere normalization in October source `03-kernel.tex`, Lemma `lem:carleman`, equations `ker:carleman` and `ker:sphere-law` (read through line 170). In particular the incoming-pair output is r times ordinary sphere area, where r is half the relative speed.

## 1. An exact transverse-width-preserving upper bound

Let D>0 and G_D(y)=(pi D^2)^(-1) exp(-|y|^2/D^2) on R^2. For nonnegative finite axial measures nu,mu define weighted measures

    nu^sharp(da)=exp(a^2/D^2) nu(da),
    M_D(nu)=nu^sharp(R).

Assume these weighted masses are finite. Then the measure gain of G_D tensor nu and G_D tensor mu has a Lebesgue density and

    P(G_D tensor nu,G_D tensor mu)(vbar,z)
      <= G_D(vbar) B_D(nu,mu)(z),                         (1)

where

    B_D(nu,mu)(z)
      =2 pi exp(-z^2/D^2)
         integral exp(-(z-a-b)^2/D^2) nu^sharp(da) mu^sharp(db).

Here B_D is an axial density, and Tonelli gives exactly

    M_D(B_D(nu,mu) dz)=2 pi^(3/2) D M_D(nu) M_D(mu).     (2)

The width D in (1) is the SAME width as in both transverse inputs. No bound on an axial density is assumed. An isotropic Maxwellian at this exact D has infinite M_D, so it is outside this assertion's weighted-mass hypothesis.

Proof. Condition on axial input coordinates a,b. The transverse center Y=(pbar+qbar)/2 and half-difference W=(pbar-qbar)/2 are independent with densities

    (2/(pi D^2)) exp(-2|Y|^2/D^2),
    (2/(pi D^2)) exp(-2|W|^2/D^2).

Put m=(a+b)/2, e=(a-b)/2 and r=(|W|^2+e^2)^(1/2). The output sphere has center (Y,m) and radius r. For r>0 its density as a measure is delta(|v-(Y,m)|-r)/r. The zero-radius event has zero collision mass. Integrating W in polar coordinates gives |W| d|W|=r dr; this cancels the denominator r. Consequently the conditional output density is

    8/(pi D^4) integral_{R^2}
      exp(-2[|Y|^2+|v-(Y,m)|^2-e^2]/D^2)
      1_{|v-(Y,m)|>=|e|} dY.

Drop the indicator. Completing the transverse square gives its integral bounded by

    (2/D^2) exp(-|vbar|^2/D^2)
       exp(-2[(z-m)^2-e^2]/D^2).

Finally

    2[(z-m)^2-e^2]=z^2+(z-a-b)^2-a^2-b^2.

Integration in nu and mu proves (1), including the coefficient 2 pi. All steps are nonnegative measure integrals, so atomic axial laws are included directly. Equation (2) follows by integrating the remaining translated axial Gaussian. The same upper bounds hold for the source's collision-rate cutoff since its multiplicative factor is at most one.

## 2. A precise affine-flow supersolution

Fix s>0, alpha>0, K>0, sigma real, D>0. Put

    h(t)=1+alpha t/s,
    U(t,z)=(sigma+alpha z/s)/h(t),
    lambda(t)=alpha/(s+alpha t),
    A(t)=K/(s+alpha t).

Thus U_t+U U_z=0 and U_z=lambda. Let n_0 be a nonnegative axial density with M_0=M_D(n_0 dz)<infinity. Let S(t,u) be pushforward of axial densities under w -> [h(u)/h(t)]w. It contracts the weighted L1 norm M_D because h(u)/h(t)<=1. On a time interval [0,T] satisfying

    theta(T)=2 pi^(3/2) D M_0 integral_0^T A(u)du <1,    (3)

there is a positive weighted-L1 mild solution

    n_t=S(t,0)n_0 + integral_0^t A(u) S(t,u)B_D(n_u,n_u) du.  (4)

Moreover

    M_D(n_t) <= M_0/[1-theta(t)].                       (5)

One construction is monotone Picard iteration from the first term of (4). Formula (2) and the scalar Riccati solution bound every iterate by the right side of (5). Monotone convergence in weighted L1 gives (4). The bilinear weighted bound also gives uniqueness in bounded weighted-L1 balls by Gronwall. For initial densities, S is a strongly continuous contraction on weighted L1. The spatial transport assertion below can alternatively be interpreted distributionally; no smoothness of n_0 is silently assumed.

Define

    F(t,x,v)=A(t) G_D(vbar) n_t(v3-U(t,z)),  x=(y,z).

It is independent of y. With w=v3-U, the identity

    (partial_t+v dot grad_x)F
       =A(t) G_D(vbar)[partial_t n-lambda partial_w(w n)]
       =A(t)^2 G_D(vbar) B_D(n,n)(w)
       >=P(F,F)(t,x,v)                                (6)

follows from (1), Galilean translation of the gain, A'/A=-lambda, and (4). This is a gain-only supersolution. Its velocity mass is bounded by A(t)M_0/[1-theta(t)]. The normalized mass contributed by the second term of (4) is at most M_0 theta(t)/[1-theta(t)]. Therefore its velocity mass is at most

    C K^2 D log(1+alpha t/s)/(s+alpha t)                (7)

when theta(T)<=1/2, with C depending on alpha,M_0. This is a repeated-self-gain estimate, not just the first iterate. The logarithm arises from the exact clock integral (K/alpha)log(1+alpha t/s).

For D=d_0 s^a, a>0, fixed alpha,K,T, theta(T)->0 as s->0. Thus (3) holds uniformly for every sufficiently small retained scale, without a cutoff-dependent constant.

## 3. Relation to a possible compact packet construction

Consider the different, linear-drift prototype

    f_s^0(x,v)=1_E(y) 1_{|z|<=C_0 s} (K/s) d^(-3)
                  J((v-(sigma+alpha z/s)e3)/d),

with a fixed smooth nonnegative unit-ball-supported J, and take D=d. This has bounded initial velocity support uniformly in s. It is dominated by F(0) if

    n_0(w)=pi e ||J||_infinity d^(-1)1_{|w|<=d}.

Indeed exp(-|vbar|^2/d^2)>=e^(-1) on the support of J. M_0 is independent of d. For E of area comparable to s^2 this packet has the same Lp scaling s^(3-p)d^(3-3p) as the original tanh-profile packet. In particular d=s^a, a<1/3, permits a summable L2 datum over disjoint geometric annuli.

This paragraph changes a pre-freeze proposed packet, NOT a frozen theorem. It does not assert that the source's branching theorem survives the replacement. Equation (6) is a supersolution statement on the unperiodized prototype. Applying it by comparison to a chosen colored evolution additionally requires its usual mild comparison framework; no global periodic comparison or finite-mass property of F is claimed. F itself has infinite total spatial mass and ignores E and the axial cutoff.

## 4. What this does not close

The same-D argument uses identical transverse widths. It does not yet control collisions between different scales, spatial masks after repeated gain, or periodic copies. Dropping the axial and transverse masks in F prevents it from proving the needed flat opposite-color source. Nonlinear high-order collisions do not retain compact velocity support merely because the first gain does. Neither (6) nor (7) proves the source's H-sheet estimate for a summed, spatially localized cold family, the seed amplification, full global entropy continuation, or exact local conservation for a new construction. The full provisional L2 nonuniqueness direction remains unfrozen and unresolved.

## 5. Authorship and chronology

The same-width identity and affine-flow idea were derived in analytic r52 after the actual free-packet first-gain estimate. Parent author assistance independently rederived the transverse square completion and warned that the isotropic Maxwellian has divergent weighted axial mass. The parent separately proved the actual tanh packet's first-gain mass bound in `boltzmann-parent-r1/free-first-gain.md`, read in full here. These are author-side checks, not independent reviews. The latter note does not prove (4) for tanh drift. No novelty conclusion follows from this calculation, and no contribution gate has been run.
