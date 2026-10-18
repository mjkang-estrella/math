# Family 363: broad cold jets, before scope freeze

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

No full target has been frozen or proved. The intended direction is one nonnegative initial density in L²(T³×R³), with bounded velocity support, admitting two distinct global entropy solutions in the FULL October source class: strong L¹ continuity including the initial trace, exact local mass/momentum/energy conservation, entropy dissipation, and separately integrable collision gain and loss with every polynomial velocity weight on bounded time intervals. None of those conclusions is being weakened to obtain a nominee. The current outcome is an unresolved construction interface with supporting estimates.

This note records the original packet test. The first-gain question below has subsequently been answered by parent author assistance. `same-width-gain.md` proves a repeated-self-gain envelope for a different affine prototype. `cross-scale-interface.md` explains precisely why these estimates do not close the required multiscale construction.

## Source normalization and original packet

The operative source is `private/preprints/Nonuniqueness-with-local-conservation-for-the-hard-sphere-Boltzmann-equation-October-5-2026/build/paper/`. Dimension is three in both space and velocity. Write x=(y,z), v=(vbar,v3), with transverse coordinates in R². The torus is the rotated unit lattice from source `04-construction.tex`; its axis is (1,sqrt(2),0)/sqrt(3).

The kernel is |(v-v*) dot omega| with ordinary area measure on S² and Lebesgue dv*. With a=(v-v*) dot omega, v'=v-a omega and v*'=v*+a omega,

    P(f,g)(v)=integral |a| f(v')g(v*') dv* d omega,
    nu_f(v)=2 pi integral |v-p|f(p)dp.

The hot comparison weight is H(v)=exp(-|v|²)<v>^(-100)(1+|vbar|^(-q)), 1<q<2. This q concerns an auxiliary hot norm, not the initial datum's Lp integrability.

The source packet at scale s and sign sigma is

    c_s^0(x,v)=1_{E_s^sigma}(y)1_{|z|<1/8}
       (K/s) S(gamma z/s) d_s^(-3)
       J((v-U_s^0(z)e3)/d_s),
    S(r)=sech²(r), U_s^0(z)=sigma+alpha tanh(gamma z/s).

Here J is a fixed smooth probability density supported in the unit ball. The source takes geometric scales, stripe period s², d_s=d_0 s^10, and an annulus of transverse radius comparable to s with quarter-period masks of opposite signs. Its cold barrier has isotropic velocity width d_s, amplitude K/s, correction size C L_s d_s/s and retirement time L_s=s^(-1/2). Long-lived disjointness uses L_s d_s much smaller than the stripe period. This condition fails for the broad widths below.

## Initial integrability and free transport

The proposed broad width is d_s=d_0 s^a with 0<a<1/3; the proposed stripe period is s^(1+b), 0<b<a. These are pre-freeze construction parameters. They do not assert that the source proof survives the replacement.

For each fixed p>=1,

    integral |c_s^0|^p dx dv
       is comparable to s^(3-p) d_s^(3-3p)
       =constant times s^[3+3a-p(1+3a)].                (I)

Indeed the transverse area is comparable to s², the axial integral of S^p is comparable to s, and the velocity integral contributes d_s^(3-3p). For the lower bound, use a central axial interval of length comparable to s and many full stripe cells in a fixed rectangle inside the annulus. The constants depend only on the fixed mask/profile parameters, p and J. Disjoint spatial masks make the p-th powers additive. Thus L² summability is exactly available when 1-3a>0. The source's a=10 directly gives only p<33/31 by this calculation. Changing q does not change (I).

At t comparable to s, the thermal transverse displacement is O(s^(1+a)), smaller than the stripe period when b<a. The period after dilation x/s is s^b, which tends to zero. These two microscopic requirements are compatible with L², but the original long-retirement disjointness is not.

Let f_s(t,x,v)=c_s^0(x-tv,v). The source's implicit axial variable satisfies p3=U_s^0(z-tp3)+d_s w3, and

    f_s(t,x,p)dp
      =[K S(gamma(z-tp3)/s)/(s+t alpha gamma S(...))]
        J(w) times the initial spatial masks dw.

The fraction is at most C/(s+t). For fixed w3, the transverse mask permits wbar in a set of area at most C min(1,s²/(t²d_s²)). Hence

    rho_s(t,x)<=C/(s+t) min(1,[s/(t d_s)]²).           (F1)

The spatial integral of rho_s is O(s²), so

    integral_0^t1 integral rho_s² dx dt
       <=C s² log(1+t1/s).                            (F2)

Minkowski in L² of spacetime and geometric summability of s sqrt(log(1+t1/s)) bound the collision mass integrals of the TOTAL FREE family. Velocities remain uniformly bounded, and integrated gain mass equals integrated loss mass. These are free packets, not nonlinear solutions.

On the unperiodized family, sum_s rho_s<=C/t. Split scales according to t d_s<=delta s for a small fixed delta. In that part, relative enlargements of the annuli have bounded overlap; each term is O(1/t). In the other part, sum the quadratic factor in (F1) over geometric scales. Bounded-time periodicization meets only finitely many lattice translates for free packets with bounded velocities. The same split and the separate bound C/s_N give C/(t+s_N) for finite truncations. This argument does not control nonlinear gains between periodic copies.

## The exact first-gain test and what now follows

The original requested test was

    G_s(t,x,v)=integral_0^t P(f_s,f_s)(u,x-(t-u)v,v)du,
    integral G_s(t,x,v)dv
       <=C K² d_s log(1+t/s)/(s+t).                   (G)

Parent author assistance proved (G) for the actual tanh packet, including its spatial masks and transverse support enlargement by sqrt(2)t d_s. The proof retains a broadened derivative Lambda of the Burgers profile and changes axial velocity by a monotone map whose Jacobian cancels one power of Lambda. It is copied with exact provenance under `author-support/`. It controls the first iterate only.

The same-width gain formula in `same-width-gain.md` retains the transverse Gaussian width and closes a Gaussian-weighted axial measure equation for an affine drift. The parent localized that affine envelope with Gaussian spatial tails. The localized envelopes cannot simply be summed: they lose (F1)'s transverse dilution, and their sum diverges near the axis. `cross-scale-interface.md` proves both a useful mixed-width bound and exact failures of two overly large envelope classes.

## Remaining full-construction obligations

A usable nonlinear cold norm must simultaneously retain transverse dilution, actual joint axial/transverse concentration, and a gain bound against H uniform over all retained scales. Same-sign cross-scale gains cannot simply be put into the hot seed equation: the source's dormant cap requires spontaneous production bounded by C_A t^(A-1)H for an exponent A larger than its fixed Gronwall and seed exponents. Mere integrability or an arbitrary small power is insufficient.

Opposite stripes can first overlap only at scales much smaller than t under the proposed geometry; axial separation then suggests flat production. This remains conditional on a suitable nonlinear envelope. Any affine or isotropic drift replacement also needs the actual branching/accessibility proof re-established. Full global continuation with local conservation and strong traces is another obligation, since the source's long-lived disjoint-color retirement cannot be imported.

No statement above establishes the proposed L² nonuniqueness result. The exact reading boundaries and antecedents are recorded separately. No numerical check, supporting lemma, or failed norm earns a campaign count.
