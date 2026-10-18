# Working amplitude interface — not a frozen claim

Myeongjin Kang. Original prose CC BY 4.0. Author-side exploration, 2026-10-18. Source truths stipulated at fd4aeeb2; r48 immutable. No nomination or contribution disposition yet.

## Exact intended object

The lattice law has exponent b_c sum_edges cos(theta_x-theta_y)+h sum_x cos(theta_x), each unordered nearest-neighbor edge once, h dimensionless, and b_c the source free-correlation mass threshold. Write Delta p(h)=p(h)-p(0), m(h)=p'(h) for h>0 and g(h)=h^(1/15)(log(1/h))^(1/15). The intended question is whether m(h)/g(h) has a positive finite limit. No target is frozen at this exploratory checkpoint.

## A better sandwich than raw boundary surgery

For a finite square Q, X_Q=sum_Q cos(theta_x). Ginibre monotonicity in nonnegative local fields implies

    |Q|^(-1) log E_infinite,0 exp(h X_Q) <= Delta p(h).

Indeed differentiate the finite-block logarithm, compare the local-field state to the uniform h state, sum over Q, and integrate from zero. The infinite zero-field state here is the free-box limit; the finite-volume argument is taken to this limit before varying Q.

The upper comparison is

    Delta p(h) <= |Q|^(-1) log E_Q,+,0 exp(h X_Q),

with pinned boundary sites included in X_Q (their contribution is deterministic). It follows by applying the aligned-boundary magnetization comparison in the uniform h state and integrating. These are comparisons of *increments*. No O(boundary size) energy surgery appears. The exact boundary comparison still requires the classical plane-rotator hypotheses, not an Ising GHS substitution.

This sandwich reduces the limit interchange to a zero-field whole-plane block-field limit and equality of the two continuum large-tilt pressure coefficients. It does not establish either automatically.

## Normalization bookkeeping

D=(-1,1)^2, K_*=2/pi, and the source Dirichlet Green kernel is (2pi)^(-1) log(1/|z-w|)+R_D(z,w). In log-one GFF notation beta=1/2. Let mu_D be ultraviolet-only Wick imaginary chaos epsilon^(-1/8) exp(i beta Gamma_epsilon), rather than full-variance Wick chaos. The source theorem and Green diagonal convergence give, for compact interior tests,

    (n^2 a_n)^(-1) sum f(x/n) exp(i theta_x) -> kappa mu_D(f),
    kappa=exp(R_D(0,0)/(2K_*)).

The spatial Green factors cancel exactly. The source center amplitude is a_n~A_XY n^(-1/8)(log n)^(1/16). A whole-plane neutral limit, if established, has the same kappa: kappa^2 equals the source bulk shape constant exp((4pi^2/(8pi)) R_D(0,0)). A uniform global phase must be added to whole-plane chaos before taking its real part.

For h_n=t/(n^2 a_n), the preceding sandwich would read

    F_whole(kappa t)/4 <= liminf n^2 Delta p(h_n)
       <= limsup n^2 Delta p(h_n) <= F_Dirichlet(kappa t)/4,

where F is the logarithmic Laplace transform of the real total chaos on D. If both F(t)/(4t^(16/15)) converge to one c_cont in (0,infinity), then choosing n for each fixed t and subsequently t->infinity yields

    Delta p(h)/(h^(16/15)(log(1/h))^(1/15))
        -> c_cont (kappa A_XY)^(16/15) (8/15)^(1/15).

Convexity then yields the magnetization amplitude (16/15) times this constant by the ordinary two-sided secant argument. This bookkeeping is technical and conditional here.

## Actual antecedents checked so far

Fröhlich (1976), DOI10.1007/BF01609843, Theorems4.5 and4.7, proves existence and positive finite homogeneous pressure for the *neutral* continuum Coulomb gas. With alpha=beta^2/2=1/8, its exponent is16/15. This does not by itself identify the Dirichlet nonneutral ensemble coefficient.

Leblé–Serfaty–Zeitouni (arXiv1510.01955v2), Proposition1.1/Corollary1.3, supplies canonical neutral plasma free-energy asymptotics. Its appendix has normalization/proof issues explicitly corrected in Aru–Baverez–Jego–Junnila (arXiv2401.14942), Theorem1.6 and AppendixB: the whole-plane chaos absolute-value tail exponent is4/beta^2=16, not2/beta^2. We use the corrected formulation, not the original appendix's erroneous stochastic-domination inference.

Junnila–Saksman–Webb (arXiv1806.02118), Sections4.4–4.5, gives fixed bounded-domain sine-Gordon tilting and exponential uniform-integrability transfer. It does not supply a growing-tilt lattice/thermodynamic interchange.

The pinned logarithmic-correction source, geometry.tex, already supplies k-nest attachment factorization but states the pinned-rim lower sector lemma for two holes and one joining arc. A fixed finite neutral configuration admits disjoint arcs pairing opposite charges; simultaneous strip restoration appears to be the relevant extension. It must be written with every pin and component convention retained. No all-orders uniform estimate is inferred from fixed-k attachment constants.
