# Proposed full proof of Mendonça–Smii Conjecture 6.1

Status: complete ordinary argument proposed for independent adversarial review. No acceptance, novelty clearance, formal certificate or manuscript is asserted. This file proves the full symmetric range 0<α<2, assuming the classical killed heat-kernel theorem explicitly identified below. No estimate here is attributed to the conjecture's authors unless labeled as theirs.

## Exact target and primary dependencies

Mendonça–Smii, https://arxiv.org/pdf/2608.17927v3, Conjecture 6.1, PDF p19: for every 0<α<2, iid symmetric stable innovations of characteristic function exp(−σ^α|q|^α), σ>0, and starting point x>0, the AR(1) exponential persistence rate satisfies

    lim[a↑1] Λ(a,α)/log(1/a) = α/2.

Their Theorems 1.2 and 5.4 establish that the limit exists, and identify Λ(e^(−h/α),α)=λ_α(h), the rate per sample of the stationary Lamperti process. Lemma 5.2 proves continuous log-time rate 1/2 by the stable first-passage asymptotic, domination and the finite α/2 moment. Lemma 5.3 proves λ_α(h)/h≤1/2. Those actual proofs on pp15–19 were read. The desired missing direction is liminf λ_α(h)/h≥1/2.

The additional classical dependency is Bogdan–Grzywny–Ryznar, *Heat kernel estimates for the fractional Laplacian with Dirichlet conditions*, Ann. Probab. 38 (2010), 1901–1923, https://arxiv.org/pdf/0905.2626v4, Theorem 1, equations (38)–(39), Example 2, electronic PDF p15. Their proof of Theorem 2 and its half-space application were read. They apply in dimension d≥1 and 0<α<2. For D=(0,∞), all t>0, x,y>0, their upper bound implies

    k_t(x,y) ≤ C (1∧x^(α/2)t^(−1/2)) p_t(y−x).                 (H)

The second boundary factor was discarded because it is at most one. This is valid for all times for a half-space; using the bounded-domain small-time statement alone would be an error. Their equation (4) gives the free stable density bound, hence finite p-moments for every p<α. Their preliminaries p7 state joint continuity of the killed density; their p6 boundary-regularity discussion applies to the half-space examples. These are classical dependencies, not new results.

## 1. A weight with uniform continuous-time decay

Fix α and choose α/2<p<α (for example p=3α/4). Write β=α/2 and w(x)=1+x^p on [0,∞). Let L be standard symmetric α-stable Lévy motion starting at zero. Start the log-time OU process deterministically at x≥0:

    Y_s^x = exp(−s/α)[x+L_(exp(s)−1)], s≥0.

This has the same transition kernel as the Lamperti process in source Lemma 5.1. Let Q_T be its semigroup killed on exiting (0,∞), including Q_T f(0)=0. With t=exp(T)−1 and c=exp(−T/α),

    Q_T w(x) = ∫_0^∞ [1+c^p y^p] k_t(x,y) dy.               (1)

The free stable moment inequality is

    ∫_0^∞ y^p p_t(y−x)dy ≤ C_p(x^p+t^(p/α)).                (2)

It follows directly from y^p≤C_p(x^p+|y−x|^p) and stable scaling; it does not require p≤1.

For T≥1 and x≤t^(1/α), (H), (1), (2) give

    Q_Tw(x) ≤ C x^β t^(−1/2)[1+c^p(x^p+t^(p/α))]
             ≤ C x^β exp(−T/2).

Since sup[x≥0] x^β/(1+x^p)<∞, this is ≤C exp(−T/2)w(x). For x≥t^(1/α), discard killing and use (2):

    Q_Tw(x)/w(x) ≤ [1+C c^p(x^p+t^(p/α))]/(1+x^p)
                  ≤ C exp(−pT/α)
                  ≤ C exp(−T/2).

Here t and exp(T) are uniformly comparable for T≥1. Consequently there is a finite C=C(α,p), INDEPENDENT OF T≥1, such that

    ||Q_T||_w ≤ C exp(−T/2),                                (3)

on the Banach space of Borel f with norm sup[x≥0]|f(x)|/w(x). For positive kernels the operator norm equals sup Q_Tw/w. This uses p>α/2 essentially. An unweighted supremum over all initial x would instead have norm one and would not work.

## 2. Uniform fixed-block convergence, including the boundary and infinity

Fix T>0. Let h_m=T/2^m, N_m=2^m, and

    K_m f(x)=E[f(Y_T^x); Y_(jh_m)^x>0, 1≤j≤N_m].

The endpoint payoff and total duration T stay fixed as m varies. The sampled-survival events A_m(x) decrease under dyadic refinement. They contain continuous survival. Up to a null event their intersection equals continuous survival for x>0. Indeed any strictly negative value before T persists on a right interval and is detected by sufficiently fine grids. If exit occurs by hitting zero before T, regularity of zero for the negative half-line and the strong Markov property produce strictly negative values immediately afterward. Exit exactly at T with value zero has probability zero, since the endpoint stable law has a density. At x=0, regularity likewise makes the intersection have probability zero. These observations deal with strict positivity and touching zero, not merely path convergence in distribution.

Thus, for every x≥0,

    d_m(x):=(K_m−Q_T)w(x) ↓ 0.                              (4)

For each finite m, K_mw is continuous on [0,∞): use the common path formula, continuity of the endpoint payoff, zero probability of any sampled coordinate being exactly zero, and domination by C_R(1+|L_t|^p) for x∈[0,R]. Q_Tw is continuous in the interior by joint continuity of k_t and the integrable density bound (H) and equation (4) of the heat-kernel paper. On compact x ranges the latter bounds the large-y integrand by C(1+y^p)y^(−1−α). At zero, (H) bounds Q_Tw(x) by C_T x^β, so Q_Tw extends continuously by zero. Hence d_m is continuous on every compact [0,R]. Dini's theorem applied to (4) gives uniform convergence on each such compact.

It remains to prove that infinity is uniform in m. Couple all starting points using the same L. Let M_t=sup[0≤u≤t]|L_u|. If continuous survival fails from x>0 by T, then M_t≥x. Also

    w(Y_T^x) ≤ C_T(1+x^p+M_t^p)

when the terminal state is positive. Therefore, for x≥1,

    0≤d_m(x)/w(x)
      ≤ C_T{P(M_t≥x)+E[M_t^p;M_t≥x]/x^p}.                 (5)

The right side tends to zero as x→∞, uniformly in m. The required E M_t^p<∞ holds for every p<α: Lévy's maximal inequality for symmetric independent increments gives P(M_t>u)≤2P(|L_t|>u) (an immaterial larger constant also suffices), first on finite grids and then by càdlàg paths. Integrating the tail and the free stable p-moment proves the assertion. No moment of order ≥α is used.

Combine compact uniform convergence with (5). Since K_m−Q_T is a positive kernel,

    ||K_m−Q_T||_w = sup[x≥0] d_m(x)/w(x) →0.               (6)

This is the genuinely uniform estimate needed for long-time iteration. It is stronger than finite-horizon path convergence at a fixed initial point. It treats arbitrarily small overshoots implicitly through compact convergence and boundary regularity, and large starting positions through the weight and maximal moment. No claimed power-law rate in h is needed.

## 3. Iterate a fixed block before choosing its length

For each fixed T≥1, (3), (6) imply

    limsup[m→∞] ||K_m||_w ≤ C exp(−T/2).                   (7)

Let b_m=||K_m||_w>0. By the Markov property, K_m^k describes survival over kN_m sampled steps. Since 1≤w and K_m is positive,

    P_x(Y_(jh_m)>0, 1≤j≤kN_m)
       =K_m^k1(x) ≤ b_m^k w(x), x>0.                     (8)

The persistence rate from deterministic x is the same rate as in the source's stationary Lamperti reduction (Proposition 1.1 and Theorem 5.4). Taking k→∞ in (8), with m and T fixed, yields

    λ_α(h_m)/h_m ≥ −log(b_m)/T.                            (9)

Only after taking that long-time limit do we send m→∞ in (7), obtaining

    liminf[m→∞] λ_α(T/2^m)/(T/2^m) ≥ 1/2−(log C)/T.        (10)

The source already proves existence of the full h↓0 limit, so the same limit appears on the left for every fixed T. Finally let T→∞. The constant C in (3) is independent of T, hence the full limit is ≥1/2. The source's opposite inequality makes it equal to 1/2. With h=α log(1/a),

    Λ(a,α)/log(1/a) = α λ_α(h)/h → α/2.

This holds separately for every α∈(0,2); no uniformity in α is asserted or required. It holds for every σ>0 and every x>0 by the source's rate and scale invariance. This completes the full Conjecture 6.1 argument.

## Strongest substantive objections and scope limits

The vulnerable point is (6), not the already-known continuous exponent. A reviewer should independently check boundary regularity, Dini continuity for the unbounded terminal weight, the positivity norm identity and the uniform tail bound (5). If any of these failed, fixed-time convergence alone would not prove (9) uniformly in m. They are spelled out above to expose that issue. The all-time half-space scope in (H) is also indispensable; a bounded-domain or fixed-small-time citation would leave (3) unproved. The original source has a typographical sign issue in a general killed-semigroup display on electronic p6; this proof uses its explicitly defined killed transition kernel and (38)–(39), not that erroneous display.

The proof appears to be a short classical semigroup argument once the correct weight is selected. A complete publicly available general dense-killing theorem, if located, could subsume the entire target. Neither mathematical correctness nor discovery eligibility is inferred from the source's open label. Current public-registry heads and comprehensive citing literature remain unavailable/unverified under the parked access restrictions. Root must adjudicate novelty and routine-corollary objections; no count increase is requested. The skewed conjecture is not proved by this symmetric heat-kernel citation.
