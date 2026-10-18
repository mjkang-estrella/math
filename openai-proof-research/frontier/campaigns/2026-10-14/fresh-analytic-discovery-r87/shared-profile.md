# The actual shared-profile adjoint and a valid L2 tail bound

The full target and r85 scope freeze remain unchanged. Read LRS arXiv1207.6582v1 Section3, extracted lines960–1095, including Proposition3.1 and the conclusion of Theorem1.2. This actual proof uses

 F_(j,t)(r,x)=2^(3j/q) 1_(I_j)(r) kappa(r)t^(-2) f_t(x),

with the SAME f_t across j. Therefore the arbitrary-profile inequality in r85 is sufficient, but stronger than necessary. For a fixed localized radial critical multiplier m and q=p/(p-1), the needed local-dilation adjoint statement is

 ||integral_1^2 T_(m(t.)) f_t dt||_{L^(q,infinity)}
 <= C_q ||integral_1^2 |f_t|dt||_q,                              (AP)

where delta=3/q-2>0. The smooth low-frequency part is already paid by the Hardy–Littlewood maximal bound. The global-dilation assembly from a valid(AP) is the actual LRS Lemma3.2 argument; it is credited, not a new operation. In particular, proving only an estimate with integral||f_t||_q on the right would not prove(AP).

## 1. Dyadic frequency-distance pieces preserve the input norm

Write the nonsmooth part of m(s)=(1-s)_+^delta a(s), with a smooth and supported near s=1. Squared-radius Bochner–Riesz has the additional smooth factor(1+s)^delta, absorbed in a. A partition in u=1-s gives

 m_j(s)=2^(-j delta) b_j(2^j(1-s)), j>=j0,

where b_j have common compact support in(1/2,2) and uniformly bounded derivatives. Let T_(j,t) have multiplier m_j(t|xi|), for1<=t<=2. All relevant xi lie in a fixed annulus. For each xi, the set of t where this multiplier is nonzero has length at most C2^(-j). Consequently Plancherel gives

 ||T_(j,t)g||_{L2_x L2_t} <=C2^(-j(delta+1/2))||g||_2,
 ||partial_t T_(j,t)g||_{L2_x L2_t} <=C2^(j(1/2-delta))||g||_2.    (1)

For a scalar smooth function u on[1,2],

 sup_t|u(t)|² <= C ||u||_2 (||u||_2+||u'||_2).

Apply this at each x, integrate, and use Cauchy–Schwarz in x with(1). Then

 ||sup_(1<=t<=2)|T_(j,t)g|||_2 <= C2^(-j delta)||g||_2.           (2)

For f_t, duality gives the EXACT mixed-input estimate

 ||integral_1^2 T_(j,t)f_tdt||_2
 <=C2^(-j delta)||integral_1^2|f_t|dt||_2.                        (3)

Indeed the pairing with g is bounded by integral_x [integral_t|f_t(x)|dt] sup_t|T_(j,t)^*g(x)|dx; self-adjointness is unnecessary because the adjoint multiplier obeys the same estimates. Thus no interchange to L1_t(L2_x) is made.

Summing(3) for j>J gives

 ||sum_(j>J) integral T_(j,t)f_tdt||_2
 <= C_delta 2^(-J delta)||integral|f_t|dt||_2.                    (4)

This is a consequence of shared input and the shrinking t support of the multiplier. It is NOT the impossible arbitrary radial-profile Lq(H)->L2 estimate from r85. In particular it does not extend LRS Lemma2.2 beyond q=4/3.

## 2. What amplitude splitting pays, and the exact remaining exponent

For restricted-weak inputs with integral|f_t(x)|dt<=1_E(x), (4) bounds the long-tail level-lambda set by

 C_delta lambda^(-2)2^(-2J delta)|E|.

The full operator is L2 bounded after summing all j, so levels lambda>=1 already obey the desired bound C lambda^(-q)|E| for q<2. The genuine endpoint difficulty for(AP) is at small lambda.

The annular radial multiplier has ||K_j||_1<=C 2^(j(1-delta)) in dimension three. Here is a direct proof: put h=2^(-j). The exact radial Fourier formula is K_j(r)=C/r integral s m_j(s) sin(rs)ds. Substitution s=1-hu and integration by parts in the fixed compact u interval give |K_j(r)|<=C_N h^(delta+1) r^(-1)(1+hr)^(-N) for r>=1. For r<1, the Fourier integral is bounded by C h^(delta+1). Integrating against r²dr gives O(h^(delta-1)), as asserted. This familiar calculation is used to quantify the elementary L1/L2 strategy, not as a nominated result. The t dilations preserve the L1 norm. Hence the low-j part has L1 norm at most C 2^(J(1-delta))|E| when0<delta<1. Combining Markov with(4) gives

 measure{|S f|>C lambda}
 <=C |E|[lambda^(-1)2^(J(1-delta)) + lambda^(-2)2^(-2J delta)].   (5)

The balancing choice is2^(J(1+delta)) approximately lambda^(-1). It yields exponent

 q_bal=2/(1+delta),

whereas our actual target is q=3/(2+delta). Their difference is

 q_bal-q=(1-delta)/((1+delta)(2+delta))>0.

For the unpaid range q∈[4/3,3/2), delta∈(0,1/4], so this gap is substantial. Since lambda<1, a larger exponent is a worse distribution bound. Thus(5) is a valid partial estimate and not a proof of(AP).

Replacing the L2 tail by a source-derived subcritical q0 estimate would approach the desired exponent, but its epsilon loss leaves a positive gap; taking epsilon→0 without uniform constants is invalid. The fixed-profile L2 improvement is useful because it identifies the true mixed norm and the small-level regime that a new phase-preserving argument must address. It does not remove that regime.

## 3. Relation to the cluster mechanism

The preceding local vector restriction and long-radius cluster estimates may be used on spatial pieces of the common f_t, retaining their shared kappa(r). Such a strategy must preserve the Lq_x(L1_t) norm in(AP). Orthogonality in t after replacing L1_t by L2_t is not automatically permissible; likewise, scalar endpoint bounds followed by Minkowski yield the larger integral||f_t||_q and do not settle(AP).

The absolute-overlap counterexample only excludes absolute aggregation of separate spherical-wave outputs. It does not exclude cancellation available from the shared radial kernel. A future assembly should address(AP) directly, rather than silently strengthening it to arbitrary independent profiles. Full critical maximal bounds for every p>3 remain unresolved in this packet.
