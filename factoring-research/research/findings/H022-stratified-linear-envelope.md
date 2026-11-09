# H022 — Threshold and norm-stratum envelope for primitive linear elements

2026-10-08. Conditional mathematical model **accepted after independent review
of Sections 1–4 and coordinator checking of the review-supplied Section 5 repair**.
Uses the accepted H020 weighted-count argument. Original reviewed bytes are
preserved in [H022-submitted-draft.md](H022-submitted-draft.md), SHA256
`ecae556871c90be3eb31bc0b7bcba49d58e201079d4603a86e71cc1dfa09754f`.
See [review](H022-independent-review.md) and [disposition](H022-disposition.md).
No implementation, finite experiment, parameter sweep or Lean theorem.
Verified full factoring complexity improvement: **NONE**.

This extends the accepted H020 count beyond its one parameter witness.
Under explicitly uniform normalized-root geometry and the declared two-sided
smoothness model, changing linear-element height and resultant thresholds
does not lower the single-polynomial model's optimum. With actual coefficient
height parameter gamma in [0,1], the exact optimum of the displayed relaxation is

    c_*³ = 32(1+gamma)/9.                                (1)

For gamma=1 this is the usual GNFS constant cubed, 64/9. For gamma=0 it is
32/9, consistent with the smaller-coefficient special-family scale. Keeping
gamma is essential: a theorem for arbitrary ordinary-base polynomials must
not silently assume their coefficient height is always comparable to m.

The argument also treats a subexponential number of height/norm strata,
subject to uniform geometry, error terms and the same conditional yield law
in each stratum. It does not prove that yield law or uniform geometry.
Multiple polynomial selection, biased smoothness samplers and a different
relation representation remain outside this single-polynomial model.

## 1. Sequence, scales and actual coefficient height

Let t=log N tend to infinity, with natural logarithms, and put

    D=t^(1/3)(log t)^(2/3),
    V=t^(2/3)(log t)^(1/3),
    d=(delta+o(1))(t/log t)^(1/3), delta>0 fixed.

For each N, use the checked monic square-free ordinary-base polynomial f,
m=floor(N^(1/d))>=2, actual degree d, f(m)=N. Its coefficient height A
satisfies A<=m. Along the sequence assume an actual limiting height parameter

    log A = (gamma/delta+o(1)) V,   0<=gamma<=1.         (2)

Subsequences can accommodate limits where they exist. No distribution of
digits or ability to construct a desired gamma is assumed. Small A is a
real change of the norm model, not merely another height bin for g.

Fix H with log H=(a+o(1))D, a>0, and a nonnegative threshold parameter Q.
Consider normalized primitive g=xX+y, 1<=x<=H, |y|<=H, and nonzero norms,
at the global threshold

    |Res(f,g)| <= T,
    T=(2H)^d(d+1) A N^(-Q/d).                           (3)

Floors select the same integer norms, so (3) is a real threshold for proof;
rational Q permits an exact cleared-power implementation. Write

    z=a delta²,    K=1+gamma-Q,
    beta=(z+gamma-Q)/delta.                             (4)

Then log T=(beta+o(1))V. A nonzero-norm leading-size stratum requires
beta>=0; if beta<0 the set is eventually empty. Thus the meaningful range
is 0<=Q<=z+gamma. Thresholds above the universal norm envelope have Q<0
and cannot describe a distinct larger leading-size norm population here.

Uniformly on the entire coefficient box,

    m-H <= |xm+y| <= H(m+1),

and m/H tends to infinity. Hence

    log |g(m)|=(1/delta+o(1))V.                         (5)

Smaller x or actual g-height changes lower-order rational size, but not its
leading V coefficient within this fixed L[1/3] coefficient regime. There is
no exceptional rational cancellation at this scale: x>=1 and m>H prevent it.
For algebraic norms, substantially smaller values do matter and are parameterized
by Q/beta instead of assigned the full-height probability.

## 2. Generalized weighted containment, conditional on H020

Choose r roots with modulus at least 2H+2, put k=d-r>=2, and let kappa be
a certified positive lower bound on half the minimum normalized pair
separation among the k remaining roots. Assume

    log(1/kappa)=o(D).                                  (6)

All roots, including both members of nonreal conjugate pairs, are counted.
The selected large-root subset need not be maximal. Its actual complement
must be the one for which (6) holds.

H020's determinant proof gives at most k primitive exceptions with a
normalized evaluation <=1/(4H). Its large-root bound retains x/2, and all
but one remaining evaluation are >=kappa*h, h=max(x,|y|). Repeating the
same derivation at the generalized cutoff (3), every nonexception satisfies

    x^r h^(k-1) < W,
    W=4*2^r*4^d*(d+1)*H^(d+1)*kappa^(-(k-1))*N^(-Q/d). (7)

This is a discrete containment, not an inference from volume.

For rational Q=p/q with p>=0,q>=1, (7) can be cleared using exponent qd:

    ae=qd(k-1), be=qdr,
    V_int=kappa_den^ae [4*2^r*4^d*(d+1)*H^(d+1)]^(qd),
    U_int=N^p kappa_num^ae,
    U_int*x^be*h^ae < V_int.                            (8)

The same dyadic rectangles and V_int-1 endpoints as H020 apply. This is an
accepted algebraic extension; it does not alter H019's frozen protocol.
A bit-cost implementation must separately bound the magnitudes of p and q
and the cleared integer widths. Binary encoding alone does not make qd-th
powers polynomial size.

Let theta=r/d. Because M(f)<=sqrt(d+1)A,

    limsup theta <= min(1,gamma/z).                     (9)

This improves the worst-case 1/z bound when the actual coefficient height
is smaller. With xi=log x/D and tau=log h/D, the dyadic counting argument
gives 0<=xi<=tau<=a+o(1) and

    theta*xi+(1-theta)*tau <= a-Q/delta²+o(1).           (10)

All constants in (7), its extra H and the dyadic factor contribute o(1)
after division by dD. The count has O(log H) bands, so the logarithm of
their number is o(D). This requires the errors in (2), (6), and the degree/
height scales to be uniform over any family of strata used later.

For theta<=1/2, (10) gives a count exponent <=2a-2Q/delta².
For theta>=1/2 it gives <=2a-Q/(theta*delta²). The latter is increasing
in theta when Q>=0. Combining with (9) yields

    log(max(1,S_prim))/D <= max(0, a F_gamma(z,Q))+o(1), (11)

where for gamma>0,

    F_gamma(z,Q) =
      2-2Q/z       if z>=2gamma,
      2-Q/gamma    if gamma<=z<=2gamma,
      2-Q/z        if 0<z<=gamma.                       (12)

Boundary formulas agree. For gamma=0 only the first branch applies.
The max with zero retains the O(d) exceptional candidates when the
nonexception region has no positive exponent. The theorem concerns primitive
distinct elements; all-output enumeration costs remain additional.
F is an upper envelope, not necessarily the pointwise sharp feasible count.
For example, gamma<z<2gamma and Q=z force only xi=tau=0 asymptotically,
although (12) is positive. This does not affect the relaxed optimum below.

## 3. One norm stratum: exact conditional relaxation

Retain the model of one common smoothness bound B=L[1/3,b], b>0.
Assume, rather than infer from a norm upper bound, that candidates in a
stratum of actual algebraic leading norm coefficient beta have joint
useful-yield exponent

    -(1/delta+beta)/(3b) = -(z+K)/(3b delta).            (13)

For the necessary-direction conclusion it suffices that their expected
useful yield per distinct paid attempt is at most this modeled exponential
rate. Such an upper-yield statement is NOT proved by the counting theorem.
If the sampler changes the law, the following conclusion need not apply.

To obtain L[1/3,b] useful relations from L[1/3,u] distinct attempts, the
model requires

    u >= b + W_norm/(3b),
    W_norm=(z+K)/delta,
    0<u<=a F_gamma(z,Q).                               (14)

A claimed work exponent c must be at least u; matrix cost adds c>=2b.
Coefficient-line enumeration adds c>=a, but the lower bound below does not
need either additional cost. Since beta>=0, W_norm>0, and (14) implies u>b.

From b(u-b)>=W_norm/3 and b(u-b)<=u²/4,

    W_norm <= 3u²/4.                                   (15)

Since delta²=z/a and a>=u/F, squaring (15) gives

    u³ >= 16(z+K)² / [9z F_gamma(z,Q)].                 (16)

Positive u requires F>0. No sufficiency of a population upper bound is used
in this lower bound on the conditional relaxation.

Put A0=1+gamma. The three branches each imply u³>=32 A0/9:

1. z>=2gamma. Put w=z-Q>0, so zF=2w and z+K=w+A0.
   Equation (16) becomes

       u³ >= 8(w+A0)²/(9w) >= 32 A0/9,

   because (w-A0)²>=0.

2. gamma<=z<=2gamma, gamma>0. Here F=(2gamma-Q)/gamma>0,
   so Q<2gamma and K=A0-Q>0. By (z+K)²>=4zK,

       gamma(z+K)² >= 4gamma*z*K
                    >= 2A0*z*(2gamma-Q).

   The second inequality has difference
   2z Q(1-gamma)>=0. Substitution in (16) gives the result.

3. 0<z<=gamma. Here zF=2z-Q>0. The exact identity

       (z+A0-Q)² - 2A0(2z-Q)
         = (Q-z)² + A0(A0-2z) >= 0

   holds because z<=gamma<=1 implies A0-2z>=1-gamma>=0.
   Again (16) gives u³>=32 A0/9.

Thus any such successful modeled stratum has

    c>=u>= [32(1+gamma)/9]^(1/3).                      (17)

This includes thresholds stronger than H018's eta>=0 range whenever their
norm coefficient and nonexception population are meaningful.

## 4. Sharpness of the relaxed inequalities, not achieved population

The lower bound is sharp as an optimization of these inequalities. Set

    u=[32 A0/9]^(1/3), b=u/2,
    delta²=2 A0/u, a=u/2, Q=0.                         (18)

Then z=A0>=2gamma, F=2, and aF=u. Also
W_norm=sqrt(2 A0 u)=3u²/4, so (14) is equality.
The extra scan and matrix constraints c>=a and c>=2b permit c=u.
A slightly larger u gives strict collection slack in this relaxation.

More generally 0<=Q<=A0 with the same delta and
a=u(A0+Q)/(2A0) has z=A0+Q, F=2A0/(A0+Q), aF=u and the same W_norm.
Tightening the threshold while increasing the coefficient box leaves this
relaxed optimum unchanged. None of these assignments proves a useful
candidate lower bound, the yield law, or an algorithm attaining c.

At gamma=1, (17) is the conventional GNFS constant (64/9)^(1/3).
The smaller multiple-polynomial Coppersmith constant belongs to a different
model and is not contradicted here. The baseline distinction is retained in
[W001 baselines](../hypotheses/W001-baselines.md); the primary
[Lee–Venkatesan optimization and Remark 4.31](https://arxiv.org/html/1805.08873v1)
also state these two different constants. No new general factoring baseline
is claimed. At gamma=0 this relaxation gives (32/9)^(1/3), matching the
coefficient-size advantage expected for suitable special-form inputs.

## 5. Mixing height and norm strata: precise conditional scope

This section incorporates the independent review's sufficient repair, checked
by the coordinator. It covers expected collection with a predetermined
reference partition. Every assumption below is part of the model, not a
proved property of actual factoring candidates.

Use one f_N and degree sequence with fixed delta>0, actual gamma in [0,1],
and one fixed common b>0. Let J_N disjoint bins have log J_N=o(D).
There are fixed constants 0<a_min<=a_max<infinity with

    a_min<=a_j<=a_max,    0<=Q_j<=a_j delta²+gamma.

The parameters may vary with N and j. Require uniform errors in the degree,
height, actual f-height, cutoff and rational-norm asymptotics, and uniform
population estimates. For each bin's containing height box require a valid
root split with k_j>=2 and sup_j log(1/kappa_j)/D=o(1). No lower bound on
k_j/d away from zero is needed. Fixed positive a_min ensures a compact
positive-z domain; bounded a_max and Q_j control the discarded errors.

Each bin contains only nonzero algebraic norms between leading coefficients
beta_j^- and beta_j^+, up to uniform o(1) errors, and each member satisfies
the actual upper cutoff T_j used for counting. Set

    0<=beta_j^-<=beta_j^+,
    beta_j^+=(a_j delta²+gamma-Q_j)/delta,
    beta_j^+-beta_j^-<=Delta,
    W_j^-=1/delta+beta_j^-,    W_j^+=1/delta+beta_j^+.

Population uses the upper endpoint and useful-yield assumptions use the
lower endpoint. A negative lower norm coefficient is clipped at zero.
Zero resultants receive no smoothness credit. Rational zero is excluded
eventually by m>H_j.

Let M_j be the random number of distinct paid attempts in bin j, Y_j its
newly credited useful outputs, C_N the total paid work, and S_j the
deterministic population upper bound. Require pathwise

    M_j<=S_j,    sum_j M_j<=C_N,

with at most one new modeled output per distinct attempted element. Require
the following aggregate law for the actual selection and stopping strategy:

    E Y_j <= p_j E M_j,
    p_j <= exp((-W_j^-/(3b)+epsilon_N)D),
    epsilon_N>=0, epsilon_N->0 uniformly.               (19)

An unconditional average for uniform samples does not establish (19) for a
biased sampler, post-selection, or adaptive stopping. One sufficient stronger
hypothesis is a conditional history-wise law. Just before paid attempt l,
let F_(l-1) contain continuation/selection decisions and all information used
to choose the candidate. Let I_(l,j) mark a new attempt in j, zero after
stopping, and let Z_l in [0,1] be its newly credited output. Assume

    E[I_(l,j)Z_l | F_(l-1)]
       <=p_j E[I_(l,j) | F_(l-1)]                       (20)

for every permitted history and bin. Taking expectations and summing
nonnegative terms yields (19), including a stopping time; no independence
or optional-stopping theorem is used. Finite claimed expected work is required.
This is an explicit model assumption, potentially very strong when selection
already reveals usefulness. It is not a theorem about deterministic norms.

A partition chosen after observing successes is not automatically covered.
Reduce such a strategy to predetermined reference bins satisfying (19) with
all selection charged, or prove a separate uniform conditional theorem that
also preserves the unconditional expected-work bound.

Assume modeled collection and work satisfy

    sum_j E Y_j >= exp((b-o(1))D),
    E C_N <= exp((c+o(1))D),    c finite.                (21)

For a uniformly vanishing mesh Delta_N->0, necessarily

    c³>=32(1+gamma)/9.                                 (22)

For one fixed positive mesh at most Delta the supported conclusion is

    c³+(8/3)c Delta+(16/9)Delta²/b >=32(1+gamma)/9.       (23)

Alternatively, (22) follows if partitions satisfying all the same uniform
laws exist for every arbitrarily small fixed Delta for the same strategy:
first take N to infinity in (23), then Delta to zero. Subdivision must
preserve the yield law; one coarse partition is insufficient.

**Proof.** Pigeonhole the expected outputs to choose a bin j(N) with
E Y_j>=exp((b-o(1))D). Put u_N=log(E M_j)/D. Uniform (19), population
and paid work give

    u_N>=b+W_j^-/(3b)-o(1),
    u_N<=max(0,a_j F_gamma(z_j,Q_j))+o(1),
    u_N<=c+o(1).

Compactness supplies a convergent subsequence of a_j,Q_j,u_N and endpoints.
F is continuous across its branch boundaries for fixed gamma on the compact
positive-z domain. The limiting inequalities, with u>b>0 and F>0, imply

    u<=aF, u<=c,
    W^+<=W^-+Delta<=3b(u-b)+Delta<=3u²/4+Delta.

Section 3's three branch inequalities give (z+K)²/(zF)>=2A0,
where A0=1+gamma, so

    (W^+)²=a(z+K)²/z>=2A0u,
    2A0u<=(3u²/4+Delta)².

Divide by 9u/16 and use b<=u<=c to get exactly (23). With Delta_N->0
the same proof gives (22). No fixed winning index or pre-existing attempt
exponent limit is assumed. No independence between bins is needed. The union
of their at-most-k_j exceptions has size at most J_N d=exp(o(D)), which
cannot meet a positive-b collection target even if every exception is useful.

The relaxed mixed model has the same infimum as Section 4 when delta and
the permitted compact ranges can include its one-bin equality witness.
For a prescribed f/degree sequence, only the lower bound follows; equality
may be unavailable. Unbounded heights, vanishing b, uncontrolled degree,
adaptive partitions without the yield law, or a changed sampler need separate
analysis. This proves no rank, proper split, success probability or actual
geometry/smoothness law. Nonprimitive processing remains paid; other relation
architectures are outside the model.

## 6. Disposition and next action

**Accepted conditional closure of this explicitly bounded single-polynomial
model.** The positive next research step cannot be a
mere retuning of Q or a relabeling of smaller-norm bins under these same
assumptions. A changed mechanism would need at least one of:

- useful fields whose certified geometry escapes the count, with selection
  and restart costs and useful yield established;
- a better justified useful-yield law for the selected candidates;
- a different relation space or sharing across multiple paid polynomials;
- construction of smaller-coefficient f for new input families, with its cost
  and scope made explicit.

These are reopeners, not assertions that any works. H021's structured lattice
generator is independent; its mathematical construction has passed review,
while its useful-population problem remains open.

Sections 1–4 passed independent review without algebraic correction. Section 5
now states and proves the review-supplied compact expected-work formulation;
the coordinator checked its conditional summation, subsequence and mesh-error
steps. See the disposition for provenance and exact acceptance scope. No
executable, numerical experiment, shared-code change or Lean theorem was added.
