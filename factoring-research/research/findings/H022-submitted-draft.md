# H022 — Threshold and norm-stratum envelope for primitive linear elements

2026-10-08. Parent analytic draft. **Independent review required.**
Uses the H020 weighted-count argument, now accepted after independent review.
The extension in this document remains unreviewed.
No implementation, finite experiment, parameter sweep or Lean theorem.
Verified full factoring complexity improvement: **NONE**.

This extends the proposed H020 count beyond its one parameter witness.
Under explicitly uniform normalized-root geometry and the declared two-sided
smoothness model, changing linear-element height and resultant thresholds
does not lower the single-polynomial model's optimum. With actual coefficient
height parameter gamma in [0,1], the proposed exact relaxed optimum is

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
algebraic extension to be reviewed; it does not alter H019's frozen protocol.

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

## 5. Mixing height and norm strata

Suppose one fixed f is partitioned into J_N disjoint primitive candidate
strata with log J_N=o(D). Suppose their a_j, Q_j, beta_j and attempted counts
have the above leading descriptions uniformly, and their geometry and
yield assumptions also hold uniformly. Use one common b>0.

If the total expected useful output reaches L[1/3,b], some stratum must
contribute at least that many up to an exp(o(D)) factor. If its attempt
exponent is u_j, it therefore satisfies (14) up to o(1). Its paid attempt
cost is part of the total work, so (17) applies to the total exponent.

This includes genuinely smaller algebraic norms under the stated conditional
yield law, rather than charging them the full-height probability. To use
fixed-width norm bins, take upper endpoints for population and lower endpoints
for the optimistic yield, retain their error, and let the fixed width tend
to zero after the asymptotic bound. Arbitrary adaptive bins do not receive
uniformity for free. Strata with a_j->0, delta changing without control,
exponentially many bins, or exceptional yield need separate treatment.

The argument is a leading-exponent necessary condition for modeled expected
collection. It is not a proof of rank, independence, success probability,
finite relation deficit or all-input root geometry. Repeated visits to a
primitive element cannot supply independent new candidates under this model.
Nonprimitive outputs can only add generation cost; no benefit from them is
silently ruled out for a different relation architecture.

## 6. Disposition and next action

**Provisional conditional closure of a larger single-polynomial model,
awaiting independent review.** The positive next research step cannot be a
mere retuning of Q or a relabeling of smaller-norm bins under these same
assumptions. A changed mechanism would need at least one of:

- useful fields whose certified geometry escapes the count, with selection
  and restart costs and useful yield established;
- a better justified useful-yield law for the selected candidates;
- a different relation space or sharing across multiple paid polynomials;
- construction of smaller-coefficient f for new input families, with its cost
  and scope made explicit.

These are reopeners, not assertions that any works. H021's structured lattice
generator is independent and remains active.

H020's parent lemma passed review without required corrections. The next
independent round can now review this extension; its task handle belongs in
tasks-H022.json when launched.
The next reviewer must audit (7)--(12), the actual-height gamma parameter,
all three inequalities, the relaxation's sharpness and the uniform stratum
argument. This draft supplies no new executable and requires no repeated
shared-code check. It must not be entered in STATE as an accepted theorem.
