# H025 — Independent review of the small-residual input-density bound

2026-10-08. Symbolic review only.

**Disposition: ACCEPT the finite-universe lemma and explicit cutoff; ACCEPT
the population-based density consequences conditional on acceptance of H024's
diagonal count; REVISE the opening scope statement in section 4.** No correction
to equations (1)–(3), (5), or (6) is required. This review does not independently
accept H024's theta-product theorem or its cost analysis.

Verified full factoring complexity improvement: **NONE**.

The complete 154-line [parent report](H025-small-residual-density.md) was read.
Its SHA256 matches the supplied review target:
`4bcd2ebcfb0cf6dba710a83172656da6597842db4bfea99c4bb1ef68e8b95b5c`.
I also read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, the H025 hypothesis, H021's disposition
and relevant construction/review sections, and the H024 parent draft.
The task's explicit live-review and ownership instructions govern this review;
the older STATE does not record the newly live H024/H025 work.

H021's accepted bounded-error rational-log construction is used as specified.
Its corrected optimizer recovery uses uncapped prefix predecessors generally,
and capped suffix recovery only when the minimum is at most the cutoff.
Neither recovery method is needed to prove the finite-universe lemma.
H024 remains a separate live dependency; H023 was not reviewed or duplicated.

**1. Fixed finite universe and actual residuals — ACCEPT independently.**

For each fixed integer ell>=2, take the common first ell primes and common
weights f_j=ceil(j/2). For finite real E_bar>=0,

    U_ell = {e in Z^ell : sum_j f_j^2 e_j^2 <= E_bar}

is finite: each coordinate satisfies
|e_j|<=floor(sqrt(E_bar)/f_j). Its definition uses no digits of N beyond ell.
For every fixed e, the stated positive and negative exponent products u_e,v_e
are fixed positive integers, with v_e>=1. The actual signed residual is
u_e-Nv_e. No rounding approximation appears in this residual.

The lemma does not need injectivity of e -> (u_e,v_e), coprimality, primality
estimates, logarithm distribution, or smoothness. These additional properties
of this construction are not being silently used to strengthen the count.

**2. Closed-interval integer count and union bound, equations (1)–(2) — ACCEPT
independently.**

For a fixed e the event is exactly

    (u_e-W)/v_e <= N <= (u_e+W)/v_e.

If a closed interval of length L contains m>=1 integers, its largest and
smallest such integers differ by at least m-1. Hence m-1<=L and
m<=floor(L)+1. An empty interval intersection satisfies the same upper bound.
Taking L=2W/v_e proves the first inequality of (1); monotonicity of floor and
v_e>=1 prove the second.

This proof covers W=0, noninteger W, negative lower endpoints, both closed
endpoints being integers, and intervals missing all integers. In particular,
a singleton at W=0 contributes at most one N, not zero. Restricting to

    I_ell = {2^(ell-1), ..., 2^ell-1}

can only remove integers. There are exactly 2^(ell-1) elements of I_ell.
Summing the individual counts and clipping at that size yields both bounds
in (2). Overlapping intervals cause harmless overcount; no disjointness or
independence assumption is present.

For the actual integer residual, 0<=W<1 can admit only residual zero. The
displayed bound is still safe even when it is loose. H021's interpretation
of residual zero is preserved: here u=Nv and gcd(u,v)=1 force v=1 and N=u.
Zero belongs to the counted event, but is not an ordinary smooth parity row.

**3. Arbitrary selection after seeing N — ACCEPT independently.**

Let S_N be any N-dependent subset of U_ell. Then

    {N in I_ell : exists e in S_N, |u_e-Nv_e|<=W}
      subseteq
    union over e in U_ell of {N in I_ell : |u_e-Nv_e|<=W}.

This is a pointwise set inclusion. It covers optimization, adaptive selection,
all choices of internal random bits, and even an uncharged oracle choosing
from U_ell. No selector runtime or selector success distribution is needed.
An N-dependent rounded log row or acceptance cutoff is harmless precisely
when it only determines such a subset. The bound need not hold without
containment in one common universe of fixed pairs (u_e,v_e).

**4. Explicit H024-rule cutoff, equation (3) — ACCEPT independently of the
theta-product and cost claims.**

Write ln for the natural logarithm. The elementary integral for ln 2 gives
1/2<ln 2<1. For the least power of ten C>=ell with ell>=2,
ell<=C<10ell and C>=10. H021 supplies integer coefficients satisfying
|a_1-C ln 2|<=1 and |T-C ln N|<=1; exact nearest rounding of the true
logarithm is unnecessary.

Every inequality used in the parent cutoff is valid, including at ell=2:

    a_1 >= C/2-1 >= 2C/5 > 0,
    a_1 <= C+1 < 10ell+1 <= 11ell,
    T >= C ln N-1 > C/2-1 > 0,
    T <= C ln N+1 <= C ell+1 <= (11/10)C ell.

The last bound uses C ell>=20, which is more than sufficient. Since
r=floor(T/a_1+1/2), the exact rational rounding rule, including a tie,
satisfies

    |r-T/a_1| <= 1/2,
    |r| <= (11ell/4)+1/2 <= 3ell,
    |a_1 r-T| <= a_1/2.

The vector e_star=(r,0,...,0) has first-coordinate weight f_1=1. Therefore

    E_star = F_N(e_star)
           = r^2+(a_1 r-T)^2
           <= 9ell^2+(121/4)ell^2
           = (157/4)ell^2 < 40ell^2.

For every accepted vector, q(e)<=F_N(e)<=E_star implies membership in the
same U_ell with E_bar=40ell^2. No assertion that all elements of U_ell pass
the rounded objective is needed. Feasibility also bounds the true global
minimum, but E_star is not asserted to equal that minimum. This checks the
local cutoff interface required by H025 without reviewing H024's DP or
prime-generation cost ledger.

**5. H024 population substitution, equations (4)–(5) — ACCEPT as a conditional
implication; dependency not accepted by this review.**

The required dependency is exactly

    M_k(E) = #{e in Z^k : sum_j ceil(j/2)^2 e_j^2 <= E}
            <= exp(11 E^(1/3))  for E>=1 and every finite k.

H024 states a diagonal-universe bound, not merely a bound on an N-dependent
F-sublevel set, so its proposed interface is the one H025 needs. For
0<=E<1 the count is exactly one because any nonzero coordinate has energy
at least one. Consequently the small-energy edge cases introduce no gap.

Assuming the displayed dependency, substitute E=40ell^2 and
K=11*40^(1/3) into the independently accepted finite lemma. This gives (5)
exactly. The finite lemma and explicit cutoff remain accepted if H024's
count later requires repair; the constant/exponent consequences must then
be recomputed from the accepted replacement. No dependency interface issue
was found. The theta-product derivation and H024's full costs were not
independently audited here.

**6. Fixed power saving, subexponential windows, and rate — ACCEPT conditional
on the population dependency.**

For fixed 0<epsilon<1, every N in I_ell satisfies
N^(1-epsilon)<2^((1-epsilon)ell). Thus one may use the common real window
W_ell=2^((1-epsilon)ell); inserting a different N-dependent W directly into
the single-universe count would not be a valid substitute for this step.

The floor bound and the exact denominator give

    (floor(2W_ell)+1)/2^(ell-1)
      <= 4*2^(-epsilon ell)+2^(1-ell).

The constants 4 and 2 in (6) are correct. Since epsilon is fixed in (0,1),
the logarithm of its unclipped right-hand side is

    -(epsilon ln 2)ell + K ell^(2/3) + O(1),

which tends to minus infinity. This is an upper probability bound, not an
asymptotic equality for the actual exceptional density. It includes residual
zero and any N-dependent accepted subsets from item 3.

The hypothesis's broader phrase "fixed epsilon>0" is also covered: for
epsilon>=1, N^(1-epsilon)<=1, and the already stated constant window W=1
suffices. No uniformity as epsilon decreases with ell is established by the
fixed-epsilon conclusion.

If W_ell=exp(o(ell)), then ln(floor(2W_ell)+1)=o(ell), while
K ell^(2/3)=o(ell). The claimed upper density
exp(-(ln 2)ell+o(ell)) follows. A zero window also satisfies this upper bound
directly. Finite-ell clipping at one is essential; the large constant K
does not establish a useful practical bit-length threshold.

**7. General energy and the cubic boundary — ACCEPT conditional on the count,
with exactly the parent's limitation.**

For nonnegative E_bar(ell)=o(ell^3), the count exponent
11 E_bar(ell)^(1/3)=o(ell); bounded and subunit energies are handled by item 5.
Replacing K ell^(2/3) by this term preserves the fixed-power-saving conclusion.

As an algebraic check of the boundary wording, if E_bar=c ell^3 for a fixed
c>0, the leading exponent in that bound becomes

    [11 c^(1/3) - epsilon ln 2]ell + O(1).

It can still be negative for sufficiently small c. Energy of order ell^3
alone therefore gives neither universal decay nor universal failure of this
bound. Equality or a positive exponent leaves the displayed estimate
inconclusive, not a lower bound on actual supply. No sufficiency of larger
energy and no per-input energy necessity follows. This substitution audit
is not a proposed new algorithm or a sharp population threshold.

The separate comment about H021 is sound within its accepted magnitude
conditions: retaining polynomial numerical k,C,E retains polynomial DP/count
ranges. It supplies no useful output distribution or factoring runtime.

**8. General input distributions and restricted sets — ACCEPT.**

For a probability distribution mu supported on I_ell, write
p_max=max_N mu(N). The exact finite proof gives

    Pr_mu[exceptional]
      <= min(1, p_max * sum_{e in U_ell}(floor(2W/v_e)+1))
      <= min(1, p_max * |U_ell| * (floor(2W)+1)).

Thus p_max<=exp(-h ell) yields the stated inequality, without assumptions
about independence between arithmetic quantities. This finite statement
does not need H024; replacing |U_ell| by its proposed exponential bound does.
A vanishing probability still requires the resulting right-hand side to
vanish; the point-mass condition is not by itself such a conclusion for
every choice of h and W.

For a uniform nonempty A_ell subseteq I_ell, the denominator is |A_ell|.
The ambient denominator 2^(ell-1) cannot be retained after conditioning on
an arbitrary restricted set. No balanced-semiprime density conclusion is
accepted without the additional input-set size argument. A distribution
concentrated on exceptional N is consistent with all the accepted results.

**9. Common parameters and a finite family of universes — ACCEPT in the
stated scope.**

The first-prime list, its identification with exponent coordinates, weights,
and energy envelope must provide one common small universe for each ell.
They may depend on ell. N-dependent choices are covered only if their union
is independently bounded. In particular, a weight permutation preserves an
individual ellipsoid's cardinality but need not preserve its exponent set
or the union of the resulting fixed pairs.

For K_ell predetermined universes with uniform population bound M_ell, the
stated further union bound is at most
K_ell M_ell(floor(2W)+1), before clipping and normalization. Finiteness alone,
without a quantitative cardinality bound, offers no asymptotic guarantee. Cardinality,
uniform envelopes and parameter selection cannot be omitted. This counting
observation pays no algorithmic construction cost and supplies no adaptive
base-selection algorithm.

**10. Required scope correction — REVISE section 4's opening paragraph;
REJECT its interpretation as a theorem for every o(N) threshold.**

The phrase "a sublinear-in-N absolute residual" followed by "for almost all
inputs" is broader than the proved fixed-power-saving conclusion. For
example, the symbolic threshold N/ell is o(N). Taking the common window
2^ell/ell in the displayed bound gives

    min(1, exp(K ell^(2/3)) * [4/ell + 2^(1-ell)]),

which equals one eventually. This shows the inference is unsupported; it
does not assert that the actual exceptional density for N/ell is large.
It is a scope check, not an experiment or a new residual-supply claim.

Replace the first paragraph of parent section 4 with:

> Subject to acceptance of H024's diagonal count, for each fixed
> 0<epsilon<1 the fraction of all ell-bit integers N admitting any vector
> with F_N(e)<=E_star(N) and |u_e-Nv_e|<=N^(1-epsilon) tends to zero at the
> upper rate in (6), irrespective of how the vector is selected. This
> excludes that fixed-power-saving small-residual mechanism for almost all
> inputs under the uniform ell-bit distribution, without a random-integer
> smoothness premise. It does not establish the same conclusion for every
> threshold o(N).

This is a local wording repair. The existing general finite bound remains
available for any specified common W, even when its numerical value is
uninformative. No equation or parent hypothesis needs changing to make the
core result valid.

**11. Factoring and smoothness consequences — ACCEPT the stated limitations;
REJECT stronger interpretations.**

The accepted object is a count of inputs admitting at least one small actual
residual from a fixed universe. For a fixed N all these residuals are
deterministic. The result does not show that larger residuals are nonsmooth,
that smooth rows have suitable parity rank, that square-root extraction
produces a proper factor, or that factoring is hard. It does not establish
H024's hypothesized exponential useful-event rarity under adaptive selection.
Zero residuals and favorable exceptional inputs are allowed. No all-input
algorithm lower bound, transformed-LLL-domain theorem, or full factoring
complexity improvement is accepted.

The required next action is the section 4 wording repair and consumption of
H024's separate count disposition. No implementation, experiment, benchmark,
parameter sweep, Lean change, or new infrastructure is needed for this
disposition. No new research extension is proposed here; any later stronger
energy, residual-window, ensemble, or adaptive-parameter claim requires
further review.

Only this owned review file was created. No parent report/hypothesis, shared
code, Lean, STATE, registry or old evidence was edited; no packages, recursive
delegation, commits, publication or scheduler were used. No executable research
or finite experiment was run. Verification consisted of symbolic derivation,
reading, and source-hash checks; no new formal theorem is claimed.

Additional source identities at review intake:

```text
c533d11821394b952da686fe5ac8387d87a2886f7f55356babaeb222f66db977  research/hypotheses/H025.md
8f510430d375c2dcc41507f583436edff5978eb3fbbb084402ffadf27323b5c8  research/findings/H024-low-energy-population.md
60b8b96b2140658e9b9ad32ac2fad06a381d228425ee76f1dbcb8681a68ad9cd  research/findings/H021-disposition.md
655afec1540a6f59099ceef793dd0687405111540b84ee55db8854a9fc26131a  research/findings/H021-structured-lattice-generator.md
fbf77260be74592643de25ac35655d5d1f94d3d4896f3ba46e123b01cfed3221  research/findings/H021-independent-review.md
```
