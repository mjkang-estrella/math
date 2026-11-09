# W005 F — review of the compatible rational trace generator

2026-10-08. **Recommendation: accept the displayed identities and the narrow
global-branch failure, with the domain and scope completions below.** The
generator genuinely constructs an ordinary square after choosing the second
trace. It does not acquire a useful modular parameter. Verified new complete
factoring improvement: **NONE**.

This is new review round F, not an extension of an earlier child. Work was
symbolic derivation, reading and report authoring only: no numerical execution,
experiment, solver/Lean change, package installation, delegation or commit.
Only this owned report was written. Governing instructions, README and the live
checkpoint were read; the mathematical inputs were the supplied brief,
[actual W005 note](W005-compatible-field.md), [W004 construction,
especially §§1–5](W004-biquadratic-construction.md), and the precise interface
passages in [the sampler note](W005-blinded-norm2.md) and
[its review, §§2–6](W005-blindnorm-review.md). No archived review was reopened.

## 1. Exact comparison with the original W004 target

Throughout, N is odd, `gcd(N,30R)=1`, R is a unit square modulo N with its
accepted integer representative, `t=2R`, `u,v` are integers,
`s=u^2+v^2=5R mod N`, and `f_1(T)=T^2-s*T+t^2` is irreducible over Q.
The outer x, when mentioned, satisfies `x^2=R mod N`; it is not an allowed
inner input. Local branch formulas below are congruences at the stated modulus.

The original full system (5), with both traces fixed and root `a+b*alpha_i`, is

    u^2+v^2 = s_j,
    a^2-t^2*b^2 = t^2*(v^2-u^2),
    2*a*b+s_i*b^2 = u^2*(s_i-v^2)-t^2.                 (W004.5)

W005 fixes the first equation, writes `a=t*H`, `b=k`, parametrizes
`H^2-k^2=d=v^2-u^2`, and solves the last equation for `s_i=s_2`. This is a
real change of computation: the second trace is variable. The genus statements
for W004's fixed-trace curve do not obstruct this parametrized surface, and
genus is not a running-time lower bound in either setting. Conversely, solving
the rational equations after freeing a trace does not impose its required
modular residue.

For `d != 0`, every rational point of `H^2-k^2=d` has
`tau=H+k != 0`, `H-k=d/tau`, so this parametrization covers the rational conic.
For `d=0` it covers only the nonzero `H=k` component; `H=-k` and the zero
point need separate treatment. The additional *modular* restriction that tau
be a unit can restrict certificates outside the clean domain. The clean branch
analysis uses unit d, so neither conic exception enters that analysis; the
chart is exhaustive there as qualified at the end of §4.

## 2. Constants, rational denominators and field tests

Put `a_0=u^2`, `b_0=v^2`, `s=a_0+b_0`, `c=a_0*b_0+t^2`. Reduction modulo
`T^2-s_2*T+t^2` gives exactly

    Q(T) = t^2*d + (a_0*s_2-c)*T,
    (t*H+k*T)^2 = t^2*d + (2*t*H*k+k^2*s_2)*T.

Consequently `D=k^2-a_0` and `s_2=-(c+2*t*H*k)/D` have the stated sign
and constants. Useful fully cleared expressions are

    L = tau^4-2*s*tau^2+d^2
      = (tau^2-(u+v)^2)*(tau^2-(u-v)^2),
    D = L/(4*tau^2),
    s_2 = -(2*t*tau^4+4*c*tau^2-2*t*d^2)/L.           (6)

There is no lost solution at `D=0` for the accepted irreducible first field.
Then `k=±u`, `H=±v`; the remaining coefficient equation requires
`c+2*t*H*k=(uv±t)^2=0`. But `uv=±t` makes
`s^2-4*t^2=(u^2-v^2)^2`, contradicting that irreducibility.

Use `A=Z_(N)={a/b in Q: gcd(b,N)=1}` and its reduction to `Z/NZ`.
For a reduced `tau=m/n`, being a unit of A means **both** m and n are
coprime to N. For reduced D the same rule applies. These conditions, with
2 invertible, put H,k,h,s_2 in A and justify every displayed reduction.
Integer division before reduction is allowed only after exact cancellation;
an attempted modular inverse of a nonunit is not. A proper gcd is a factor.
Skipping full gcds is a permissible failure rule, not evidence of coverage.
Some nonunit raw denominators can cancel in other constructions; this report
does not exclude those constructions by imposing W005's stricter chart.

Let `Delta_i=s_i^2-4*t^2`, with `s_1=s`. The exact cheap tests are:

- `f_2` is irreducible over Q iff Delta_2 is not a rational square, including
  zero among squares.
- Once both quadratics are irreducible, their fields are distinct iff
  `Delta_1*Delta_2` is not a rational square. Unequal traces alone do not
  establish this. Equivalently test `Delta_2/Delta_1` for a square.

These are rational square tests on reduced numerators and denominators;
squarefree factorization is unnecessary. The trace congruence implies
`Delta_2=9R^2 mod N`, so a compatible trace is separable, but its rational
discriminant can still be a nonzero square. No supply of irreducible, distinct
fields follows. Positivity is unnecessary for the identity or explicit-root
reduction. Any later use of real-positive-field arguments needs its own check.

For inputs and rational tau with maximum numerator/denominator bit length B,
the constant-degree expressions, gcds, rational square tests and exact
verification take `poly(B+log N)` bit work. A bounded number of rational
operations here has O(B+log N)-bit intermediate values. Finding tau, growing
lift heights and rejections are additional costs.

## 3. The modular residual and the actual unit domain

Writing `F=-(c+2*t*H*k)`, direct expansion gives

    4*tau^2*(F-s*D)
      = -(2*t+s)*tau^4
        +(2*s^2-4*u^2*v^2-4*t^2)*tau^2+(2*t-s)*d^2.

For `t=2R`, `s=5R mod N`, this is the negative of

    E(tau) = (tau^2-R)*(9R*tau^2-d^2).                (7)

The coefficient check uses `d^2=s^2-4*u^2*v^2`: the middle coefficient
becomes `d^2+9R^2`. Since `4*tau^2*D` is a unit, (7) vanishes iff
`s_2=s mod N`. Thus the proposed quartic is exactly correct on the stated
domain, including prime powers.

Write `g=v^2-R`, `g_4=v^2-4R`. The separation identity is a congruence,

    d^2-9R^2 = 4*g*g_4 mod N,                         (8)

not generally an equality of the lifted integers. In fact the exact difference
between its two sides is `(s-5R)*(s+5R-4*v^2)`. This is one notation
correction to make explicit in the parent note.

There is a useful stronger domain fact: **compatible unit tau and unit D
already force both g and g_4 to be units.** If a prime p dividing N divided
`g*g_4`, (8) would give `d^2=9R^2 mod p`; (7) would then force
`tau^2=R mod p`. Substitution into D gives

    D = g*g_4/R = 0 mod p,

contrary to its unit requirement. Thus the extra g and g_4 checks are useful
early checks but redundant after full compatibility and the unit-D test.
No squarefree hypothesis is involved.

For unit g the displayed image is

    y = R*(3*tau^2+d)/(2*tau*g),
    y^2-R = R*E(tau)/(4*tau^2*g^2) mod N.             (9)

This last identity follows from `d+3R=2g mod N`. In particular a compatible
parameter already gives a modular root **before any rational lift, field
irreducibility test, field distinctness test or square-root computation**.
Those field tests are needed to certify the proposed field construction;
they are not needed to extract this modular root.

## 4. Complete branch description, including repeated primes

On the clean domain `d*g*g_4` a unit, the factors in (7) cannot both vanish
modulo any p dividing N. If their product is zero modulo `p^e`, one is a unit
there, forcing the other to vanish modulo the **whole** `p^e`. The branches are

    I:   tau^2=R,          y=tau,       D=g*g_4/R;
    II: 9R*tau^2=d^2,     y=d/(3*tau), D=g*g_4/(9R).   (10)

There are exactly four simple local parameter roots: two signs in each
branch. Their derivatives are units, so there are no additional nilpotent
root choices at repeated primes. If d is nonunit, valid unit parameters are
still separated by the preceding section; at primes dividing d only branch I
is possible. Unit d is needed for the uniform four-root count, not for every
instance of separation or extraction.

An explicit normal form makes the information content precise. For
`r=omega(N)`, define, without knowing the factorization,

    e = (9R*tau^2-d^2)/(9R^2-d^2) mod N.              (11)

The denominator is a unit by (8). At each prime power, e is 1 in branch I
and 0 in branch II. Thus `e^2=e`, and

    tau = e*y+(1-e)*d/(3*y).                          (12)

Conversely every root `y^2=R` and every idempotent e give, by (12), a unit
parameter solving (7), with unit D and with (9) returning that same y.
The four local values are distinct because (8) is a unit. Hence this is a
bijection

    {compatible parameter residues}
      <-> {roots of R} x {idempotents modulo N}.

There are `4^r` residues, partitioned into `2^r` parameters for each root.
A nontrivial e gives a proper gcd with N. Equivalently,
`gcd(tau^2-R,N)` is the product of exactly the full prime powers of type I,
so mixed branch types immediately split N. This is a constructive CRT
description for proof, not a use of unknown CRT factors by the algorithm.

For example, drawing independent uniform parameter residues has exact full
compatibility probability `4^r/N`, or `4^r/phi(N)` if conditioned on units.
These counts do not survive arbitrary field filters without adjustment.
Uniform draws are a paid search with mean `N/4^r` draws to a congruence hit;
cheap arithmetic per draw does not make that acquisition polynomial.

There is no further localized root chart missing on this clean domain for
the fixed packet and norm `t^2`. Suppose an irreducible compatible f_2 has
an ordinary square root `z=h+k*alpha_2`. Since alpha_2 and z are integral
over A, their rational traces `T=Tr(z)`, `U=Tr(alpha_2*z)` lie in A.
The unit discriminant gives

    k=(2*U-s_2*T)/Delta_2,    h=(T-s_2*k)/2 in A.

Hence `H=h/t` lies in A. Unit d and `(H+k)*(H-k)=d` force `tau=H+k`
to be a unit. The coefficient equations give (7) even before assuming
unit D; the two separated cases (10) then force D to be a unit. Thus this
ordinary square is in the reviewed parameter chart. This statement is
specific to the clean domain, compatible trace, fixed packet and fixed norm.

## 5. All signs and embeddings relevant to the displayed root

For either global choice `tau=x` or `tau=d/(3x) mod N`, (10) gives `y=x`.
Negation gives `y=-x`. Lift changes preserving these residues cannot alter
this conclusion, even if their rejection/acceptance pattern depends on x.
Selecting a different branch independently at prime powers entails a
nontrivial idempotent, which already gives a factor. Changing relative root
signs entails a nontrivial square root of unity relative to x, likewise a
factor. Neither operation is free randomization.

For irreducible f_2 the packet is nonzero: neither its nonzero constant or
linear factors can vanish at the irrational alpha_2. Therefore its only
field square roots are `±(h+k*alpha_2)`. A different basis, norm sign in a
square-root formula, real-embedding convention or exact cancellation in a
different expression cannot introduce additional roots of this same element.

Conjugation deserves a separate calculation: it changes the packet element,
so the preceding two-root argument alone would not address it. The other
global modular evaluation is `alpha_2 -> 4R`, with

    Q(4R) = 4R*g_4^2,
    y_4 = (h+4R*k)/(2*g_4)
        = R*(3*tau^2-d)/(2*tau*g_4).

Substitution in (10) gives `y_4=-y` in branch I and `y_4=y` in branch II,
or globally

    y_4 = (1-2e)*y.                                  (13)

Thus conjugation also returns only `±x` for either global construction.
In the mixed case comparing these two roots detects precisely the factor
already exposed by (11). A general modular image beta of alpha_2 satisfies
`(beta-R)*(beta-4R)=0`; their difference `3R` is a unit. Any image mixing
these evaluations over prime powers itself gives the proper factor
`gcd(beta-R,N)`. It is not an extra unspecified choice of embedding.

This settles the sign/embedding ambiguity of the stated displayed-root
computation. It does **not** settle every computation on fields chosen with x.
In particular these inexpensive, different tests can be retained before
rejecting a candidate, without any claimed positive success probability:

- If `Delta_2=q^2` in Q, its reduced root q lies in A and is a unit.
  Then `q/(3R)` is a square root of unity modulo N. Its gcds against ±1 can
  split N. Equivalently a rational root of f_2 may mix R and 4R locally.
- If `Delta_2/Delta_1=q^2`, q again is a unit in A and `q^2=1 mod N`.
  A nontrivial such q gives a factor, despite failing field distinctness.
- An exact rational square `s_2-2t=w^2` returns the root w of R; a square
  `s_2+2t=w^2` returns w/3. These test a different radicand from Q(alpha_2).
  They are not alternative signs of its displayed root.

Their square roots have valid reductions because their squares are units of
A, so the reduced rational roots have neither numerator nor denominator
divisible by a prime of N. Their helpful residue patterns and acquisition
frequency remain unproved. No claim that they always escape correlation, or
that they never do, follows from the two-root argument. Likewise extending
to cancelled-denominator charts or other packets requires another analysis.

## 6. A paid certificate filter, with an actual supply bound

The blinded sampler's review establishes uniformity on
`T_R={(u,v):u^2+v^2=5R mod N}` conditional on its certificate branch, and
independence from the outer root conditional on N,R. It grants only
N,R,u,v and fresh independent RNG to the inner routine. Filters of these
inputs retain root-choice independence, though surviving certificates need
not retain the original unconditioned law. Using x or reconstructing the
accepted rotation tape in the trace selector violates that interface.

One limited acquisition question *can* be paid now. Test gcds of d, g and
g_4 before lifting fields. Return proper factors. A full gcd of g returns
the root v, and a full gcd of g_4 returns v/2; verify either. A full gcd of d
can be a rejection. The remaining branch has precisely the clean unit domain.

Here is its exact mass under the specified uniform certificate law. For
each `p^a || N`, put `chi_p=(-1|p)` and `eta_p=1` if `(10|p)=1`, otherwise 0.
There are `p-chi_p` conic points modulo p. Exactly four have `v^2=R`, four
have `v^2=4R`, and `4*eta_p` have `u^2=v^2=5R/2`. These sets are disjoint
because `p` is not 2,3,5. Every point has `p^(a-1)` conic lifts, as at least
one partial derivative is a unit. CRT therefore gives conditional unit mass

    rho_N = product_(p|N) (1-(8+4*eta_p)/(p-chi_p)).    (14)

Without extra preprocessing this mass may be zero; it was right not to
assume it. After also trial-dividing by the fixed primes 7,11,13, all remaining
primes are at least 17. Order them `p_1<...<p_r`, so `p_j>=j+16`. Then

    rho_N >= product_j (p_j-13)/(p_j-1)
           >= product_(j=1)^r (j+3)/(j+15)
            = product_(k=4)^15 k/(r+k)
           >= (r+1)^(-12) >= (n+1)^(-12),

where `n=bit_length(N)`. This deliberately loose polynomial bound uses no
factorization in the algorithm; the primes appear only in its proof.

To include sampler failures, use its reviewed capped routine. Its certificate
probability is C_B and its early-factor probability is F_B, with
`C_B+F_B >= 1-exp(-(n+1))`. One filtered call has factor-or-clean-certificate
probability at least `F_B+C_B*rho_N >= rho_N/2`. Thus at most
`2*(n+1)^12` calls in expectation suffice; a cap of
`ceil(2*(n+1)^12*log(1/epsilon))` gives failure at most epsilon.
With the review's coarse O(n^6) sampler bound this is
`O(n^18*log(1/epsilon))` capped bit work, plus polynomial gcd overhead, with
fresh tapes and all cap failures charged. Early roots only improve this bound.
This proves supply of the unit-filtered **certificate**, not of tau or of an
irreducible distinct second field. It does not solve the remaining constraint.

## 7. Substantive changed computation: seek a local hit in a block product

The immediate simplification is to run (7), gcd extraction and (9) before
building any field. A more substantial change is to stop demanding a full
compatible trace: a zero at just one prime can already give a factor. The
following explicit computation uses N,R alone and therefore respects the
strict interface without using the certificate at all.

Choose a block length B, a number K of blocks, and construct over `Z/NZ`

    P_B(X) = product_(j=0)^(B-1) ((X+j)^2-R).

Use a subproduct tree: leaves are the displayed quadratics and each parent
is the product of its two children modulo N. Build the monic evaluation tree
with leaves `X-i*B`, `0<=i<K`, and propagate polynomial remainders to obtain
`P_B(i*B)`. This does not divide by differences between evaluation points;
monic polynomial division works over the composite coefficient ring.

Test the K resulting gcds with N. A proper gcd is a factor. At the first full
gcd, scan that single block's B leaves and test `gcd((i*B+j)^2-R,N)`.
Some leaf has a nonunit gcd. A proper gcd splits N; a full gcd returns the
verified unit root `y=i*B+j mod N`. If all block gcds are 1, return FAILURE.
This includes products that become divisible by p^a through several leaves;
they are not incorrectly treated as individual compatible parameters.

With ordinary fast multiplication and monic remainder trees, construction and
evaluation cost `O(M_N(B+K)*log(B+K))` bit work, where M_N(d) bounds degree-d
polynomial multiplication modulo N. Add `(B+K)*poly(n+log(BK+1))` for all
gcds and the one-block scan. Integer packing and fast integer multiplication
give `M_N(d)=tilde O(d*(n+log(d+1)))`; working storage for the literal trees
is `O((B+K)*(n+log(B+K+1))*log(B+K+1))` bits. These are real construction,
memory and recovery costs, not a unit-cost product oracle.

For an explicit coverage and success law, take
`B=K=ceil(N^(1/4))`. The interval of `B^2` consecutive integers includes
a representative of a root of R modulo the smallest prime divisor
`p<=sqrt(N)`, so a nonunit block is guaranteed. The procedure returns a
factor or a root. Conditional on a root return, the fresh uniform outer x
is still uniform on its `2^r` roots given R and the entire inner transcript.
Hence its useful outer gcd probability is exactly `1-2^(1-r)`.
For r>=2, each unit outer trial succeeds with probability at least 1/2.
Composite prime powers can instead be handled by paid polynomial perfect-power
testing. Unit sampling, retries, primality termination and recursive splits
are also charged. The resulting coarse complete expected envelope is only
`N^(1/4)*poly(log N)`, with exponential-in-n tree storage in this realization.

This is a concrete replacement for a quartic-parameter scan, with coverage
and costs; it is **not a new factoring bound**. The block product/multipoint
mechanism is established prior art. The primary
[Bostan–Gaudry–Schost paper, introduction pp.3–4 and factorization discussion](https://cs.uwaterloo.ca/~eschost/publications/pollard.pdf)
explicitly describes Strassen's consecutive-product blocks and subproduct-tree
evaluation, and proves its own stronger deterministic factoring implementation.
Our quadratic-leaf variant above has been derived here; that paper is not
being cited for a useful W005 packet law. No novelty conclusion follows from
this bounded source check.

## 8. Disposition and next decisive gate

Accept the exact generator, quartic factorization and displayed-root failure
for the two outer-x global branches. Complete the parent statement by making
(8) a congruence, specifying rational-square field tests, distinguishing the
unit-d four-root count, and including the conjugation calculation (13).
The stronger normal form (11)–(12) leaves no overlooked sign or field-basis
choice within that extraction. It exposes exactly a root and an idempotent.

Retain the direct discriminant/gcd branches and the paid unit-certificate
filter as possible computation changes; neither grants useful field mass.
The block-product procedure supplies a fully priced direct-factor comparator,
not a reason to run a numerical screen. To go beyond it, the next proposal
must specify a different product representation, update or evaluation schedule
and prove enough local hits at a smaller total bit cost, or give a different
paid root/parameter acquisition law. Random lifts, global branch swaps,
field-square-root sign changes and the label “quartic” do not meet that gate.
No experiment or implementation is selected by this review.
