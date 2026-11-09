# W012 square-selector review — independent round D

2026-10-08. **Verdict: accept formulas (1)–(6) and the specified selector,
with the domain, sampling-model and comparison qualifications below. Verified
factoring complexity improvement: NONE.** The support-query set has degree
three, which does not invalidate fixed-dimension convex integer optimization.
The submitted continuation supplies an efficient way to draw an index from a
precise distribution, not a useful-relation supply theorem or a factoring bound.

This is the separately scoped continuation review, not a repeat of completed
rounds A/B/C. The original W012 brief and square-coordinate continuation were
copied before analysis at 2026-10-08T23:14:27Z. The required project instructions
and specification were read and frozen. STATE was read for context only; the
explicit round-D assignment controls this finite review. No delegation,
parameter sweep, candidate performance experiment, package installation,
publication, commit, shared solver edit, Lean edit, registry edit, STATE edit,
or parent-proposal edit was performed. All new files use the exclusive
`research/findings/W012-square-selector-review*` prefix.

The principal qualifications are: require integer `B>=3` for the sampler;
sample only interior indices; distinguish uniform slope from uniform angle;
charge rejection sampling as expected work; and read (6) as its displayed
multiplicative bounds, not `1±epsilon`. A telescoping argument below also
proves a uniform constant upper amplification bound throughout (4), where
the displayed upper bound in (6) alone can diverge as epsilon approaches one.
Neither comparison assumes that Q has an exact efficient implementation.

**Formulas (1) and (2): accepted, including strict rounding.** Let integers
`N>1`, `B>=1`, and `1<=v<=B` be given. A particularly simple exact implementation is

    t_v = isqrt((N-1)//v) + 1.

Indeed `v*(t_v-1)^2<N<=v*t_v^2`; the strict lower inequality explains the
`N-1`. This formula needs no rational or floating-point square root. Taking
the ceiling of `sqrt(N//v)` can underestimate (`N=19,v=2`), while always adding
one to `isqrt(N//v)` can overestimate (`N=18,v=2`).

Put `h_v=sqrt(N/v)` and `e_v=t_v-h_v`. Then `0<=e_v<1`, including `e_v=0`
when the ratio is an integer square. Direct expansion gives

    (v*t_v)^2 - v*r_v = v*N,
    r_v = 2*sqrt(N*v)*e_v + v*e_v^2,
    0 <= r_v < 2*sqrt(N*v)+v.

Thus both formulas hold for every permitted v, not only in regime (4).
In this note B is an integer cutoff. A real-valued proposed cutoff must first
be converted to its intended integer cutoff.

A relation requires an exact factorization certificate for `v*r_v`, not just
a small residual. Using every prime up to B includes every prime dividing v;
it does not make generating that base or factoring v free. A QS base restricted
to quadratic residues of N cannot simply be substituted for this full base.
In particular, v can introduce other prime columns. Check proper gcds with N
before inversions or unit arguments. Checking `gcd(v*t_v,N)` catches nonunits
on the known-square side; a prime of N dividing r_v must also divide `v*t_v`.
Treat `r_v=0` separately: zero has no finite prime-exponent vector. With
`v<N`, a zero residual either exposes a proper divisor v or, when v=1, is
the ordinary square case. Outside that restriction, `v=N,t=1` is only a
trivial zero relation. Even inputs and perfect powers need their usual paid
handling in an all-composite factoring procedure.

**The convex query: accepted with degree three and actual coefficient sizes.**
Let `T=ceil(sqrt(N))`. The set

    C = {(t,v): 1<=t<=T, 1<=v<=B, v*t^2>=N}

is compact, nonempty, and convex. On `t>0`, the function `N/t^2` has second
derivative `6N/t^4>0`, so the nonlinear condition is its epigraph in v.
Equivalently it is the epigraph `t>=sqrt(N/v)` on v>0. For each integer v,
the smallest feasible integer t is exactly t_v, and is at most T. Positive
a in `a*t+b*v` forces this choice at any optimizing v.

For integral positive a,b, add `z=a*t+b*v` and minimize the integer coordinate
z. The resulting convex semialgebraic set is in dimension three, has degree
three, and uses five inequalities and one affine equality. Expressing each
nonstrict inequality with `<,>,=` uses at most eleven atomic predicates.
Rational objectives can be cleared of denominators, with their bit lengths
charged. The coefficient-length bound is

    ell = O(bitlen(N)+bitlen(B)+bitlen(a)+bitlen(b)).

Khachiyan–Porkolab Theorem 1.2 applies to a convex solution set described by a
real formula; it does not require the polynomial `N-v*t^2` itself to be convex.
With fixed dimension, degree and formula size it gives a polynomial bound
in ell. This checks the necessary change from degree two to three against
the primary theorem, using the frozen round-A primary text, printed p. 208;
it does not redo that round's broader audit. No optimizer implementation is
claimed. [Khachiyan–Porkolab, primary publisher PDF](https://link.springer.com/content/pdf/10.1007/PL00009496.pdf).

Minimizing the residual is a different problem. For example, at N=36 the
points `(v,t)=(1,6),(4,3)` both have residual zero; their midpoint has residual
`117/8>0`. Thus even the zero-residual sublevel within the convex query box
need not be convex. Introducing an objective coordinate equal to `v*t^2-N`
does not preserve the convexity required by the theorem. This is only an
applicability obstruction, not a lower bound for arbitrary residual algorithms.

**Formulas (3) and (4): accepted.** For `2<=v<=B-1`, twice integrating the
second derivative gives the exact triangular-kernel identity

    w_v^0 = integral[-1,1] (1-|s|)*h''(v+s) ds,
    h''(x) = (3/4)*sqrt(N)*x^(-5/2).

The kernel is nonnegative with integral one. Consequently

    w_v^0 >= (3/4)*sqrt(N)/(v+1)^(5/2) > 0,
    w_v-w_v^0 = e_(v-1)-2*e_v+e_(v+1) in (-2,2).

The rounding interval is open: each e lies in `[0,1)`. The convenient global
lower bound using B+1 is conservative (interior indices have `v+1<=B`), but
valid. Condition (4) therefore implies `w_v>0`, hence positive integer w_v
and strict discrete convexity. It can be tested without real arithmetic as

    9*N > 64*(B+1)^5.

It is sufficient, not necessary. It implies `B=O(N^(1/5))`; `B=N^o(1)`
satisfies it eventually, with epsilon tending to zero. The small-B guard and
integer comparison must actually be checked for finite inputs.

The condition cannot simply be discarded. The fixed example `N=15,B=5`
has `t=(4,3,3,2,2)` and `w_3=-1`. At the half-integer slope `lambda=1/2`,
indices 2 and 4 tie for the global minimum. Thus both monotone binary search
and the no-ties conclusion rely on the strict-convexity hypothesis, not on
the mere integrality of ordinates.

**Formula (5): accepted, with exact support and endpoint conventions.**
Assume integer `B>=3` and (4). Define g on `2,...,B`. Since t is nonincreasing,
`g_v>=0`; since `g_v-g_(v+1)=w_v>0`, g is strictly decreasing. For
`F_lambda(v)=t_v+lambda*v`, the increment from `v-1` to v is `lambda-g_v`.
An interior v is therefore minimizing exactly when

    g_(v+1) <= lambda <= g_v.

These local inequalities are globally sufficient because the increments
are strictly increasing. Strict inequalities give the unique minimizing
index. At an equality, the corresponding adjacent vertices tie. All t above
t_v have strictly higher objective, so this also describes optimization over
the whole integer query set.

Let `W=g_2-g_B=sum_(v=2)^(B-1) w_v>0`. Uniformly choose an integer
`J in {g_B,...,g_2-1}` and use the integer objective

    2*t + (2*J+1)*v.

This is precisely the submitted half-integer slope; it has positive integer
coefficients and no precision cost. The J values yielding v are exactly

    {g_(v+1),...,g_v-1},

whose cardinality is w_v. These disjoint sets partition the W allowed J's,
proving `P(v)=w_v/W`. This is an exact law, without fractional-part randomness.

Index 1 minimizes above g_2 and index B below g_B, with adjacent ties at
the transition slopes themselves. The sampled interval deliberately omits
both endpoints. It is not a law on all `1,...,B`. For B=3 it returns v=2
deterministically; for B=2 there is no interior and W=0; for B=1 g is undefined.
Changing endpoint inclusion changes the law. Uniform half-integer slopes on
this finite interval are also not uniform Euclidean normal angles or uniformly
chosen integer coefficient pairs. The phrase normal-direction sampling here
must retain the specific slope law in the proposal.

**Integer sampling and binary-search cost: accepted as expected polynomial
bit cost, with an explicit implementation.** Compute `g_2,g_B,W` using at
most four ceiling-root evaluations. If W=1 choose J=g_B. Otherwise set
`k=ceil(log2 W)=(W-1).bit_length()`, draw k independent unbiased bits to form
U, reject U>=W, and return `J=g_B+U` on acceptance. Each allowed J has exactly
the same probability. Acceptance is `W/2^k>1/2` (or one when W is a power of
two); expected trials are `2^k/W<2`. Expected random bits are below 2k.
Because `W<=g_2<=ceil(sqrt(N))`, k is O(n) for `n=bitlen(N)`.

Given an accepted J, find the last index k with `g_k>=J+1`, using this
integer-only bisection:

    lo=2; hi=B                 # g_lo>=J+1, g_hi<=J
    while hi-lo>1:
        mid=(lo+hi)//2
        if g_mid>=J+1: lo=mid
        else:          hi=mid
    return lo

The invariants hold at initialization from the allowed J range. Each update
preserves them and decreases the interval, and termination gives
`g_(lo+1)<=J<g_lo`, the exact desired bin. It uses at most
`ceil(log2(B-2))` probes when B>3, and none for B=3. A probe computes two
t values; caching is optional, not a hidden O(B) preprocessing table.

Under (4), all indices, t values, slopes and residual/product intermediates
have O(n) bits. With D(n) the cost of integer division and I(n) the cost of
integer square root, a draw costs

    O((1+log B)*(D(n)+I(n)+n)) expected bit operations,

including endpoint preparation and expected rejection work. Elementary
long division and digit-by-digit integer square root give the conservative
bound `O(n^2*(1+log B))`, hence O(n^3) here. O(n) working bits suffice when
values are recomputed rather than stored; retaining a probe cache costs
O(n log B) bits. Computing r and the square-side value and checking gcds adds
polynomial bit work. This prices drawing an index and forming its row, not
factoring its residual or collecting a useful dependency.

There is no worst-case finite rejection bound in this exact fair-bit sampler.
For the preregistered case `N=100001,B=4`, `t=(317,224,183,159)`,
`g=(93,41,24)`, and `P(2)=52/69`, `P(3)=17/69`. A sampler guaranteed to use at
most K fair bits can only have probabilities with denominator dividing 2^K;
it cannot produce this distribution exactly while always returning an index.
After R rejection attempts, one may instead report FAIL, of probability below
`2^(-R)`. Conditional on nonfailure, the original exact law is preserved;
forcing an ordinary output on failure perturbs it by at most that probability
in total variation. These distinctions matter under the repository's bounded
random-tape contract. The submission's explicit expected-bit wording is correct.

**Formula (6): accepted; its inference can be strengthened and scoped.** Put

    a_v=(v-1)^(-1/2)-2*v^(-1/2)+(v+1)^(-1/2),
    D_B=(1-1/sqrt(2))-((B-1)^(-1/2)-B^(-1/2)).

Then `w_v^0=sqrt(N)*a_v`, `W0=sqrt(N)*D_B`, and `Q(v)=a_v/D_B>0`.
Thus N cancels for a fixed B. If B itself depends on N, the support and
normalizer still vary with B; N-independence should not obscure that fact.
Q is a mathematical reference distribution; no exact efficient Q sampler is
assumed, constructed, or needed for the proof.

With the submitted epsilon, (3) and the curvature bound give

    |w_v/w_v^0-1| < epsilon,
    |W/W0-1| < epsilon.

Since `P(v)/Q(v)=(w_v/w_v^0)/(W/W0)`, division by these positive quantities
proves exactly the two bounds in (6). In particular, a safe relative-error
bound is `|P(v)/Q(v)-1|<=2*epsilon/(1-epsilon)`, not epsilon itself. Summing
`P(v)=Q(v)*(P(v)/Q(v))` over any subset proves the same probability bounds
without any independence assumptions. The empty set is handled directly,
without dividing zero by zero. The subset may depend arbitrarily on N,
including actual residual sizes or smoothness.

For epsilon bounded away from one, (6) directly rules out unbounded event
amplification relative to Q. In the full regime epsilon<1, that particular
upper bound alone is not uniform. The conclusion is nevertheless valid by
the sharper telescoping identity

    W-W0 = e_1-e_2-e_(B-1)+e_B,       |W-W0|<2.

Let `m=B-2`. For B>=4, m>=2 and (4) gives `W0>2m`. Also
`w_v/w_v^0<2`. Therefore

    P(v)/Q(v) < 2/(1-2/W0)
              < 2*m/(m-1) <= 4.

For B=3 both laws are the same point mass. Consequently the specified sampler
satisfies `P(E)<=4*Q(E)` for every interior event throughout (4), independently
of N and B. For the intended `B=N^o(1)` regime, (6) supplies the much stronger
uniform ratio `1+O(epsilon)` with epsilon tending to zero.

This is selection no-amplification over Q, not a universal impossibility result.
It supplies neither a bound on Q's useful-event mass nor an efficient
comparison algorithm drawing Q. It says nothing comparable about uniform
multiplier choice, events at v=1 or B, uniform angular sampling, adaptive
directions, another range, or a different law after filtering. In particular,
conditioning on unseen indices or smooth residuals changes the normalized
law and incurs the actual rejection/observation cost. The pointwise bound
also must not be multiplied across an unbounded number of draws and then
called a constant bound for an entire factoring run.

**Narrow primary-literature check.** Belabas's author-hosted course notes,
section 4.3.3, printed pp. 123–124, give
`F(x)=A*x^2+2*b*x+c`, `b^2-A*c=N`, and
`A*F(x)=(A*x+b)^2-N`. They choose coefficients to keep values small and
discuss changing polynomials and finding their roots modulo base primes.
These are established relation-generation ingredients. The extracted Algorithm
32 return line reads `A*x^2+b*x+c`, inconsistent with the preceding identity;
the algebra here uses the preceding `2*b*x` convention. No implementation is
copied from that line. [Belabas, section 4.3.3](https://www.math.u-bordeaux.fr/~kbelabas/teach/N1MA9W11/book.pdf).

Silverman's 1987 primary article, sections 2–5, discusses premultiplying by
a small k to improve small-prime quadratic-residue coverage, polynomial
coefficient choice, and the cost of recomputing roots across the factor base.
Printed p. 335 explicitly presents a modified Knuth–Schroeppel multiplier
score balancing prime-divisibility contributions against a multiplier-size
penalty. Thus choosing useful multipliers and small polynomial values is
already known machinery. The original article was read through an accessible
republished transcript; AMS PDF access failed and the institutional PDF mirror
returned 404. Its OCR damages some formulas, so this review does not certify
the score's exact numerical constants. The access failures and accessible
transcript are retained. [Silverman, DOI](https://doi.org/10.1090/S0025-5718-1987-0866119-8),
[accessible primary-article transcript](https://studyres.com/doc/24497791/s0025-5718-1987-0866119-8).

The following correspondence is this review's direct algebra, not a novelty
claim or a theorem attributed to those sources. For fixed v, define

    f_v(s)=v*s^2-N,       v*f_v(s)=(v*s)^2-v*N.

This is a square relation for the multiplied target vN with square-side
variable constrained to multiples of v; reduction modulo N gives (1).
After substituting `s=t_v+x`, its quadratic has coefficients
`A=v,b=v*t_v,c=r_v` and reduced discriminant `b^2-A*c=v*N`.
This is not literally the usual fixed-target MPQS parameter choice:
A shares a factor with the multiplied target, and the proposal draws one
boundary value per v rather than sieving an interval for each polynomial.
For an odd prime `p` not dividing vN, `f_v` has a root modulo p exactly when
the Legendre symbol `(v*N/p)=1`. This makes the connection to multiplier
selection explicit without claiming the new slope law equals the historical
score. If `p|v` and `p` does not divide N, p cannot divide r_v, although it
still contributes to the known v part of the relation.

These two sources suffice to reject novelty for square congruences, multiplier
selection in general, or using small polynomial values. They do not establish
whether the particular discrete-curvature sampler appeared previously. No
novelty claim for it follows from this deliberately narrow search. No historical
timings or heuristics are imported as guarantees for this construction.

**Complete-cost obligations still missing for factoring.** Choosing B and any
separate residual-smoothness cutoff must be uniform and paid. `B=N^o(1)` is
not the same as `B=poly(log N)`; explicitly generating all primes or a table
through B may already be superpolynomial in n. A changed coefficient-selection
rule must price every tried direction, arithmetic score, residual observation,
failure, preprocessing table, and coefficient bit length.

Given a draw, produce exact exponent data for v and r_v, or discard the row
with its work charged. A small residual or small norm envelope alone proves
no smoothness probability. If base primes are processed separately for each
draw, that is actual repeated work, not a free sieve over all multipliers.
Any proposed batching or polynomial-root sharing needs its own executable
algorithm and cost, including roots, buffers, scans and failed cofactors.
For `B=N^o(1)`, (2) is an `N^(1/2+o(1))` upper envelope; it is not a lower
bound preventing exceptional small residuals, and it is not a density theorem.

The raw sampler has only B-2 possible rows for a fixed N,B. Repeated v gives
the same t and r; it supplies no new row data. In the unit case, the dependency
consisting of a duplicate row twice has identical square sides modulo N and
is trivial. Therefore an accepted-row rate cannot substitute for a supply
bound on useful distinct relations or dependencies. With a history H, a
useful acquisition guarantee must bound the conditional chance of adding
useful information given H, and price the observations leading there.

For a retained subset S whose full prime-exponent sums are even, form

    X = product_(v in S) (v*t_v) mod N,
    Y = product_p p^((sum_(v in S) exponent_p(v*r_v))/2) mod N.

Then `X^2=Y^2 mod N`. The parity matrix needs all actual columns; this
construction's residuals are nonnegative, while extensions with signed
residuals must track sign too. Store exponent information sufficient to
assemble Y, not just parity bits. Modular products prevent unnecessary
unreduced-product growth; all matrix construction, memory, elimination,
dependency selection, modular exponentiation and gcd work still count.
More columns than available useful rows, failed rank assumptions, duplicate
rows and failed dependencies cannot be hidden by an idealized row count.

Finally check `gcd(X-Y,N)` and, if useful, `gcd(X+Y,N)` and verify proper
factors. A nonzero parity dependency need not yield a nontrivial square root
of one. No proper-factor success probability, independence law, or restart
bound is supplied. A complete expected-cost theorem must combine actual
per-attempt costs with a justified success law; repeated identically
distributed attempts with uniformly bounded expected cost C and success
probability at least rho would allow a C/rho bound, but those premises are
not established. A bounded-time theorem must separately charge capped
failures and its random-bit budget. Full factorization also requires the
ordinary preprocessing, primality decisions and recursive splits.

**Evidence and disposition.** The fixed preregistered certificate checks
passed 40/40; failed checks: zero. They verify ceiling traps, four bin boundary
queries, two excluded endpoint slopes, algebraic bin cardinalities, a
non-dyadic probability, B=3/B=2 behavior, the out-of-regime negative curvature
and half-integer tie, a nonconvex residual sublevel, and zero-residual handling.
No random or performance run was used. The general proof above, rather than
these finite checks, supports the accepted formulas. Only the exclusive
scratch certificate was executed; shared implementation/Lean checks were not
run because no shared implementation changed and this assignment restricts
writes to the review prefix.

Best supported full-work claim: exact drawing from P and forming its row
take expected `O(n^2*(1+log B))` bit operations in regime (4), using ordinary
unbiased bits and elementary arithmetic, excluding residual factorization
and relation processing. The general paid support query is polynomial in its
actual coefficient lengths. There is no proved factoring improvement and no
new end-to-end candidate supported by this sampler alone.

Disposition: **accept the mathematical selector; require the stated
qualifications; leave useful relation supply and factoring complexity
unestablished.** A materially different computation that could change this
conclusion would be a specified batched arithmetic selector or adaptive rule
with a proved useful-distinct-row supply bound and complete observation cost.
The next decisive task would be that proof and an exact comparison to existing
multiplier/polynomial selection, not a favorable-parameter benchmark. This
finite review does not close the parent's other support-based or non-relation
research routes.

The original-brief SHA-256 is
`879240eed4d6900cb2f26a853d3f6b43bfcaf73ced4efbaa41c80bb325a2242a`;
the frozen-continuation SHA-256 is
`079d5b809661fbc4d49b7140b97393a336ceff1d1dbb618447bd42bf9503c555`.
The preregistration, certificate source/result, input manifest, primary-source
copies/transcript, access failures and source manifest are adjacent files with
this report's prefix. `W012-square-selector-review-delivery-manifest.json`
and `W012-square-selector-review-delivery.sha256` inventory their exact bytes
and hashes, including the final report; the checksum list excludes itself.
