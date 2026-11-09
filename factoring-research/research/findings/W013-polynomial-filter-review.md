# W013 Card B independent polynomial-filter review

2026-10-08 UTC. **Verified complete classical factoring improvement: NONE.**

**Disposition:** accept the exact filter, the coefficientwise obstruction (4),
and the cancellation-tolerant degree-four obstruction (5)–(7), with every stated
constant unchanged. The weighted-Dirichlet calculation is a sufficient acquisition
budget, not a lower bound. Reject the proposed balanced width `H ≍ N^(1/3)` with
`q ≍ H` and bounded error for this uniform integer-coefficient quartic mechanism.
This is not a factoring lower bound and uses no W012 geometric obstruction.

Two useful review additions are proved below. First, inequality (7) does not need
the small-error condition in (5); that condition is needed for the intermediate
conclusion `a2=0`, not for the final error lower bound. Second, one can replace
modular root enumeration by exact integer roots of `(X+h)(A(h)-e)-qN`. This removes
the prime-modulus and `q≥H` requirements from constant-candidate extraction when
`E` is bounded. It does not provide the missing approximants or reopen the rejected
width. Its linear special case has close, explicit prior art in Hiary.

## Review object and evidence

The original assignment is preserved in
[original-brief.txt](W013-polynomial-filter-review-evidence/original-brief.txt).
[input-manifest.json](W013-polynomial-filter-review-evidence/input-manifest.json)
records SHA-256 and byte size for the frozen guidance, contract, README, W013,
W012 disposition, and STATE. The frozen W013 hash is
`f20282daba4ebd972246328c4641d80ac5472c5173065c48e1b52acc43bfb2f9`.
The frozen Card B includes the final degree-four section. Card A is excluded.
STATE was read for operating context, not used as a mathematical premise. W012
was read only to preserve the boundary between its covering claim and this proof.

The proof below is mathematical review, not a Lean theorem. One
[preregistered certificate](W013-polynomial-filter-review-evidence/preregistration.md)
checks symbolic identities and three fixed scope examples using standard-library
exact arithmetic. Its [script](W013-polynomial-filter-review-evidence/certificate.py)
and [output](W013-polynomial-filter-review-evidence/certificate-output.json) are
retained. All **10 checks passed**, no checks failed, and stderr is empty. Script
SHA-256: `6d0e77f9cc8d443e6a2dfc36714485ed5ccf104d5cdadf426fae6beaac405220`.
Output SHA-256: `d87170432ade2ede081cf891cadf35cac20a9f266c6035649a1c0437a1b4b87f`.
No performance experiment, parameter search, prime sweep, depth sweep, replacement
instance, factoring run, recursive delegation, or shared solver/Lean edit occurred.

## 1. Divisibility, Taylor error, and rounding

Take integers `N>1`, `X≥2`, `H≥1`, `q≥1`, and `d≥0`. Offsets are integers
`0≤h<H`. For actual factor extraction also intersect the block with
`2≤X+h≤isqrt(N)`; a final truncated block uses its actual integer width.

Write `N=tx+r`, `0≤r<x`. If `r>0`, both `floor(N/x)` and
`floor((N-1)/x)` equal `t`; if `r=0`, the second is `t-1`. Thus the floor
difference is precisely the indicator of `x|N`. No summation algorithm follows
just from this identity.

Set `c_j=(-1)^j N/X^(j+1)` and `S_d(h)=Σ_(j=0)^d c_j h^j`. Telescoping gives

    (X+h) S_d(h) = N + (-1)^d N h^(d+1)/X^(d+1).

Since `X+h>0`, subtracting from `N/(X+h)` proves the exact signed remainder

    N/(X+h) - S_d(h)
      = (-1)^(d+1) N h^(d+1)/(X^(d+1)(X+h)).

This finite algebraic identity does not require `h<X`. In particular the
degree-four remainder is negative for `h>0`, and zero at `h=0`.

For integer coefficients `a_j` with `|q c_j-a_j|≤η_j`, `η_j≥0`, the triangle
inequality, `h≤H`, and `X+h≥X` imply

    |q N/(X+h) - A(h)|
      ≤ Σ η_j H^j + q N H^(d+1)/X^(d+2) = E.

Using `H` instead of `H-1` is deliberately conservative. The exponent of `X`
in the last denominator is `d+2`, as claimed. All these quantities may be exact
rationals. Computing an outward rational bound is required; a floating-point
underestimate is not a certificate. Nearest-integer rounding of coefficients
permits `η_j≤1/2`, including either tie choice, but alone gives a large weighted
error and does not establish the intended small `η_j`.

If `X+h|N`, write `N/(X+h)=t∈Z`, and define `e=A(h)-qt`. Then `e∈Z`,
`|e|≤E`, and `A(h)≡e (mod q)`. Consequently it suffices to enumerate

    e = -floor(E), ..., floor(E).

There is **no additional half-unit rounding allowance**: `e` itself is already
an integer. A rational certified upper bound for `E` must be rounded down exactly
when forming this target interval. Negative and positive targets are both needed.
This congruence is a necessary condition only. Exact division or gcd and the
nontrivial-factor check are required for every emitted candidate.

## 2. Modular roots and full extraction costs

Let `K=floor(E)` and `s=min(q,2K+1)`. The consecutive targets represent exactly
`s` distinct residues modulo `q`; deduplicate them before counting work. If `q`
is prime and the coefficient-reduced `A` has positive degree `r≤d`, each
`A-e` is a nonzero polynomial with at most `r` roots in the field. Their union
has at most `min(q,d s)` residues. Each residue lifts at most `ceil(H/q)` times
into `[0,H)`. Thus an upper bound on distinct candidate offsets is

    min(H, d s ceil(H/q)).

The root-count proof is the usual repeated factor theorem over a field; it is
not a bound on the cost of finding the roots. Exhaustive testing of all `q`
residues is a valid terminating root algorithm but costs `q` evaluations, which
would erase the proposed gain when `q≍H`. Any faster algorithm must be specified
and its deterministic or randomized guarantees and arithmetic costs included.

If `A` is constant modulo `q`, a target matching that constant makes `A-e`
identically zero and admits every residue. Other targets give no roots. The
fixed certificate includes the zero polynomial modulo 5, with all five roots.
The case `q=1` also admits every offset. Reducing coefficients can lower the
degree, so the degree check must occur after reduction.

For composite `q`, the field root bound fails even for monic polynomials:
`h²≡0 (mod 16)` has roots `0,4,8,12`. More generally `h²≡0 (mod p^k)` has
`p^floor(k/2)` roots. Squarefree CRT combinations can multiply the numbers of
roots, and a polynomial may vanish identically modulo some prime factors.
Factoring `q`, finding prime-power roots, handling singular lifts, CRT assembly,
and producing all interval lifts cannot be treated as free. A gcd of a coefficient
with `q` concerns the auxiliary modulus, not necessarily a divisor of `N`.

The claimed `O_d(1)` final tests therefore holds for the stated prime/nonconstant,
`q≥H`, bounded-`E` situation, conditional on correct root enumeration. It is not
an unconditional block time bound. Charge denominator/coefficient acquisition,
error certification, modulus construction and any certification/factorization,
target handling, roots, lifts, and final tests. No smoothness relation collection
is needed, but its absence does not pay those costs.

## 3. Coefficientwise short-denominator obstruction

Assume `X²≤N≤4X²`, `H≥2`, `d≥2`, `4q/X<1/2`, and
`|q c_2-a_2|≤H^(-2)`. Then

    0 < q c_2 = q N/X³ < 1/2,      H^(-2)≤1/4.

An integer within `1/4` of that open interval must be zero: a negative integer
is too far below it, and an integer at least one is more than `1/2` above it.
Hence `a_2=0` and

    q N H² ≤ X³,       q H² ≤ X.

If additionally `q≥H`, then `H³≤X`. The hypotheses are sufficient for the
forced zero; the proof does not assert that they are necessary or optimal.
It concerns the stipulated coefficientwise approximation gate. Cancellations
in a general uniform approximation are dealt with separately in Section 5.

## 4. Conditional scales and weighted Dirichlet budget

On a balanced block, `N≍X²`. If `q≍H`, the Taylor upper bound has scale
`H^(d+2)/X^d`. Bounded remainder therefore permits the *conditional* width

    H ≍ X^(d/(d+2)) ≍ N^(d/(2d+4)).

An interval of length comparable to `sqrt(N)` would then use about
`N^(1/(d+2))` blocks. For `d=4` these expressions are `H≍N^(1/3)` and
`N^(1/6)` blocks. This is the calculation of one error term, not proof that the
integer coefficients exist, that the modulus can be acquired, or that all smaller
factor ranges are covered at that total cost.

Here is the precise weighted pigeonhole calculation. For integer `H≥2`, partition
coordinate `j` of `[0,1)^d` into `H^j` half-open intervals, `1≤j≤d`. There are

    P = Π_(j=1)^d H^j = H^(d(d+1)/2)

boxes. Among the `P+1` vectors `({k c_1},...,{k c_d})`, `0≤k≤P`, two share a
box. Subtracting their indices produces `1≤q≤P` and integers `a_j` with
`|q c_j-a_j|<H^(-j)` for every `j≥1`. Choose `a_0` by nearest-integer rounding.
Then the coefficient contribution to `E` is at most `d+1/2`.

Substituting this upper budget `q≤H^S`, `S=d(d+1)/2`, into the Taylor bound
gives `O(H^(S+d+1)/X^d)`. Keeping this certified upper bound constant gives

    H = O(X^(d/(S+d+1)))
      = O(N^(d/((d+1)(d+2)))).

The corresponding balanced block-count exponent is
`1/2-d/((d+1)(d+2))`. For `d=1,2` it is `1/3`; for every integer `d≥3` it is
larger, since `d/((d+1)(d+2))<1/6` is equivalent to `(d-1)(d-2)>0`.

This proves a **sufficient worst-budget scale**, not a lower bound on denominators,
not the best scale obtainable from these correlated coefficients, and not an
algorithm time bound. The pigeonhole proof neither guarantees `q≥H` nor a prime
or smooth `q`. Multiplying a small `q` also multiplies its errors and does not fix
that omission for free. Explicitly generating all the pigeonhole points costs
up to `P` points; an efficient acquisition method needs its own guarantee. Using
the actual smaller `q`, or exploiting dependence among the `c_j`, can improve a
particular approximation. Nothing in the pigeonhole budget forbids that.

## 5. Complete proof of the cancellation-tolerant quartic theorem

Use integer `N,X,H,q` with

    X²≤N≤4X²,      10≤H≤X,      1≤q<X/240.

Let `A(h)=Σ_(j=0)^4 a_j h^j`, `a_j∈Z` (zero leading coefficients allowed), and
suppose `|A(h)-qN/(X+h)|≤E` on every integer `0≤h<H`, with real `E≥0`.
Define `m=floor((H-1)/4)`.

**Nodes.** We have `m≥2` and `4m≤H-1`. Thus `0,m,2m,3m,4m` are five distinct
integer offsets covered by the hypothesis. Also

    m ≥ (H-5)/4 ≥ H/8,        m ≤ (H-1)/4 < X/4 ≤ X.

The weaker `m≤X` is sufficient for the parent's constants. Real values between
nodes, negative offsets, and `h=H` are not invoked.

**Exact interpolation.** Set `F(h)=qN/(X+h)`. For distinct nodes `t_0,...,t_k`,
its divided difference is

    F[t_0,...,t_k] = (-1)^k qN / Π_(j=0)^k (X+t_j).

For `k=0` this is the definition. The divided-difference recursion subtracts
the two previous expressions and divides by `t_k-t_0`; the numerator difference
is `(X+t_0)-(X+t_k)=-(t_k-t_0)`, proving the induction and the sign. Therefore
the unique degree-at-most-four interpolant is

    I(h) = Σ_(k=0)^4 (-1)^k qN Π_(j=0)^(k-1)(h-jm)
                                      / Π_(j=0)^k(X+jm).

Equivalently, with `D=Π_(j=0)^4(X+jm)`, clearing denominators gives

    (X+h) I(h) = qN [1 + Π_(j=0)^4(h-jm)/D].

The certificate verifies the latter polynomial identity symbolically. It implies
the required nodal values directly; no Taylor truncation bound is used here.

**Quadratic coefficient.** The first two terms have no `h²` coefficient. In the
remaining falling products the coefficients are `1`, `-3m`, and `11m²`;
multiplication by `(-1)^k` changes the middle contribution to `+3m`. Thus

    alpha = qN/[X(X+m)(X+2m)]
          + 3m qN/[X(X+m)(X+2m)(X+3m)]
          + 11m² qN/D
          = qN (X²+10Xm+35m²)/D > 0.

The compact last expression is also certified symbolically. Since `m≤X`,
`X+m≤2X` and `X+2m≤3X`; using `N≥X²` proves

    alpha ≥ qN/[X(X+m)(X+2m)] ≥ q/(6X).

Each denominator in the three-term expression is at least the appropriate power
of `X`. Again using `m≤X`, then `N≤4X²`, gives

    alpha ≤ (1+3+11)qN/X³ = 15qN/X³ ≤ 60q/X < 1/4.

This verifies both sides of (6), including the strict last inequality.

**Error interpolation.** For the Lagrange basis at `z=0,1,2,3,4`, the `z²`
coefficients are, in order,

    35/24,   -13/3,   19/4,   -7/3,   11/24.

Their absolute sum is `(35+104+114+56+11)/24=320/24=40/3`. Substituting
`z=h/m` makes each `h²` coefficient `1/m²` times the displayed value. Both
`A` and `I` have degree at most four, so interpolation of their five nodal
differences is exact. Each difference has absolute value at most `E`. Hence

    |a_2-alpha| ≤ (40/3) E/m².                         (R1)

Under the additional hypothesis `(40/3)E/m²<1/4`, (R1) and `0<alpha<1/4`
place `a_2` strictly between `-1/4` and `1/2`. Since `a_2∈Z`, necessarily
`a_2=0`. Combining (R1) with the lower bound on `alpha` yields

    q/(6X) ≤ alpha ≤ (40/3)E/m²,
    q m² ≤ 80 E X,
    q H² ≤ 64·80 E X = 5120 E X.                     (R2)

This proves (5)–(7) exactly as written. In particular `E=0` is impossible under
these hypotheses. There is no sign error, missing factor of `m`, off-by-one node,
or exception at the permitted minimum width. No numerical counterexample search
is warranted for a theorem proved this way.

**Strengthening, without altering the reviewed theorem.** Because
`0<alpha<1/4<1/2`, every integer `a_2` satisfies `|a_2-alpha|≥alpha`: zero is
the nearest integer. Apply this directly to (R1). It gives (R2) for **every
`E≥0`**, without `(40/3)E/m²<1/4`. Large errors need not force `a_2=0`, but
they still satisfy the same error lower bound.

**Consequences.** If `q≥H` and `E=O(1)`, then `H³≤5120EX`, so
`H=O(X^(1/3))=O(N^(1/6))` on balanced blocks. The proposed `H≍N^(1/3)` is
therefore excluded. Even without `q≥H`, the positive integer condition `q≥1`
gives `H=O(X^(1/2))` for bounded error throughout `q<X/240`, also too small
for `H≍X^(2/3)`.

For the literal modular filter there is a stronger diagnostic: if `H²≥2560X`,
(R2) forces `E≥q/2`. Its consecutive targets then cover every residue modulo
`q`, so every offset passes the modular filter, independent of root algorithms.
The proposed `H≍X^(2/3)` eventually has this property. This conclusion uses the
extension of (R2) just proved, so there is no circular assumption that the error
remains small.

## 6. Scope and a better extraction primitive

The theorem concerns **one ordinary integer-coefficient polynomial of degree at
most four** that approximates the real value `qN/(X+h)` on all the stated integer
offsets. It does not assert a lower bound for factoring, early stopping, arbitrary
floor-sum methods, or general modular filters. In particular it does not cover:
`q≥X/240`; modular proximity with changing integer multiples of `q`; a changing
denominator; several approximants sharing computations; growing degree; or
approximations only on an adaptively selected subset of offsets. It supplies no
cost theorem for those alternatives.

Integer-valued polynomials are also distinct from integer-coefficient polynomials:
`h(h-1)/2` is integral at all integer `h` but has `a_2=1/2`. Thus the specific
integrality step cannot simply be copied into that setting. The certificate
checks its values only at the five preregistered nodes. This example is not a
counterexample satisfying the approximation hypotheses or a claimed speedup.

There is, however, an immediate extraction correction **inside** the uniform
approximation framework. For each integer `e∈[-K,K]`, form

    R_e(h) = (X+h)(A(h)-e) - qN.

Every divisor offset gives one such equation, by Section 1. Each `R_e` is an
integer polynomial of degree at most `d+1`, and it is not identically zero:
`R_e(-X)=-qN≠0`. It therefore has at most `d+1` integer roots. Find its integer
roots in `[0,H)`, then test divisibility of `N` exactly. The converse before that
test is not automatic, since `R_e(h)=0` only says `qN/(X+h)` is an integer;
factors introduced by `q` can create false candidates.

For fixed `d`, this gives at most `(d+1)(2K+1)` candidates, with no need for
prime `q`, factoring `q`, or `q≥H`. Notice that `e` and `e+q` give different
equations here; modular-target deduplication must not discard either equation.
When `E<1`, the sole equation is `R_0=0`. For degree one, `A=a-bh` gives

    -R_0(h) = (qN-aX) + (bX-a)h + b h²,

which makes the close connection to the interval method below explicit.

For completeness, fixed-degree integer-root finding here needs no factoring
oracle or unpriced analytic primitive. The following elementary recursion suffices
on a finite integer interval `[L,U]`:

1. For a constant polynomial, its sign on the interval is immediate.
2. For a nonconstant `P`, recursively partition `[L,U-1]` into consecutive runs
   on which `Delta P(t)=P(t+1)-P(t)` has a fixed sign (`-`, `0`, or `+`). Its degree
   is one less. If `L=U`, evaluate the single value instead.
3. On a run `[l,r]`, `P` is monotone on `[l,r+1]`. Exact integer binary searches
   locate the transitions between negative, zero, and positive values. Merge
   overlapping endpoints and adjacent runs of the same sign.

The recursion is correct by the difference identity. A nonzero degree-`D`
polynomial has at most `D` real roots, so its sign sequence at consecutive
integers has `O(D)` runs (a zero value can form its own run). Thus for fixed
degree the recursion uses `O_D(log(U-L+2))` exact evaluations, with constants
depending only on `D`; differences also have bounded degree. Zero-polynomial
subproblems are handled in step 1, while the top-level `R_e` is nonzero. A zero
run of the top-level polynomial contains at most `D` integers, so outputting its
integer roots costs only `O(D)`. Exact Horner evaluations and the difference
coefficients have polynomial bit cost in the input coefficient sizes and endpoint
bit lengths. This supplies a finite polynomial-bit extraction routine without
assuming modular root finding. It is a mathematical algorithm description, not
an implemented or timed solver in this review.

The correction saves unnecessary modular/lifting work; **it does not acquire
`A,q,E`**. Even a small `q` must be found with an error that permits useful blocks.
Section 5 still excludes the selected width throughout its short-denominator
regime. For unbounded `E`, explicitly processing every equation costs `2K+1`
root computations; writing their product explicitly has growing degree and is
not a free batching operation.

## 7. Bit sizes and complete-work obligations

Let `n=bit_length(N)` and retain the bit lengths of `q`, all `a_j`, and the
numerator/denominator of the rational error certificate as part of the input
size of a block routine. With fixed `d`, `X,H≤N`, and all those quantities of
polynomial magnitude in `N`, each scalar used here has `O_d(n)` bits. For example
`X^(d+1)` has `(d+1)log_2 X+O(1)` bits; the quartic interpolation denominator
has at most `5log_2(2X)+O(1)` bits because its nodes lie below `H≤X`.
The Dirichlet upper budget has `O(d² log H)` bits, even though explicitly
enumerating that many points can be exponentially costly in `n`.

For the cancellation theorem itself, huge hidden monomial coefficients cannot
evade the argument: interpolation at `0,1,2,3,4` bounds them by a fixed constant
times `qN/X+E`. All five values are bounded by that amount and the inverse
Vandermonde matrix at fixed nodes has constant rational entries. This observation
is only a size bound, not a way to obtain the approximant.

For supplied coefficients of maximum bit length `B`, evaluation at `h<H`
uses `O_d(B+log H)`-bit intermediates. The coefficients of `R_e` have bit length
`O_d(B+log X+log q+n+log(K+1))`. The finite-difference extraction just described
is polynomial in these bit sizes and `log H` per target for fixed `d`.
With schoolbook arithmetic, integer division and multiplication already give a
polynomial bit bound for the fixed amount of rational algebra; no unit-cost
assumption on unbounded integers is needed. Counting candidate roots or blocks
alone still omits coefficient acquisition and error certification.

A complete splitter must pay for every block, all small-factor ranges, failed
acquisitions, and termination. Full factorization also needs recursion and
primality handling as specified by the frozen contract. No complete improved
bound follows from this review, and no current best factoring bound is inferred
from an older paper's historical introduction.

## 8. Narrow primary-source check

Only the following two primary papers are retained as substantive literature
inputs; source PDFs, extracted text, retrieval metadata and hashes are in
[source-manifest.json](W013-polynomial-filter-review-evidence/source-manifest.json).
Search results suggesting other literature were not adopted as evidence. This
is not a broad novelty survey or a repeat of the W012 source audit.

**Sladkey.** Richard Sladkey, *A Successive Approximation Algorithm for Computing
the Divisor Summatory Function*, [arXiv:1206.3369](https://arxiv.org/abs/1206.3369),
especially §§1–3, 6–7. The retrieved PDF labels itself v1, 15 June 2012, while its
title page displays 27 November 2024; the preserved bytes identify the reviewed
copy. It counts lattice points under `xy=N` using rational-slope region
decomposition and coordinate changes, and states `O(N^(1/3))` time and
`O(log N)` space. Its complexity discussion counts regions and recursion depth;
do not silently read those statements as fully audited bit bounds for a new
restricted-interval factoring routine. I checked the definitions and computational
scope, not every step of its complexity proof. Independently, the floor identity
above implies that subtracting counts for `N` and `N-1` counts divisors. A total
divisor count does not locate one without a paid restriction/search procedure.
The paper does not supply Card B's short common-denominator quartic gate.

**Hiary.** Ghaith A. Hiary, *A deterministic algorithm for integer factorization*,
[arXiv:1408.2608v3](https://arxiv.org/abs/1408.2608), 29 July 2016, Algorithm 1,
Theorem 2.1 and Lemmas 3.1–3.2. This is the directly relevant interval method.
It approximates `N/X²` by `b/q` using continued fractions with `q≤4H`, rounds
`qN/X` to `a`, and uses a reciprocal error of absolute value below one. Every
divisor in the block must then solve
`(qN-aX)+(bX-a)h+b h²=0`; exact divisibility tests follow. It states a complete
`N^(1/3+o(1))` bit bound, with `O(N^(1/3) log²N)` listed operations on
`O(log N)`-bit numbers. Its guaranteed half-width is about `X/N^(1/3)`, hence
`N^(1/6)` near `sqrt(N)`. It does not need prime `q` or `q≥H`. This establishes
substantial prior overlap for reciprocal approximation followed by exact
divisor extraction, not a novelty claim for the quartic obstruction. No historical
“fastest known” claim from its introduction is carried forward.

## 9. Failure accounting and next material computation

The failed assumption is acquisition of a bounded-error, short-common-denominator
integer quartic across the hoped-for balanced width. It fails algebraically even
when arbitrary coefficient errors cancel. No empirical failures or successes are
substituted for that theorem. The generic Dirichlet budget does not repair it.
The modular-root candidate count is correct under its explicit hypotheses, but
those hypotheses are unnecessary for the improved exact-equation extraction.
That correction itself is not an asymptotic factoring improvement.

There were no failed certificate checks, source-download errors, or extraction
errors. The initial absence check for pre-existing owned-prefix files returned
`rg` status 1 (no matches). Some initial combined read/tool-catalog output was
truncated; the relevant files and Card B were then read in focused calls and
frozen. Early literature queries produced unrelated hits; only the two primary
PDFs above were used. All computed certificate outputs, including empty stderr,
are retained and hashed. No solver benchmark or shared Lean audit was run because
no shared implementation was changed and the assignment selects exact evidence
only. Input drift, if any, is separately recorded at delivery; frozen inputs are
the review authority.

The next material question for the parent is a **paid joint extraction across
many error integers**, or a directly paid computation of the nonnegative count

    C_N(L,U) = Σ_(x=L)^U [floor(N/x)-floor((N-1)/x)].

An exact count would permit interval localization, but the count operation must
be constructed and priced; merely giving it a name is not an algorithm. A useful
next brief should specify how nearby numerator levels or many equations `R_e`
share work, with a bound that does not enumerate every offset or error integer.
Sladkey supplies the relevant floor-counting comparison, and Hiary already
supplies the linear bounded-error exact-equation comparison. Repeating a prime
search or enlarging the quartic parameter sweep cannot test the closed gate.

For example, under the obstruction's hypotheses a larger block requires
`E≥qH²/(5120X)`; processing all these targets separately explicitly pays that
many equations. Any proposed batching routine must account for its representation,
construction, integer output recovery, and worst-case false candidates. This is
the concrete remaining computation to specify, not evidence that it is fast or
that every possible alternative is impossible. Parent remains principal ideator.

**Final status: selected quartic gain rejected; extraction formulation revised;
complete factoring improvement NONE.**
