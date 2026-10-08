# H009 first-quotient obstruction for literal sparse long division

Status: paper derivation by native Astra /root/h007_lattice_carries, root-checked
and independently CONFIRMED by /root/h007_additive_relations. NOT a Lean
theorem or a measured runtime. Candidate is H009-crt-euclid-v1, fixed curve and
shifts before uniform finite target sampling. No engine or numerical pilot used.

## Exact leading form and quotient

Let e_i=N/B_i and b0=min B_i. Standard Semaev normalization has individual degree
16 for S6 and LC_x S_m=S_(m-1)^2. The latter follows by applying the resultant
recursion to the leading square (x-X)^2 in S3. Repeated extraction gives

    coefficient(x1^16 x2^16 x3^16 x4^16 x5^16, S6)=1.

For every r and fixed shifts, f_r(T)=S6(u_i+T^e_i,r) is therefore monic with
EXACT degree D=16 sum e_i. No generic-coefficient or singular-curve assumption.
Define the reversed multivariate polynomial

    H_r(z)=product(z_i^16) S6(u_i+1/z_i,r),    H_r(0)=1,
    H_r(z)^(-1)=sum_{nu>=0} c_nu(r) z^nu.

The quotient of T^N-1 by f_r is the polynomial part of

    T^(N-D) sum_nu c_nu(r) T^(-sum nu_i e_i).

The -1/f_r contribution has only negative degrees. CRT prevents EVERY possible
support collision below weight N, not merely collisions between selected terms:
if sum nu_i e_i=sum nu'_i e_i<N, nonnegativity gives nu_i,nu'_i<B_i; reduction
modulo each B_i then gives equality because e_i is invertible modulo B_i.

## A two-variable face with explicit coefficients

Leading extraction in the other three variables gives the exact identity

    H_r(z,w,0,0,0) = [z²w² S3(u1+1/z,u2+1/w,r)]^8 = F_r(z,w)^8.

In F_r, target degree of each coefficient is at most its total z,w degree.
The terms attaining that degree are

    1 - 2r(z+w) + r²(z-w)².

Thus c_(a,b,0,0,0)(r) has degree at most a+b, with leading coefficient

    C_ab = (16)_(a+b) (17/2)_(a+b)
           / [(17/2)_a (17/2)_b a! b!],

where (x)_n denotes the rising factorial. This is an identity of actual
coefficient polynomials, with curve coefficients and shifts fixed arbitrarily.

Derivation: rewrite (1-2z-2w+(z-w)²)^(-8) as
(1-z-w)^(-16) [1-4zw/(1-z-w)²]^(-8). Its z^a w^b coefficient is

    (16)_(a+b)/(a!b!) * sum_{j=0}^{min(a,b)}
        [(-a)_j(-b)_j / ((17/2)_j j!)].

Duplication (16)_(2j)=4^j(8)_j(17/2)_j cancels the intermediate factors.
Terminating Vandermonde evaluates the sum as
(17/2)_(a+b)/[(17/2)_a(17/2)_b], giving the formula. Root independently checked
this extraction algebra; the low coefficients C_10=16 and C_11=304 are consistent,
but those small checks are not used as a proof of the identity.

## Characteristic, range and exceptional targets

Set h=floor(b0/8), require b0>=160 and p>4h+16. For 0<=a,b<=h, all rising-factorial
numerator and denominator factors above are nonzero in F_p. Consequently the
coefficient polynomial has exact target degree a+b and at most a+b roots.

Furthermore D/N<=80/b0<=1/2 and a e1+b e2<=N/4<=N-D. All these coefficients
therefore become distinct quotient terms; none can cancel against another
nonnegative multi-index. At most

    sum_{a,b=0}^h(a+b)=h(h+1)^2

target abscissae annihilate any selected coefficient. Outside this union, the
FIRST quotient has at least (h+1)^2 nonzero terms. For a uniform finite point of
the full order-q curve, the bad probability is at most

    beta = min(1, 2h(h+1)^2/(q-1)) = O(B^(-2))

in the declared balanced B_i~B, q~B^5 family. Each abscissa has at most two points.
The bound is uniform over fixed nonsingular curves and fixed shifts satisfying
the stated hypotheses. It does not cover choosing shifts as functions of r.

## Literal algorithm and cost consequences

Leading-term long division creates exactly one nonzero quotient monomial per
iteration, with strictly descending leading degree. Thus at least (h+1)^2=
Omega(B²) iterations occur on every nonexceptional target before even the first
remainder is complete. This holds without storing the quotient, whatever the
final gcd degree, and supplies no peak-memory lower bound.

Uncapped expected first-division work is Omega(B²) for uniform finite targets.
A fixed cap below the iteration threshold cannot complete a nonexceptional query;
these failures are inconclusive, not certified emptiness. Success is confined
to mass at most beta, so constant useful yield is impossible under that cap.

For the advertised at-most-one-useful-row-per-query ledger, let K denote actual
expected paid query cost and sigma useful-success probability. With a cap below
the threshold, sigma<=beta and every query pays at least one event, so K/sigma
is Omega(B²); a zero-success cap supplies no solver. With a cap at least the
threshold, nonexceptional targets pay Omega(B²) and sigma<=1 gives the same
bound. Uncapped execution also pays Omega(B²) in expectation. Thus the advertised
B*K/sigma collector costs at least Omega(B³), exceeding B^(5/2), before setup.
This conclusion is independently reviewed under fixed caps and uniform finite
targets, with no extra pre-screening oracle.

## Batch-aware cost extension, independently confirmed

Root proposed and /root/h007_additive_relations independently confirmed this
extension. Let X be paid work and Y newly usable independent rows from a query.
There are N ordered coordinate tuples, each with at most32 rational sign tuples;
each signed tuple sums to exactly one point. Thus, for a uniform finite target,

    E[number of available verified witnesses] <= C=32N/(q-1)=O(1),
    E Y <= C.

Noncurve values, duplicate witnesses and rank loss only reduce Y. Target labels
fixed within the query do not multiply independent rows from the same witness.
Let L=(h+1)^2 and eps=2h(h+1)^2/(q-1)<1 in the asymptotic regime. Under literal
v1 with its cap selected before the independent target and no extra early-return
screen, every unfinished ordinary query consumes its cap.

- Cap K<L: E X>=(1-eps)K. Only exceptional targets can emit rows, and each emitted
  row costs at least one event, so E Y<=eps*K.
- Cap K>=L (including uncapped execution): E X>=(1-eps)L while E Y<=C.

Consequently E X>=gamma E Y in both cases, where

    gamma=min((1-eps)/eps, (1-eps)L/C)=Omega(B²).

If eps=0, the first regime emits no rows. The inequality holds conditional on
prior history for fresh uniform targets and pre-target cap choices. Multiply by
the history-measurable indicator that a next query is attempted, sum finite
prefixes, then use monotone convergence for nonnegative costs/rewards. Predictable
stopping and overshoot are handled by counting the rows actually emitted and
charging their extraction. A collector producing Theta(B) independent rows with
constant completion probability therefore costs Omega(B³) in expectation.

This closes rare high-output queries for the advertised uniform-target collector.
It does NOT prove every conceivable solver needs Theta(B) rows: early special
dependencies/direct recovery need their own analysis. A cheap additional rejection
screen invalidates the small-cap consumption premise and is a new operation.
Target-dependent shifts, nonuniform samplers, modularly reduced construction,
compressed reciprocals and other gcd algorithms are outside this proof.

This rejects the named literal recurrence's optimistic constant-yield gate;
faster gcd schedules, compressed reciprocals or target-dependent shifts are new
algorithms. Degree was not used as a sparse support bound. No claim excludes
coordinate-aware ECDLP methods generally.

Primary source inspected by derivation author for standard S3/resultant facts:
[Gorla–Massierer, Definition3 and Theorem1](https://arxiv.org/pdf/1403.0126).
The reciprocal coefficient and cost argument above are this research derivation,
not attributed to that paper. Original Semaev PDF fetch failed403.

Independent prior-art review found CRT roots-of-unity encoding in earlier work
and a recent [2026 paper](https://arxiv.org/abs/2606.12144); generic hardness from
that paper is NOT applied to this fixed-S6 family. Known dense upper bounds do
not establish lower bounds for every implementation. The raw Opus report's
generic slice-growth assumption is not needed for the two-variable argument.

Verified improvement NONE; baseline unchanged. The literal first-division
hypothesis and advertised uniform-query collector, including explicitly paid
batch output, are rejected on reviewed paper evidence. Broader gcd algorithms
are not excluded. Validation is paper review plus project regression checks,
not a new Lean certificate or performance measurement.
