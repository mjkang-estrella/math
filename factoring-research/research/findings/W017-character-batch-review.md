# W017 character-batch review

Review date: 2026-10-08 America/Los_Angeles; evidence retrieved 2026-10-09 UTC.
Role: independent review child; the parent remains principal researcher.
Disposition: **accept the finite computation with explicit precision/cost details;
do not promote it to a new factoring algorithm or a new asymptotic batching bound.**
Verified new end-to-end factoring improvement: **NONE**.

The complete submitted [W017](W017-character-batch-review-evidence/inputs/research/hypotheses/W017.md)
was read. Its SHA-256 is
`bbcc3a8f97c11a71e46dda43a41ec26f685abc8213d28e043737cc1d97dc9537`.
The [exact brief](W017-character-batch-review-evidence/brief.txt), required project
instructions, background W001, checkpoint, and primary PDFs are frozen in the
[evidence directory](W017-character-batch-review-evidence/).
The final `delivery-manifest.json` records payload hashes, including this report;
`delivery-manifest.sha256` is its separate hash anchor.

## Decisions

1. **Accepted:** the three-valued Euler-log identity, periodic generating
   functions, balanced rational summation, coefficient extraction, and C-term
   sieve compute all the requested finite Euler logs.
2. **Accepted with details supplied below:** exact arithmetic modulo `2^W`
   preserves the rounded-weight sums despite intermediate wraparound. A final
   magnitude bound, including both A and C, gives unambiguous signed recovery.
   Neither division by 2 in that ring nor a field FFT in that ring is justified
   or needed.
3. **Accepted as an upper bound:** soft-O(D_B+K) with polynomial logarithmic
   precision costs, charging period construction. This is a numeric-parameter
   bound, not polynomial time in the bit length of N.
4. **Prior-art overlap is stronger than just the class-number motivation:** a
   Fourier expansion of these SAME periods, followed by established exponential
   sum multi-evaluation, already gives the same soft-O(D_B+K) bound for the SAME
   finite outputs and error target. The modular implementation is a different
   realization; no asymptotic or priority novelty is established.
5. **Accepted:** square multipliers with no new omitted local factors have
   identical relative truncation errors. The exact formula also identifies what
   changes when a multiplier has primes above B.
6. **Accepted only conditionally:** the single-search 1/5 balance and the
   all-K search exponent 5/4 in K. They neither prove an unconditional tail bound
   nor supply useful class samples, certification, or successful factor recovery.
7. **Rejected as inferences:** free sharing of baby tables across discriminants;
   identifying an annihilator of one element with the class number; assuming
   independent analytic errors or useful-torsion successes across multipliers;
   and importing Hiary's post-precomputation per-value cost into a single hidden
   composite conductor.

No arithmetic experiment was run. The optional rational-weight certificate was
unnecessary for these algebraic proofs and would not test the unresolved analytic
or extraction steps. No failures or trials have been omitted. No delegation,
installation, shared solver/Lean/STATE/registry change, or commit was made.

## 1. Exact finite identity and domains

Let B >= 2 and K >= 1 be integers, and let D be an explicitly supplied integer.
Define the finite target

    E_B(Dk) = product_(prime ell <= B) (1 - (Dk/ell)/ell)^(-1),
    S_k = log E_B(Dk),                 1 <= k <= K,

using the Kronecker symbol at 2 and the Legendre symbol at odd primes. Every
factor is positive. This computation makes sense even if Dk is not a quadratic
order discriminant. Such an input does not acquire a class-number interpretation
merely by passing through the computation.

For every prime ell and x in {-1,0,1}, set

    A_ell = (1/2) log((ell+1)/(ell-1)),
    C_ell = -(1/2) log(1-ell^(-2)).

For x=0 both sides vanish; A+C=log(ell/(ell-1)) and -A+C=log(ell/(ell+1)).
Consequently

    -log(1-x/ell) = A_ell x + C_ell x^2.                 (R1)

At an odd prime, write c_ell=(D/ell) and lambda_ell(a)=(a/ell).
Multiplicativity in the numerator gives

    (Dk/ell) = c_ell lambda_ell(k),
    (Dk/ell)^2 = c_ell^2 * 1_(ell does not divide k).     (R2)

This includes zeros and nonsquarefree k. Thus the C contribution is exactly

    C0 - sum_(ell | k, odd ell <= B, c_ell != 0) C_ell,
    C0 = sum_(odd ell <= B, c_ell != 0) C_ell.

Initialize K outputs with C0 and subtract at the indicated multiples. There are
at most `sum_(ell<=B) floor(K/ell)` visits, bounded even by O(K log(B+1));
the usual prime estimate sharpens this. Prime generation and initialization
give soft-O(B+K) work before operand-width factors. Use the SAME rounded C_ell
in the constant and subtraction; these are exact cancellations of integer
weights, not two separately rounded numerical estimates.

At 2, use the eight-entry sequence `(k/2)`: zero for even k, +1 for k=1,7 mod 8,
and -1 for k=3,5 mod 8. Multiply by `(D/2)` and apply (R1). The total addition
cost is O(K); no odd-prime Legendre definition is applied to 2.

Gcds with N during prime construction are legitimate early exits if they give
proper factors. Character zeros alone must not be reported as factors: D can
contain known auxiliary divisors, and gcd=N is not a proper split.

## 2. Rational summation and composite-ring arithmetic

For each odd prime, construct the full period explicitly, for example by
initializing the nonzero residues to -1 and marking the nonzero squares +1.
This uses O(ell) operations on O(log ell)-bit integers. Define

    P_ell(z) = sum_(a=0)^(ell-1) lambda_ell(a) z^a,
    Q_ell(z) = 1-z^ell.

In formal series over any coefficient ring,

    [z^k] P_ell(z)/Q_ell(z) = lambda_ell(k mod ell),      (R3)

because `1/Q_ell = sum_(j>=0) z^(j ell)`. No analytic convergence in z is used.

For integer weights u_ell, put the leaf pair `(U,Q)=(u_ell P_ell,Q_ell)`.
Combine two pairs by

    (U1,Q1), (U2,Q2) -> (U1 Q2 + U2 Q1, Q1 Q2).         (R4)

A balanced tree gives `U/Q = sum u_ell P_ell/Q_ell`, with
`deg Q <= D_B`, `deg U < D_B`, and

    D_B = sum_(odd prime ell <= B) ell.

Zero-weight leaves can be omitted; retaining them preserves the stated bound.
At each tree level the total degrees are O(D_B), so fast multiplication gives
soft-O(D_B) polynomial work over all levels. This does NOT construct the much
larger common period `lcm(ell)`.

Since Q(0)=1, its formal inverse exists over `R=Z/(2^W)`. Starting with G=1,
double the number of correct coefficients using

    G_new = G(2-QG) mod z^(2t),
    1-QG_new = (1-QG)^2.

The second equality proves the step in every commutative ring. There is no
division by 2, differentiation/integration denominator, or inverse of a nonunit.
Compute through `z^(K+1)`, multiply by U, and take coefficients 1,...,K.
The convention matters: recovering coefficient K requires length K+1.

Fast multiplication over R need not assume convenient roots of unity in R.
Lift polynomial coefficients to integers in `[0,2^W)`. For two length-r
polynomials, each integer convolution coefficient is smaller than `r*2^(2W)`.
Packing into base `2^t` with `t > 2W+log2(r)` permits a fast integer product
without carries crossing coefficient blocks. Unpack and reduce modulo `2^W`.
This gives soft-O(r(W+log(r+1))) bit cost using fast integer multiplication.
All temporary lifts have their widths charged. This construction also handles
negative residues by their nonnegative representatives.

The tree and Newton calculation therefore cost

    soft-O((D_B+K)(W+log(D_B+K+2)))                     (R5)

bit operations for polynomial arithmetic, plus the input/weight work below.
Storage is soft-O((D_B+K)W+B) bits, allowing retained tree levels; streaming or
discarding finished levels can reduce constants. Cancellation of a common
`1-z` in an individual leaf is possible but does not change the stated scale.

## 3. Precision, absolute error, and signed recovery

It suffices to consider a requested 0 < epsilon <= 1. Let m=pi(B). Choose b so
that `2m*2^(-b) <= epsilon/2`, and compute certified integers a_ell,d_ell with

    |2^(-b) a_ell - A_ell| <= 2^(-b),
    |2^(-b) d_ell - C_ell| <= 2^(-b).

Compute the integer target

    T_k = sum_(ell<=B) [a_ell (Dk/ell) + d_ell (Dk/ell)^2].

Use u_ell=c_ell*a_ell in (R4), the integer C sieve, and the separate 2 term.
For EVERY k, simultaneously and deterministically,

    |2^(-b) T_k - S_k| <= 2m*2^(-b) <= epsilon/2.       (R6)

There is no union bound over K and no error amplification by the rational
denominator: the polynomial work is exact on the rounded weights.

For ell >= 2, both A_ell and C_ell are positive and less than 1. Hence
`|a_ell|,|d_ell| <= 2^b+1`, and the entirely explicit bound

    |T_k| <= M0 := 2m(2^b+1)

holds, including the prime 2. Choose W with `2^(W-1) > M0`. For example,
`W=b+ceil(log2(m+1))+4` is sufficient. After combining all terms modulo `2^W`,
interpret a residue r as r if `r < 2^(W-1)`, otherwise as `r-2^W`.
The result is exactly T_k. A bound only for the A part is insufficient if the
combined A+C output is reconstructed with the same modulus without checking
its full bound. The strict inequality removes the sign-boundary ambiguity.

Large expanded coefficients in U, Q, or Q^(-1) are irrelevant: reduction is a
ring homomorphism, and (R3)-(R4) identify each final coefficient with the small
integer sum T_k. One does not attempt signed reconstruction of intermediate
polynomials. Dyadic scaling is undone AFTER signed recovery; `2^b` is not
inverted modulo `2^W`.

Certified weights are obtainable without an L-function oracle. For example,

    A_ell = sum_(j>=0) 1/((2j+1) ell^(2j+1)),
    C_ell = (1/2) sum_(j>=1) 1/(j ell^(2j)).

For ell >= 2 their omitted tails have geometric bounds, so O(b+1) terms with
guard bits suffice. Even elementary rational interval arithmetic has cost
polynomial in b+log(B+1) per prime; faster logarithm routines are optional.
Do not implement the displayed real halves as divisions in R.

The dyadic `2^(-b)T_k` itself already meets the requested error. If it is
converted to another format, reserve the other epsilon/2 for that conversion.
Exponentiation gives relative product error at most `exp(epsilon)-1`, NOT
absolute product error epsilon. A simple bound, obtained by including all
integers 2,...,B in the extremal products, is

    2/(B+1) <= E_B(Dk) <= B.

Thus an absolute product tolerance eta can instead be met with a suitably
smaller log tolerance O(eta/B) and certified exponential rounding. Multiplying
by a class-number scale proportional to sqrt(|D|k) similarly changes the
necessary numeric tolerance. These are precision requirements only; they
control no infinite-product tail.

Including the prime sieve, period marking, Kronecker/Legendre tests on D, all
weights, and K outputs, a conservative uniform bound is

    soft-O((B+D_B+K) * poly(log(|D|+2)+log(B+2)
                           +log(K+2)+log(1/epsilon))).   (R7)

For B>=3, B can be absorbed at this scale into D_B. The bound `D_B <= B^2`
is enough here; in the ordinary large-B prime regime it is of order
`B^2/log B`. No period table, factorization of N, or exact real operation is
free in (R7).

## 4. Equal-input comparisons and verified prior-art overlap

The basic comparator receives the SAME D,B,K,epsilon and computes the SAME
finite products. Sieve once, compute the weights and c_ell once, then evaluate
each character `(k/ell)` directly for each k. Its cost is
`(B+K*pi(B))*polylog` in these parameters. It does not need all the length-ell
period tables. The candidate is genuinely useful against this straightforward
comparator when K is sufficiently larger than B, up to logarithms. Small K
should use the direct method. Precomputing the periods for both algorithms
and then declaring their construction free would be an unfair comparison.

There is also a stronger, explicit comparator. This reduction is made here
from the finite periods, rather than inferred from a theorem about conductors.
Let

    v_(ell,a) = (1/ell) sum_(r=0)^(ell-1)
                 lambda_ell(r) exp(-2*pi*i*a*r/ell).

The inverse discrete Fourier identity, proved by summing the finite geometric
series, gives

    lambda_ell(k) = sum_(a=0)^(ell-1)
                       v_(ell,a) exp(2*pi*i*a*k/ell).

Therefore the full A contribution is an exponential sum with at most D_B
terms, frequencies a/ell, and coefficients c_ell*A_ell*v_(ell,a). Since
`|v_(ell,a)|<=1` and `A_ell<1`, these coefficients have magnitude <=1.
The same paid period construction followed by FFTs of those periods costs
soft-O(D_B) at the required precision. Non-power-of-two periods can be
transformed through convolution with padding; they do not require quadratic
DFTs. The C sieve and prime 2 treatment are unchanged.

Hiary's Theorem 5.1 states that J bounded-coefficient exponential modes can be
evaluated at H consecutive centered integer indices with error eta in
`O(M log^2(M/eta))` arithmetic operations on `O(log(M/eta))`-bit numbers,
where M=max(H,J). Choose H=2(K+1), J<=D_B. This gives the SAME
soft-O(D_B+K) finite-output bound. [Hiary, section 5, p. 7](https://arxiv.org/pdf/1608.06614v2).

Coefficient and phase construction must be accurate as well. With J terms,
coefficient errors <=epsilon/(16 max(1,J)) and frequency errors
<=epsilon/(32*pi*max(1,J)*max(1,K)) contribute O(epsilon) in total, by
`|exp(ix)-exp(iy)|<=|x-y|`. Allocating smaller fixed shares also covers weight,
FFT, and final evaluation errors. This takes only logarithmic guard precision.
Frequencies a/ell may alternatively be supplied as exact rationals. Thus this
is a same-precision, same-input algorithm, not a unit-cost exact-complex oracle.

The primary Odlyzko-Schonhage text develops FFT reduction to rational
multi-evaluation in section 3 and gives the finite-precision rational evaluator
in Theorem 4.1. Its displayed theorem has a separation condition; section 3
handles near-coincident evaluation points separately. One must not drop that
condition from a naive partial-fraction implementation. Hiary's exponential-sum
statement is the convenient packaged comparator above.
[Odlyzko-Schonhage, sections 3-4](https://www-users.cse.umn.edu/~odlyzko/doc/arch/fast.zeta.eval.pdf).

Brent-Kung is supporting background for fast formal-series computation, not a
theorem that arbitrary floating-point or composite-ring computations have unit
cost. Its introductory model discussion explicitly separates coefficient
arithmetic assumptions. The ring and bit-width arguments in sections 2-3 of
this review are supplied directly.
[Brent-Kung, pp. 581-582](https://maths-people.anu.edu.au/brent/pd/rpb045.pdf).

**Exact overlap established:** existing exponential-sum machinery applies to
this very finite family at the claimed asymptotic cost. **Not established:**
that a previous paper printed precisely W017's A/C decomposition plus dyadic
`Z/(2^W)` implementation, or who first used that combination. The inspected
sources do not justify either an exact-code identity claim or a novelty claim.

Hiary's distinct full-L-value Theorem 1.1, for fixed t and conductors in
`[Q,Q+H)` with `1<=H<Q/2`, uses `O(Q log^4(Q/epsilon))` precomputation
operations and bits of storage, then `O(d(q) log(Q/epsilon))` operations per
value on logarithmic-width numbers. The d(q) factor is not uniformly
polylogarithmic; its favorable average is over the conductor family. The
introduction explicitly allows s=1.
Section 4's composite inclusion/exclusion requires divisors; section 6 charges
their acquisition by sieving the conductor interval. The full proof, especially
the auxiliary analytic estimates and s=1 adaptation, was not independently
verified here. [Hiary, pp. 1-2, 6, 8](https://arxiv.org/pdf/1608.06614v2).

For the promised fundamental subfamily with |D| comparable to N, conductors
in a block of multipliers k comparable to K have scale Q comparable to NK.
They are a sparse progression inside that conductor range. Applying that
full-conductor precomputation literally pays soft-O(NK), not soft-O(K).
Likewise, factoring conductors throughout an interval is not free information
about the divisors of the particular hidden N. This inference explains why
the full-L-value theorem is not a free replacement for a tail bound, while its
general exponential-sum subroutine IS a matched finite-product comparator.

## 5. Square multipliers: exact dependence, not a variance assumption

Assume now D is a negative quadratic order discriminant, so chi_D is a
nonprincipal quadratic Dirichlet character. For every positive f,n,

    chi_(D f^2)(n) = chi_D(n) * 1_(gcd(n,f)=1).          (R8)

This follows from multiplicativity of the Kronecker symbol, including the
prime 2. First in Re(s)>1 by absolute convergence, then at s=1 by analytic
continuation of the finite-factor identity,

    L(1,chi_(D f^2)) = L(1,chi_D) J_f,
    J_f = product_(ell | f) (1-chi_D(ell)/ell).

Directly for the finite product,

    E_B(D f^2) = E_B(D) J_(f,B),
    J_(f,B) = product_(ell | f, ell<=B) (1-chi_D(ell)/ell).

It follows exactly that

    L(1,chi_(D f^2))/E_B(D f^2)
      = [L(1,chi_D)/E_B(D)]
        * product_(ell | f, ell>B) (1-chi_D(ell)/ell).  (R9)

If f is B-smooth the last product is 1. More generally factors with chi_D(ell)=0
also contribute 1. The normalized relative error, or log-tail error, is then
identical for all these multipliers. Averaging after removal of known local
factors cannot reduce it. Absolute unnormalized errors scale by J_f, and class
numbers additionally scale by the discriminant square root and the unit factor;
they are not numerically equal errors.

When f has relevant primes above B, the difference in (R9) is explicitly known
if those primes have been acquired. Removing those additional local factors
still leaves the common unknown tail; it is not independent error sampling.
For a fixed nonsquare multiplier d, the same statement applies within its
square class k=d*f^2. Nonsquare multipliers outside that square class require a
new analysis. W017's exact argument is NOT a theorem that every conceivable
relationship between class groups enforces this particular correlation.

## 6. Analytic and class-group obligations

The old approximation-plus-search route is explicitly described in the
introduction of Schnorr-Lenstra: the earlier 1/4-scale approach is accelerated
to 1/5 using the class-number formula, with the approximation error qualified
by generalized Riemann hypotheses. Their paper's own smooth-class-number Monte
Carlo method is a separate algorithm and carries its own assumptions.
[Schnorr-Lenstra, printed pp. 289-291, especially p. 290](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1984c/artc.pdf).

Schoof supplies the relevant precise primary comparison: section 3 describes
approximation and interval search; Theorem 6.3, assuming GRH, bounds

    |1-product_(p>x)(1-chi_Delta(p)/p)|
        < c3 log(|Delta| x)/sqrt(x),
    x > c2 log^2(|Delta|).

Algorithm 6.4 uses suitable negative order discriminants, small split-prime
forms, and 2-primary extraction to obtain the GRH-qualified
`O(N^(1/5+eta))` factoring bound for every fixed eta>0. Theorem 6.1/Corollary
6.2 also bring GRH-based generation information. The analytic class-number
formula on p. 245 includes nonmaximal orders.
[Schoof, pp. 245, 247-250, 266-272](https://www.mat.uniroma2.it/~schoof/mcpaper.pdf).

These are conditional primary-source results, not an unconditional 1/5
factoring theorem obtained from W017. The proof outline of Theorem 6.3 and the
algorithm were inspected, but their external analytic/genus-theory dependencies
were not reproved. No comparison with modern unconditional factoring bounds or
GNFS is inferred from these three historical sources.

To see the error conversion, write

    h_Delta = w_Delta sqrt(|Delta|)/(2*pi) * L(1,chi_Delta),
    hhat = w_Delta sqrt(|Delta|)/(2*pi) * E_B(Delta).

The unit count w_Delta is 2 apart from the exceptional orders Delta=-3,-4.
If a justified tail statement says `|E_B/L-1|<=r<1`, then the exact h lies in

    [hhat/(1+r), hhat/(1-r)].                            (R10)

Its width is `2*r*hhat/(1-r^2)`, before numerical enclosure errors. A bound
on the log tail similarly gives `[hhat*exp(-r), hhat*exp(r)]`. A small absolute
error in log E_B alone implies NEITHER interval. In using the published
conditional tail estimate uniformly over k, impose its cutoff threshold for
the largest |D|k, keep r bounded below 1, and supply the ordinary upper bounds
on the class-number/L-value factor before suppressing logarithms.

A negative integer congruent to 0 or 1 modulo 4 defines an imaginary quadratic
order and a primitive-form class group without first finding its maximal
order. Thus restricting to fundamental discriminants is sufficient but not
necessary for this route. If W017 chooses that restriction, a sieve of k does
not certify squarefreeness of the unknown N or of D. If it instead uses
nonmaximal orders, it must specify the imprimitive character, unit correction,
and useful-factor argument. Neither choice makes an unknown conductor
factorization free. Sieving k<=K for its own prime factors and squarefree
status costs soft-O(K); testing gcd(k,N) costs K polynomial-logarithmic
operations and may itself find a factor. Constructing split-prime forms
requires character tests and square roots modulo those known primes. The
size of that prime pool, sampling/mixing work, and random bits also belong
in the extraction budget.

For one element g in such a finite group, an interval containing h also
contains an annihilating exponent: g^h=1. If its integer interval is [L,U],
clip L to at least 1, and let J=U-L and t=ceil(sqrt(J+1)). Store g^j for
0<=j<t (the smallest j for each repeated group element) and look for equalities

    g^j = g^(-L-it),

for the required i. A match gives g^(L+it+j)=1; check the interval boundaries
and the identity. This costs O(sqrt(J+1)+log(U+2)) group operations and
O(sqrt(J+1)) group elements, plus construction and comparisons. It identifies
AN annihilator, not necessarily h or the order of g.

For clarity, full class-number certification is NOT necessary just to try
factoring. Given a positive annihilator m of g, write m=2^t*u with u odd.
Compute g^u and square repeatedly. If g has even order, the last nonidentity
element before 1 has order 2; this costs O(log m) group operations and needs
no factorization of u. If g has odd order it yields only 1. Even a nonidentity
involution can give only a split of auxiliary parts of Delta, so its gcds
with N must be checked for a proper split.

Annihilation does not certify the group: an element in the C3 subgroup of
C2 x C3 is annihilated by 3, although the group has order 6 and that element
cannot generate its 2-torsion. This is a logical counterexample to the
inference, not a claim about a distribution of class groups. Sampling more
elements from the same restricted subgroup does not repair it. Either prove
the sample's useful coverage and its acquisition cost, or use a justified
generator procedure and pay for it. The known conditional factoring approach
does the latter; W017 supplies no better replacement.

Different Delta values do not furnish a common baby table. A stored reduced
form and its composition/reduction law belong to a specified discriminant;
the generator and target also matter. Accidental abstract isomorphism gives
no cheaply computable transport. A product-group table stores K coordinates
and pays for their operations. This observation rejects free table reuse,
not every possible future shared algorithm. Related-order maps likewise need
explicit construction and a useful extraction theorem.

## 7. Exponents and the precise remaining bottleneck

Let `|D|` be comparable to N and suppress only stated polynomial logarithmic
factors. Under the parent's stipulated width envelope

    W_h(B,k) = soft-O(sqrt(Nk)/sqrt(B)),

one interval-annihilator search costs

    soft-O(1 + (Nk)^(1/4) B^(-1/4))                    (R11)

group operations, with additional logarithmic powering overhead. Actual bit
cost includes the group-operation cost at `log N+log k` bits and the number
and acquisition cost of sampled elements. An upper width envelope is not a
lower bound on realized searches, nor a probability law for their success.

For one preselected k of bounded size, compute its finite product directly.
The modeled work is

    T_single = soft-O(B + N^(1/4) B^(-1/4)).

Balancing exponents gives `B^(5/4)=N^(1/4)`, hence `B=N^(1/5)` and
`T_single=soft-O(N^(1/5))`. Derivatives change a constant, not this exponent.
The rational batch cost D_B must NOT replace B in the comparator and then
be silently treated as linear in B.

If every k=1,...,K incurs one full search with that width, then

    sum_(k<=K) k^(1/4) = Theta(K^(5/4)),
    T_searches = soft-O(K + N^(1/4) K^(5/4) B^(-1/4)).   (R12)

The K term handles width below one and mandatory per-group work. For a
filtered subset I the correct expression is the sum over I, not automatically
K^(5/4); charges for constructing and rejecting the remaining candidates
remain. More samples per group, failed trials, or unknown useful coverage
cannot be hidden in (R12) as if a factor had already been obtained.

For the literal all-period batch followed by all searches, the resulting
relaxed cost model is

    soft-O(B^2 + K + N^(1/4) K^(5/4) B^(-1/4)),         (R13)

before those additional success obligations. In the unconstrained parameter
relaxation the balance is `B=N^(1/9) K^(5/9)`, with cost
`N^(2/9) K^(10/9)` up to logarithms. At K=1 this is worse than the direct
single-estimate construction; taking the direct fallback avoids that waste.
For all K direct estimates at a common cutoff, the corresponding balance is
`B=(NK)^(1/5)` and cost `N^(1/5) K^(6/5)`. The two relaxed optima cross at
K of scale N^(1/4), where both have scale N^(1/2). These are comparisons of
specified workloads, not factoring lower bounds or forecasts of measured time.
Parameter restrictions, valid-discriminant filters, and earlier trial-division
successes can change which workload is actually executed.

Processing all K is also not required to find one factor. A proposed selector
could inspect the K approximate values in soft-O(K) work and choose a subset,
but must specify what those values certify. Under the literal width proxy
`sqrt(Nk)/sqrt(B)`, k=1 already minimizes the width; simply scanning for that
proxy buys nothing. A small fractional part of hhat does not certify a small
analytic error. Smoothness of a rounded estimate does not certify smoothness
of h. Selecting a small observed estimate, adaptive cutoffs, or searching
only a few promising groups could change actual costs, but needs an explicit
success/error theorem that remains valid after that selection.

**No materially better extraction or selector is established by this review.**
The precise gap is a paid procedure taking these finite estimates to a
proper-factor witness with a proved or explicitly modeled strategy-valid
success rate, while paying valid tail intervals (or bypassing them), useful
group elements, their distinct-group searches, and nontrivial gcd recovery.
The finite arithmetic saves the repeated character-summation stage; it supplies
none of those missing guarantees. Square-class normalization cannot manufacture
independent tail estimates, and nonsquare character changes do not transport
class-group search work for free.

W001 Card C's uniform-square-collision bound is not applied to this new
approximation-based computation. Its birthday assumptions do not describe
interval-annihilator search. Likewise, no result here addresses the live W016
or W014 audits or establishes a lower bound for factoring in general.

## 8. Disposition and a next question that could change it

Retain W017 as a sound finite-batch implementation proposal with explicit bit
and error accounting. Its advantage over independent evaluation is real for
large batches, but its asymptotic cost has an equal-input construction using
established exponential-sum machinery. No implementation timing comparison,
new factoring complexity, or priority claim is supported.

The next substantive step is to specify ONE factor-extraction or selection
map from the batch outputs, together with acquisition cost, a uniform or
clearly conditional tail/error contract, and a useful-output probability or
deterministic coverage argument. Compare it on identical inputs and analytic
assumptions with the direct single-discriminant approximation route and the
Fourier finite-batch comparator. A proof can change this disposition; a toy
coefficient identity check or more nearly equal normalized square-multiplier
values cannot establish the missing improvement.

Exact source versions, read locations, unread proof dependencies, rendering
scope, and retrieval limitations are recorded in
[read-scope.md](W017-character-batch-review-evidence/read-scope.md). The proofs
in sections 1-3 and 5 and the reductions/cost calculations in sections 4 and 7
are this review's mathematical arguments, not claims that every cited paper
was fully audited.
