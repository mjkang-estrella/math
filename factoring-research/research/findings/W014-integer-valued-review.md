# W014 A — integer-valued polynomial and powered-base audit

2026-10-08 local / 2026-10-09 UTC. Review role only; the parent remains principal
researcher. **Accept the parent's dense-grid rigidity theorem and its stated
polylogarithmic-degree balanced-parameter consequence.** No correction to its
constants or root count is required. Accept the powered-base transfer with the
explicit inherited hypothesis `alpha in (Z/NZ)^*`. The E-sized exponent search
is algebraically valid, but usable powered-base order and useful certificate
acquisition remain conditions, not consequences. **Verified complete factoring
improvement: NONE.**

The original brief and ten local inputs are frozen under
[the evidence directory](W014-integer-valued-review-evidence/), with exact paths,
byte counts and SHA-256 in
[input-manifest.json](W014-integer-valued-review-evidence/input-manifest.json).
The full W014 file is retained to preserve the submitted Card A; B/C are outside
this audit. W013's arbitrary rational numerator/denominator normal form and the
shared batch consumer are not re-audited here. The accepted W013 quartic
disposition is background, not a premise of the proof below. The W013 polynomial
filter review was additionally frozen only for its finite-difference root routine.
No delegation, install, publication, commit, performance run, sweep, shared
solver/Lean/state/registry edit, or new all-factoring lower-bound claim occurred.

## 1. Exact rigidity theorem and proof audit

Let X,L be positive integers, L>=2, let the degree cap d be an integer >=2,
q,N>0, and E>=0. Suppose A is a real polynomial of degree at most d, and
for every integer j in [0,L], A(j) is an integer and

    |A(j)-qN/(X+j)| <= E.

If

    L >= 2d^2,
    8d^4 (E/L^2 + qN/X^3) < 1,                       (R)

then A(h)=a+bh for integers a,b. Here q,N need only be positive reals for
rigidity; the factoring transfer later requires integer q,N. The theorem
concerns degree **at most** d, so an affine solution is allowed from the outset.

**Tangent subtraction.** With T(h)=qN/X-qNh/X^2, exact division gives

    qN/(X+h)-T(h) = qN h^2 / (X^2 (X+h)).

For 0<=h<=L this is nonnegative and at most qN L^2/X^3. Thus, with
R=A-T and U=E+qN L^2/X^3, all grid values satisfy |R(j)|<=U.
No assumption L<X is needed for this bound. It is a bound on R, not on the
nonpolynomial function A(h)-qN/(X+h).

**Markov normalization.** On [-1,1], the uniform-norm inequality is
`||r'|| <= d^2 ||r||`. For r(t)=R(L(t+1)/2), the chain rule gives

    ||R'||_[0,L] <= (2d^2/L) ||R||_[0,L].

The factor 2 is correct. The source for the unweighted uniform norm is
Nikolov–Shadrin's published research article, introduction, equation (1.1),
specialized to k=1: its constant is T_d'(1)=d^2. The latter follows directly
from T_d(cos(theta))=cos(d theta) and the limit at theta=0.
[Nikolov–Shadrin, pp. 227–228](https://www.math.bas.bg/mathmod/Proceedings_CTF/CTF-2010/files_CTF-2010/25-Nikolov.pdf).

**Grid to interval.** Let S=||R||_[0,L]. A maximizing point has an integer
grid point within distance 1/2, including the endpoints. Hence

    S <= U + (1/2)||R'|| <= U + (d^2/L)S,
    S <= U/(1-d^2/L) <= 2U.

Division is legitimate even at the allowed boundary L=2d^2. This is not an
assumption that the maximum lies on the grid, nor an interpolation stability
claim beyond this dense regime.

**Second derivative.** Apply Markov to R', whose degree is at most d-1:

    ||R''|| <= 4d^2(d-1)^2 S/L^2
             <= 8d^2(d-1)^2 U/L^2
             <= 8d^4 (E/L^2+qN/X^3) < 1.

Thus the parent's looser d^4 bound is safe. Subtracting an affine T leaves
A''=R''. The proof does not assert that 8 is optimal.

**Integer second differences and root count.** For j=0,...,L-2,

    Delta^2 A(j) = A(j+2)-2A(j+1)+A(j)
                = integral_0^1 integral_0^1 A''(j+s+t) ds dt.

The integration remains inside [0,L]; its domain has area one. Therefore
each second difference is an integer of absolute value less than one and
must be zero. There are L-1 distinct such zeros. The polynomial Delta^2 A
has degree at most d-2 and L-1>d-2, so it vanishes identically. If A had
actual degree r>=2 and leading coefficient c!=0, Delta^2 A would have
leading coefficient r(r-1)c and degree r-2, a contradiction. Finally
a=A(0) and b=A(1)-A(0) are integers.

Every displayed step is valid for real coefficients. Neither a denominator
bound, a bound on individual power-basis coefficients, nor absence of
cancellation is used. No counterexample satisfying all hypotheses was found;
the analytic proof establishes the conclusion, not the finite certificate.

## 2. Balanced parameters and the extent of the rejection

Interpret X~sqrt(N) and L~X^(3/5) as two-sided bounds with fixed positive
constants. Assume q=O(X^(1/5)), E=O(X^(2/5)) uniformly, and
d(X)<=C(log X)^k for fixed C,k. Then

    d^2/L = O((log X)^(2k) X^(-3/5)) -> 0,
    E/L^2 + qN/X^3 = O(X^(-4/5)),
    8d^4(E/L^2+qN/X^3)
        = O((log X)^(4k) X^(-4/5)) -> 0.

Both guards hold eventually. The big-O constants must not vary secretly
with X or with an unbounded choice of k. Small instances are decided by
the actual inequalities, not by the asymptotic notation.

Consequently every admissible approximant in this regime is an ordinary
integer affine polynomial. Its minimal coefficient-clearing denominator is
1; retaining a large factorial M after proving affinity buys nothing. This
rejects obtaining a nonaffine approximation improvement by changing only
integer power-basis coefficients to integer-valued rational coefficients at
these budgets. It does not prove that every affine generator/search has a
particular lower bound, or rule out shared work, other parameter ranges,
sparse domains, changed representations, or factoring improvements generally.
Failure of (R) is not evidence that a useful nonaffine certificate exists.

## 3. Integrality, negative offset and denominator transfer

For an integer-valued rational polynomial of degree <=d, Newton expansion is

    A(h)=sum_(j=0)^d c_j binomial(h,j),
    c_j=Delta^j A(0) in Z.

In fact, integer values at just 0,...,d suffice: these finite differences
are integers, and Newton interpolation agrees with A as a polynomial.
Thus the dense-grid hypotheses already imply global integer-valuedness,
even if one initially only assumes real coefficients. For t>=1,

    binomial(-t,j)=(-1)^j binomial(t+j-1,j) in Z.

This proves integrality at 1-X, including negative offsets. Taking M=d!
clears the power-basis coefficients since each j! divides d!. A single
degree cap for all certificates supplies a single common M. A common multiple
of the actual coefficient denominators may be smaller; d! is sufficient,
not necessary or guaranteed to preserve good order.

Let p|N be prime, Q=N/p, q>=1 integer, and let p=X+h lie in a covered block.
Define the integers

    e=A(p-X)-qQ,       D=A(1-X)-qN,       P=MA in Z[h].

Then p-X and 1-X are congruent modulo p-1, and N-Q=(p-1)Q. Hence

    M(D-e)=P(1-X)-P(p-X)-Mq(N-Q) = 0 (mod p-1).

For **a unit alpha modulo N**, beta=alpha^M gives

    beta^(D-e)=alpha^(M(D-e))=1 (mod p),
    beta^D=beta^e (mod p).

Negative exponents require the computable inverse of alpha or beta modulo N,
with its gcd/inversion cost paid. The statement is not justified for an
arbitrary nonunit alpha. That unit hypothesis is explicit in W013 and should
be written explicitly when Card A is used on its own.

The searched exponent is e, not Me: if |e|<=E, it lies in
[-floor(E),floor(E)]. The factor M moves into the base and public computation.
No inverse of M modulo N or modulo p-1 is used or required. One must not
cancel M from the congruence without an additional coprimality hypothesis.

The fixed counterexample to cancellation is A(h)=binomial(h,2), N=15,
p=3, X=2, q=1, M=2, alpha=2. Here A(-1)=1, e=-5, D=-14 and
D-e=-9 is not divisible by p-1=2, whereas M(D-e)=-18 is. Modulo 3,
alpha^D=1 and alpha^e=2, but beta^D=beta^e=1. This verifies both the
need for powering and the negative-offset convention.

## 4. Order loss and exact recovery

For any unit alpha and any modulus m, if r_m=ord_m(alpha), then

    ord_m(alpha^M)=r_m/gcd(r_m,M).

This follows because r_m divides Mt exactly when r_m/gcd(r_m,M) divides t.
It applies both to N and to each prime component. A lower bound on r_N
alone need not be a useful lower bound on the powered order. A sufficient
worst-case bound r_N>=MB can be far more demanding than r_N>=B.

In the fixed N=15 example, alpha=2 has order 4. M=2 reduces that to 2;
the valid common choice M=4!=24 reduces it to 1. Padding a degree-two
certificate into a degree-four family can therefore annihilate its base.
This is a counterexample to unconditional order preservation, not a large-N
distribution claim. Small bit length of M does not prevent this loss.

The W013 consumer's prerequisite becomes ord_N(beta)>=B. Its component-order
checks must use beta as well: for 1<=j<B, a proper gcd(beta^j-1,N) is useful;
a gcd of N reports an order failure, not a proper factor. If global order is
at least B and no proper gcd occurs, all these gcds are 1 and every prime
component has order at least B. Acquiring or certifying such a base and
handling failed attempts remain charged obligations. This is the interface
needed from the separate W013 consumer audit, not a reproof of its batch stage.

For a tagged candidate error e', recovery uses

    F_e'(x)=x(P(x-X)-M e')-MqN in Z[x].

Its constant coefficient is -MqN!=0 and its degree is at most d+1. For the
true error e, P(p-X)-Me=MqQ, so F_e(p)=0. It has at most d+1 distinct
integer roots; each must be checked for being a proper divisor of N. A
global modular collision with a wrong e' may yield no factor, and its work
cannot be omitted. Uniqueness of the relevant baby index still requires
the component-order condition above. Nonzero F is necessary for bounded
algebraic recovery; it does not make every modular collision informative.

In the fixed transfer case F(x)=x^3-5x^2+16x-30, F(3)=0 and F(0)=-30.
There is no exact-reciprocal zero-polynomial degeneracy in this representation
when M,q,N>0. This observation does not duplicate the distinct W013 rational
numerator/denominator normalization audit.

## 5. Variable degree: an explicit polynomial-bit qualification

Write n=bitlength(N), and suppose the binomial coefficients c_j have at most
b bits in absolute value. Let lambda=ceil(log2(X+L+d+3)). With exact dense
representations, elementary bounds give

    log2(M+1) = O(d log(d+1)),                 M=d!,
    bitlength(A(1-X)) = O(b + log(d+1) + d log(X+d+1)),
    bitlength(D) = O(b + d lambda + log(d+1) + log(q+1) + n).

For example, bound each negative-offset binomial by (X+d+1)^d and sum d+1
terms. Multiplying falling-factorial polynomials, clearing denominators,
and shifting by X gives a sufficient coefficient-bit bound for F_e'

    tau = O(b + log(M+1) + d log(X+d+1)
              + d log(d+1) + log(|e'|+1) + log(q+1) + n).

These expressions are bounds on written integers, not unit-cost arithmetic.
Constructing d!, computing beta, exact evaluation, shifts and modular powers
are polynomial in these bit lengths and d. They are polynomial in n only
under corresponding polynomial bounds on d,b,lambda,log q and log(E+1).
An arbitrary enormous supplied M must instead be charged by its actual bit
length. Exponents cannot be reduced modulo N or M in lieu of their unknown
group order.

There is a useful extra observation in the full-grid setting. Since L>=d and
|A(j)|<=V:=qN/X+E for j=0,...,d,

    |c_j| <= 2^j V.

Thus b=O(d+log(V+1)); enormous coefficient heights are not an independent
escape here. This bounds representation size of an existing certificate,
not the work to find one. Large intermediate expressions in a chosen
construction are still charged.

The fixed-degree root routine need not be treated as a degree-independent
constant. It admits the following explicit extension. For a nonzero integer
polynomial F of degree m<=d+1 and a finite integer interval [a,b], recursively
find the maximal sign runs of Delta F on [a,b-1]. On each run [l,r], F is
monotone on [l,r+1]. At most two exact binary searches find its negative,
zero and positive portions. Merge overlaps and adjacent equal signs before
returning the sign runs. Constant polynomials and singleton intervals are
base cases. The recursive polynomial is computed once for the entire interval
at each level, not separately for each subinterval.

A degree-k nonzero real polynomial has at most k roots, so its sampled sign
sequence has at most 2k+1 runs. Summing the run counts over the m levels gives
O(m^2) binary searches and O(m^2 log(b-a+2)) exact evaluations. All forward
difference coefficients have at most tau+O(m log(m+1)) bits: use
Delta^k F(x)=sum_(j=0)^k (-1)^(k-j) binomial(k,j) F(x+j) and k<=m.
Horner evaluation at endpoints of bit length ell uses integers of
O(tau+m log(m+1)+m ell) bits and O(m) arithmetic operations. Formation of
the difference polynomials and sorting/merging their runs are polynomial too.
Top-level zero runs contain at most m integer points, since F is nonzero.
This supplies a polynomial bound in m,tau,ell and log(b-a+2), without a
factoring oracle or a scan of every integer in the block. It is an audited
algorithm description, not a new implemented or timed solver.

Therefore a growing degree that is polynomial in n does **not by itself**
make recovery superpolynomial. Conversely, neither root count alone nor
the old O_d notation justifies this conclusion without the argument above.
Reading all K coefficient lists and all tags, and processing every failed
global match, remain costs. Subject to the separate W013 consumer theorem,
its transformed interface can have a bound of the form

    (B+G+K) poly(n,d,b,lambda,log(q_max+1),log(E_max+2))
        + all certificate/coverage/base acquisition,
    G=sum_i ceil((2 floor(E_i)+1)/B).

This is a conditional cost form, not an unconditional factoring bound or a
claim about its optimal logarithmic factors. In the balanced regime of section
2, rigidity already forces the approximants to be affine before these extra
degree costs can buy an approximation advantage.

## 6. Counterexample checks and retained finite evidence

The [certificate brief](W014-integer-valued-review-certificate-brief.md) and
[source](W014-integer-valued-review-certificate.py) were copied and hashed
before a single execution. Its [complete output](W014-integer-valued-review-certificate-output.json)
retains all five cases and all nine values/errors for each grid case. **5/5
case-specific exact checks passed; none failed, errored or was replaced.**
No prime, degree, parameter or performance sweep was used.

The affirmative grid control takes X=10^6, N=X^2, q=1, L=8, d=2,
A(h)=X-h and E=64/X. Both guards hold; the error is exactly
-h^2/(X+h), and all second differences vanish.

Two explicit boundary examples demonstrate why broadening the result is unsafe:

* Without grid integrality, A(h)=X-h+h^2/X at the same X,N,q,L,d has
  error h^3/[X(X+h)]<=512/X^2. With that E it satisfies both numerical
  guards and is nonaffine. Its value at 1 is not integral, and its second
  differences are 2/X, so the rounding-to-zero inference is unavailable.
* Without density, A(h)=X-h+binomial(h,9), using actual degree d=9 and
  E=64/X, agrees with the affine control on all nine grid points 0,...,8.
  It is integer-valued globally and satisfies the smallness guard:
  `8*9^4*(2/X)=0.104976<1`. It is nevertheless nonaffine and L=8<162.
  Its second difference is binomial(h,7), with exactly the seven available
  grid zeros 0,...,6; seven zeros do not kill a degree-seven polynomial.

These are counterexamples only to dropping assumptions. The transfer and
order cases from sections 3–4 make up the other two fixed certificates.
Five successful algebra cases provide no success probability or timing
evidence for a factoring algorithm.

## 7. Primary-source check and limits of attribution

The source reads are recorded in
[sources/](W014-integer-valued-review-evidence/sources/), including failed
retrievals, search responses, two downloaded primary texts, and the PDF's
extracted text. Searches returning weighted L2 results did not supply the
needed uniform-norm constant and are not adopted.

Nikolov–Shadrin, *On Markov-Duffin-Schaeffer Inequalities with a Majorant*,
Constructive Theory of Functions, Sozopol 2010, published 2012, pp. 227–264:
the introduction and (1.1) were read in the downloaded published text.
They fix the interval [-1,1], the uniform norm and the Chebyshev derivative
constant used in section 1. No weighted L2 bound is substituted for it.
[Published primary article](https://www.math.bas.bg/mathmod/Proceedings_CTF/CTF-2010/files_CTF-2010/25-Nikolov.pdf).

Adcock–Platte–Shadrin, arXiv:1610.04769v3: sections 2.2 and 5.1 were checked
beyond the abstract. Theorem 2.2 states the Coppersmith–Rivlin grid norm
growth in terms of exp(Theta(degree^2/grid_intervals)). Lemma 5.1 proves a
grid-to-continuous bound with Bernstein's **weighted** derivative inequality
and an arcsine mesh parameter. It does not state the exact unweighted Markov
normalization used by the parent. Its role here is related approximation
theory and comparison of proof structure, not a source of the constant 8.
[Primary paper, v3](https://arxiv.org/html/1610.04769v3).

Coppersmith–Rivlin, *The Growth of Polynomials Bounded at Equally Spaced
Points*, SIAM J. Math. Anal. 23(4), 1992, pp. 970–983: the publisher's
abstract and metadata were checked; full text was not available in that read.
No result is claimed to have been checked in its original full text. The
parent theorem only needs the elementary Markov argument given above.
[Publisher record](https://doi.org/10.1137/0523054).

This is targeted source verification, not an exhaustive novelty search.
No novelty for the inequalities, binomial basis, grid-norm technique,
finite-difference recovery, or factoring consumer is asserted.

## 8. Accepted, rejected and conditional claims; next removable hypothesis

**Accepted:** the exact dense-grid rigidity theorem; integer intercept and
slope; the fixed-polylog-degree balanced consequence; global integrality from
consecutive grid values; negative-offset binomial evaluation; M=d! clearing;
unit-base transfer with e rather than Me; the exact order-loss formula;
nonzero recovery polynomial and its root bound; and the explicitly qualified
polynomial-bit arithmetic/root-recovery arguments above.

**Rejected:** canceling M without a coprimality premise; treating high order
of alpha as automatically high enough order of beta; inferring useful supply
or an end-to-end speedup from compact factorial encoding; a nonaffine upgrade
within the balanced full-grid regime; removing grid integrality or the density
guard without another argument; and interpreting this result as a lower bound
on general factoring. These rejected overextensions are distinguished from
the parent's theorem, which is accepted.

**Conditional:** shared-base savings require paid construction of useful
certificates with coverage, a usable common beta and its component-order
conditions, complete collision/extraction handling, and the stated operand
and degree bounds. The review supplies none of the missing useful-supply or
all-input factoring guarantees.

An exact hypothesis a materially different computation could remove is
**one low-degree polynomial approximates the reciprocal and is integer-valued
at every point of a full consecutive grid 0,...,L**. A precise alternative
primitive would construct, from N and public parameters, structured retained
sets S_i with a proved prime-factor coverage property and polynomials A_i
whose required approximation holds only on S_i. It would certify integrality
at retained offsets and at 1-X_i, a common coefficient-clearing M, and costs
for generating, representing, covering and consuming those sets. Sparse sets
would remove the nearest-integer-grid step used here. This is a changed
computation, not a supplied algorithm or a free sieve.

Merely omitting a few points is not sufficient evidence of escape: a long
arithmetic progression in a retained set may permit the same proof after
rescaling, with step-s second differences bounded by s^2||A''||. The next
decisive proof obligation is therefore a concrete paid retained-domain
construction that both avoids an applicable rigidity bound and reduces the
total certificate/error consumer work while preserving factor coverage.
Assessing the parent's separate W014 B/C mechanisms is outside this review.

Delivery hashes cover the report, brief, certificate, all outcomes, input
snapshots and source evidence. The delivery JSON lists payload hashes;
the SHA-256 list additionally hashes that JSON. Its own digest is the final
handoff trust anchor, avoiding an impossible self-hashing manifest.

At the final input integrity check, all ten frozen inputs still matched their
recorded bytes and hashes, and both preregistered artifacts matched the hashes
embedded in the output. The live research/STATE.md and
W013-hidden-period-consumer.md had changed during this review; the live W014
file still matched its frozen copy. This report audits the frozen versions.
The later shared changes were neither made nor re-audited here. Exact live
comparison hashes are retained in
[integrity-check.json](W014-integer-valued-review-evidence/integrity-check.json).
