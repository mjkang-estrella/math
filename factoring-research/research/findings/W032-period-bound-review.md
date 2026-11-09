# W032 label-period lower bound: independent symbolic review

**Disposition: ACCEPT the finite divisibility theorem and the uniform
large-factor obstruction for the specified order-(2R+1) canonical filter.
No mathematical correction to the frozen target is required. The proof
below makes the boundary, function-reduction, and uniformity steps explicit.
Verified complete factoring improvement: NONE.**

For every integer R>=2, every positive global function period S of
E(A)=C_R(A^2) modulo D=4^R(2R+1)! satisfies the stronger divisibility claim

    B_R := 2^(4R-s_2(R)-1-v_2(R))
           * product_(R+1 < ell <= 2R-3, ell prime) ell
    divides S.                                                    (1)

The empty product is 1. In particular S>=B_R. This is independent of
how S is obtained and does not require S to divide D. With the standard
prime number theorem, log B_R=(4 log 2+1)R+o(R). Consequently the stated
high-order filter cannot split sufficiently large composites with
leastprime(N)>=N^epsilon for any fixed epsilon greater than
alpha=log 4/(4 log 2+1). This includes balanced semiprime families.

## 1. Frozen scope and accepted interfaces

The complete target is the frozen
[lower-bound proposal](W032-period-bound-review-evidence/inputs/research/findings/W032-label-period-lower-bound.md).
The [brief](W032-period-bound-review-evidence/brief.txt) records the assignment;
the [input manifest](W032-period-bound-review-evidence/input-manifest.tsv)
identifies all 16 frozen local inputs by path, byte length, and SHA-256.
The target was first inspected during intake, then copied before substantive
proof checking. This review applies to those frozen bytes.

The accepted imports are the scalar diagonal and exact floor representation
from the scalar/carry review, and the high-order difference identity and
strict residual bound from the canonical-difference review, as accepted in
W032-W033-parent-disposition.md. Those interfaces are restated where used.
Their original implementations, symbolic programs, assays, and full evidence
packages were not reaudited or run. Read coverage and exclusions are recorded
in [read-scope.md](W032-period-bound-review-evidence/read-scope.md).

W032-exact-label-period.md was read only to identify the common-label contract
and distinguish this new proof from task factoring-w032-label-period-review-r1.
This review does not decide that algorithm's Newton test, greedy reduction,
implementation, cost, or returned period. No live task status was queried or
changed. The separate W033 ratio-sharing audit and the near-top order-(2R-1)
filter are outside this review.

All new mathematics here is symbolic prose. No candidate evaluation,
formal-polynomial program, numerical experiment, parameter sweep, assay
replay, Lean invocation, or project test was performed. Executed utilities
only inspected/copied files, retrieved/read the primary PNT paper, and
recorded/checksummed evidence. No delegation, install, commit, shared code,
Lean, STATE, or task-registry edit occurred. Only the assigned review and
its evidence directory were written.

## 2. Exact polynomial and meaning of period

For 0<=j<=R define

    P_j(Y) = product_(i=1..j) ((2i-1)^2-Y),   P_0(Y)=1,
    M_j = 4^(R-j) * (2R+1)!/(2j+1)!,
    a_j = M_j * [Y^(R-j)] P_j(Y).

Coefficients beyond a polynomial's degree are zero. The accepted diagonal
gives the integer polynomial

    E(A) = sum_(j=0..R) a_j A^(2j) = C_R(A^2).          (2)

Each factorial quotient in M_j is an integer. This definition of E is
independent of N, of any unit-domain restriction, and of a period algorithm.
A global period means

    E(A+S) = E(A) modulo D for every A in Z.            (3)

Every positive integer multiple of S is also a period, by iterating (3).
The proof uses that global property. E has D as a period because it has
integer coefficients. Its integer periods form an additive subgroup of Z;
thus its own minimal positive period divides D. This fact is not needed
to prove (1), and no relation between different label minima is assumed.

## 3. Forced power of two

The coefficient at j=R is

    a_R = product_(i=1..R) (2i-1)^2,

which is odd. For every j<R, M_j contains a factor 4 from 4^(R-j)
and the separate factor 2R in the product (2j+2)...(2R+1). Hence

    4*(2R) divides a_j for j<R.                        (4)

The j=0 derivative term is zero. For 1<=j<R, the term 2j*a_j in E'(1)
is divisible by 8*(2R). The leading derivative term is 2R*a_R and has
valuation v=1+v_2(R). All lower derivative terms have valuation at least
v+3, so they cannot cancel its odd unit part. Equivalently,

    E'(1) = 2R*(a_R+8k) for some k in Z,
    v_2(E'(1)) = v.                                   (5)

Counting the multiples of each power of two in a factorial gives
v_2(n!)=sum_(k>=1) floor(n/2^k)=n-s_2(n); the last equality follows by
expanding n in binary and summing each bit's contribution. Since
s_2(2R+1)=s_2(R)+1,

    d := v_2(D) = 2R+(2R+1)-s_2(2R+1)
                 = 4R-s_2(R).                         (6)

The integer binomial expansion of E(1+t) gives a polynomial B in Z[t]
with

    E(1+t)-E(1) = t E'(1)+t^2 B(t).                    (7)

For nonzero integer t with w=v_2(t)>v, the first term has valuation
w+v and the second has valuation at least 2w>w+v. This remains valid
when B(t)=0. Terms with unequal valuations cannot cancel at the smaller
valuation, proving

    v_2(E(1+t)-E(1)) = w+v.                            (8)

It remains to justify that the required w is available for every R>=2.
Write r=v_2(R). The elementary inequalities s_2(R)<=R and r<=R-1 yield

    d-2v-1 = 4R-s_2(R)-3-2r >= R-1 > 0.              (9)

Here r<=R-1 follows from 2^r<=R and 2^r>=r+1. Thus (9) includes R=2
without an exceptional calculation. In particular d-v-1>v.

If q=v_2(S)<=d-v-1, set t=2^(d-v-1-q) S. It is a positive integer
multiple of the global period S, and v_2(t)=d-v-1>v. Equation (8) then
gives valuation d-1, whereas periodicity at A=1 demands divisibility
by 2^d. This contradiction proves

    v_2(S) >= d-v = 4R-s_2(R)-1-v_2(R).               (10)

This proves a necessary exponent, without claiming equality or a sharp
minimum. The odd part of S is unrestricted in the argument.

## 4. Every prime in the stated band divides S

Fix a prime ell with R+1<ell<=2R-3 and put j0=(ell-1)/2. If the band
is empty there is nothing to prove. Otherwise ell is odd and

    2j0=ell-1>R,       j0<=R-2,
    ell<=2R+1<2ell,    ell^2>2R+1.                    (11)

The last inequality follows from ell>2 and 2ell>2R+1. Thus v_ell(D)=1.
When j<j0, 2j+1<ell; M_j retains that one factor ell and a_j=0 modulo
ell. When j>=j0, both factorials in M_j contain exactly one factor ell,
so M_j is nonzero modulo ell. This cancellation is performed in the
integer factorial quotient before reduction; no zero denominator is
inverted in F_ell.

Among the integers 1,...,ell-1, each pair {x,ell-x} has exactly one odd
member. Hence 1,3,...,ell-2 selects one representative from each pair
{x,-x} in F_ell^*. Their squares are distinct and give all j0 nonzero
squares. Each is a root of Y^j0-1, since x^(ell-1)=1 for x!=0.
The monic product of (Y-r) over these squares r equals Y^j0-1:
both have degree j0 and these j0 distinct roots. Thus in F_ell[Y]

    P_j0(Y) = (-1)^j0 (Y^j0-1).                       (12)

For j=j0, the requested coefficient has index h=R-j0. From (11),
2<=h<j0. It is a strict interior coefficient of (12), hence zero.
The excluded endpoint ell=R+1 would not justify h<j0; the proof does
not include that endpoint.

For j>j0 put m=j-j0. The remaining odd factors have values
ell,ell+2,...,ell+2(m-1), and therefore

    P_j(Y) = (-1)^j0 (Y^j0-1) Q_m(Y) modulo ell,
    Q_m(Y) = product_(s=0..m-1) ((2s)^2-Y).             (13)

Here h=R-j satisfies 0<=h<j0, so the Y^j0 part of (13) contributes
nothing to [Y^h]. Only its constant part contributes. As m>=1,
Q_m has the factor -Y at s=0. At j=R, h=0, proving a_R=0 modulo ell.
This does not conflict with a_R being odd in the two-adic argument.

At j=R-1, one has h=1 and m=R-1-j0>=1. The linear coefficient of Q_m
is exactly

    [Y] Q_m(Y) = -product_(s=1..R-j0-2) (2s)^2.       (14)

For an empty product this is -1. Otherwise every displayed 2s satisfies

    0<2s<=2R-ell-3<ell,                               (15)

using ell>R+1. No factor in (14) vanishes modulo ell. Combining (13),
(14), and the nonzero multiplier M_(R-1) shows

    a_(R-1) != 0 modulo ell.                          (16)

There is no cancellation among contributions to that coefficient in E:
each index j in (2) contributes only to the distinct monomial A^(2j).
The only potentially surviving terms now have j0<j<=R-1, with the last
one certified nonzero. We do not claim that every intervening coefficient
survives.

For such j put k_j=2j-(ell-1). At every nonzero A in F_ell,
A^(2j)=A^k_j by Fermat's identity. Both exponents are positive, so the
same equality also holds at A=0. The exponents k_j are distinct and

    2<=k_j<=K:=2R-ell-1<ell.                          (17)

The upper endpoint ell<=2R-3 ensures K>=2 and includes equality K=2.
The lower endpoint ell>R+1 ensures K<ell. Thus E induces the same
function on the entire field as

    f(A) = sum_(j=j0+1..R-1) (a_j mod ell) A^k_j,
    deg f = K,       2<=K<ell.                        (18)

Its leading coefficient is nonzero by (16). Were this function constant
with value b, the nonzero polynomial f-b of degree K<ell would have
ell roots, impossible over a field. This explicitly avoids inferring
nonconstancy merely from a nonzero polynomial of unrestricted degree.

Reduction of (3) modulo ell supplies f(x+S)=f(x) for every x in F_ell.
If S!=0 modulo ell, the ell translates x+nS, 0<=n<ell, exhaust F_ell.
Repeated use of the identity would make f constant, contradicting (18).
Consequently ell divides S. Since these primes are distinct and odd,
their product is coprime to the power of two in (10). This proves (1).

## 5. PNT consequence and its exact external dependency

Use natural logarithms and theta(x)=sum_(ell<=x, ell prime) log ell.
The external input is solely theta(x)=x+o(x) as x tends to infinity,
an unconditional prime number theorem. It is explicitly proved as
step (VI), page 707, in D. Zagier, *Newman's Short Proof of the Prime
Number Theorem*, American Mathematical Monthly 104 (1997), 705-708,
[author-hosted published paper](https://people.mpim-bonn.mpg.de/zagier/files/doi/10.2307/2975232/fulltext.pdf).
The checked formula, source fingerprint, and visual-verification record are
preserved; see
[source-check.md](W032-period-bound-review-evidence/source-check.md).
No effective error term, short-interval theorem, arithmetic-progression
estimate, or unproved hypothesis is being imported.

For R>=4 the exact band logarithm is

    log product_(R+1<ell<=2R-3) ell
      = theta(2R-3)-theta(R+1).

For R=2,3 the interval is reversed and the product is defined as 1;
the displayed theta-difference identity is not needed or asserted there.
As R tends to infinity the difference is R-4+o(R)=R+o(R).
Also s_2(R),v_2(R)=O(log(R+1)). Therefore

    log B_R
      = (4R-s_2(R)-1-v_2(R)) log 2 + R+o(R)
      = kappa R+o(R),      kappa=4 log 2+1.            (19)

Thus log S>=kappa R+o(R); the o(R) here can be chosen solely as a
function of R, uniformly over all periods S and all inputs N. It is a
lower-bound asymptotic, not an assertion that S has exponential rather
than factorial growth. Equation (1) itself uses no PNT.

## 6. Transfer to the high-order filter, uniformly in R

Take the accepted scalar branch: N>1 composite, leastprime(N)>2R+1,
and a_i=a0+iS in [0,N) with gcd(a_i,N)=1 for i=0,...,2R+1. For this
application S is a common global period of the two labels

    e(a)=[E(a)]_D,
    h(a)=[-F(N,a)*(N^(2R+1))^(-1)]_D,
    F(N,a)=sum_(k=0..R) N^(2k) C_k(a^2).

In particular it is a global period of E, so (1) applies. A period of
E alone is sufficient for the lower bound but does not itself establish
that h is fixed; that additional hypothesis is retained for the filter.

On a common-label progression the accepted floor formula gives

    d_R(a_i)=J(i)+floor Q(i) modulo N,
    J(i)=(C_R(a_i^2)-e)/D,
    Q(i)=e/D+hN/D+sum_(k<R) N^(2k-2R) G_k(a_i^2).

J has integer values at every integer i and rational-polynomial degree
at most 2R; Q has degree at most 2R-2. Replacing D by S in the argument
a_i does not change these degree bounds or the fixed-label identity.
The order-(2R+1) filter therefore satisfies the imported exact identity

    gcd(Z,N)=gcd(c,N),       c in Z,       |c|<4^R.      (20)

The canonical interval requires (2R+1)S<N; this is necessary, not a
guarantee that a unit stencil exists. Hence log N>log S>=log B_R.
Along unbounded R, (19) gives

    4^R < N^(alpha+o(1)),       alpha=log 4/kappa<1/2. (21)

The strict comparison alpha<1/2 follows from
2 log 4=4 log 2<4 log 2+1, without a numerical approximation.

For complete uniformity, fix epsilon>alpha and choose delta>0 so small
that kappa-delta>0 and beta:=log 4/(kappa-delta)<epsilon. From (19)
there is an integer R0>=2 such that log B_R>=(kappa-delta)R for all
R>=R0. Every width-admissible such R then satisfies

    R log 4 <= beta log B_R < beta log N < epsilon log N.

For 2<=R<R0, one instead has R log 4<R0 log 4. Choose N_epsilon>1
with epsilon log N_epsilon>R0 log 4. Then for every N>=N_epsilon and
every admissible R>=2 simultaneously, whether bounded, unbounded, or
oscillating with N,

    4^R<N^epsilon.                                    (22)

If leastprime(N)>=N^epsilon, a nonzero c in (20) has absolute value
smaller than every prime divisor of N, so gcd(c,N)=1. If c=0, the gcd
is N. Neither is a proper split. This is valid for arbitrary composite
N on the stated branch, including prime powers and repeated factors.
The depth R=1, not covered by (1), has Q constant and c=0 under the
accepted high-order theorem, so it supplies no exception to this filter
conclusion. No claim at epsilon=alpha follows from this argument.

For balanced semiprimes N=pq with min(p,q)>=c0*sqrt(N) for a fixed
c0>0, choose any alpha<epsilon<1/2. Then
c0*N^(1/2-epsilon) tends to infinity, giving
leastprime(N)>=N^epsilon for all sufficiently large N. This proves the
stated balanced-family consequence. Denominator-unit and whole-stencil
unit hypotheses are still those of the filter; initial gcd exits remain
distinct successes and are not contradicted by this conclusion.

## 7. Disposition, limits, and next meaningful change

All requested checks pass. The proof forces the stated power of two and
each prime in the exact open/closed band, verifies the surviving leading
coefficient after function reduction including A=0, and supplies a uniform
N threshold for each fixed epsilon>alpha. The finite statement is stronger
as divisibility (1) than as the requested numerical lower bound.

The hoped-for saved work was a narrower canonical stencil after compressing
global carry-label periods. This theorem leaves compression possible but
shows that its necessary width still makes the final residual smaller than
every prime factor in the stated large-factor regime. Even the smallest
common global label period cannot remove that particular obstruction.

This is an exponential necessary period bound, not factorial-scale
necessity, a sharp period formula, or a period-algorithm performance bound.
It gives no new complete factoring runtime and no improved GNFS comparison.
It does not exclude all smaller-factor families, individual digits and their
gcds, the near-top filter, other difference orders, unit-domain-only periods,
accidental fixed labels on a selected finite stencil, wrapped selectors,
changed scalars, arbitrary consumers, or all factoring algorithms.
In particular the translation argument on F_ell requires a global period;
it must not be transplanted to an input-restricted notion without proof.

A computation that could change this disposition would relax global label
equality, retain a different surviving signal, or change the scalar. Its
exact carry identity, lawful canonical acquisition, useful separating yield,
and complete paid costs would require a new argument. No numerical test is
needed to decide the proved theorem, and no new assay is proposed here.
**Verified complete factoring improvement remains NONE.**

## Delivery integrity

[validation.md](W032-period-bound-review-evidence/validation.md) and the
associated comparison logs record archival checks and action scope.
[delivery-manifest.tsv](W032-period-bound-review-evidence/delivery-manifest.tsv)
lists every payload, including this report, with its project-relative path,
byte length, and SHA-256. The manifest and
[terminal-manifest.sha256](W032-period-bound-review-evidence/terminal-manifest.sha256)
are excluded from the payload list to avoid circular hashing. Together with
the listed payloads they are the complete delivery. The exact finalized
manifest hash is also returned outside the files in the terminal handoff.
No report or payload is changed after sealing. These hashes establish byte
identity relative to that external anchor, not mathematical correctness.
