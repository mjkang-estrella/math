# W032: exact carry quotients from a shared lower polynomial

Parent constructive derivation, 2026-10-08. **Accepted at the algebra and
primitive-cost level** in [the independent review](W032-carry-quotient-review.md).
No experiment in this note. Useful factor yield remains unproved.
Verified complete factoring improvement: **NONE**.

This removes the small-tail guard rather than treating its failed depth
condition as an oracle. Assume R>=1, N odd, and leastprime(N)>2R+1;
all denominator checks and any initial point gcds are paid. Let

The full check goes through 2R+1, including the omitted j=R denominator;
checking only the truncated recurrence's inverses is insufficient for the
imported digit/truncation theorem. Use actual unwrapped integer inputs and
recover the final signed sums over Z, not only modulo M. Let

    M=N^(2R),            m=2R+1,
    V_R(a) in [0,N*M),   d_R(a)=floor(V_R(a)/M),
    r(a)=[V_R(a)]_M.

The accepted W032 polynomial identity, reduced modulo M, says

    r(a)=[P_R(a)]_M,
    P_R(A)=sum_(j=0..R-1) b_j A^(2j) modM,
    b_j=N^(2j)*product_(i=1..j)((2i-1)^2-N^2)
                   / [4^j(2j+1)!] modM.             (1)

All displayed denominators are units. Terms j>=R vanish modulo M;
the accepted tail argument supplies this truncation, rather than falsely
asserting raw coefficient divisibility by N. There is no division by a
variable in (1). For original scalar comparisons, retain the stipulated
unit inputs; polynomial evaluation itself is defined on all residues.

## An exact integer quotient, not a numerical derivative

Take an unwrapped arithmetic progression a_i=a0+i*h of unit inputs,
0<=i<=m, with a canonical progression as a sufficient common scope.
The identity for V modulo N*M has degree at most 2R; (1) has degree
at most 2R-2. Therefore their order-m integer differences satisfy

    Delta^m V_R(a_i) = (N*M)*t,
    Delta^m r(a_i)   = M*c,             t,c in Z.

These statements follow by reducing an integer-coefficient representative
of each residue polynomial. No assumption on the canonical representatives'
ordinary polynomial shape is made. Since V=M*d_R+r exactly,

    Delta^m d_R = N*t-c,
    gcd(Delta^m d_R,N)=gcd(c,N),
    c = (sum_i (-1)^(m-i)*binom(m,i)*r(a_i))/M.        (2)

The numerator is exactly divisible by M, including for negative sums.
Because 0<=r(a_i)<M, the positive and negative weight totals are each
2^(m-1)=4^R, and

    |c|<4^R.                                        (3)

This proves the same useful residual bound for EVERY such unwrapped
progression, without equal carry labels, a large label period, or a
small-tail guard. With h=1 and R=Theta(logN), the width requirement is
only O(logN)<N. No useful factor probability is inferred from (3).

## Acquire all coefficients in linear recurrence work

Initialize b_0=1. For j=1,...,R-1 use

    b_j=b_(j-1)*N^2*((2j-1)^2-N^2)
                    *[4*(2j)*(2j+1)]^(-1) modM.     (4)

This is a concrete O(R) recurrence at O(R logN) bit width, with charged
unit inversions. Batch inversion can use prefix products and one inverse,
followed by a reverse pass, because every denominator is a unit. A
nonunit denominator triggers separately paid small-factor handling.
The precision of later coefficients can also be reduced using their
known N-adic powers, but that optional optimization is not needed here.

Constructing an integer-coefficient lift of P_R then needs O(R) residue
records. Monic multipoint evaluation at O(R) explicit a_i obtains all
r(a_i) without 2R+2 independent quadratic-algebra powers. Product and
remainder trees over Z/MZ require only monic polynomial division; no
inverse of a difference a_i-a_j is assumed. With fast integer/polynomial
arithmetic, a conservative bit envelope for this batch is soft
O(R^2*logN), plus setup, input reading, binomial weights and final gcd.
This compares to the imported soft O(R^2*(logN)^2) independent-scalar
batch bound. It is a primitive bound comparison, not a factoring-time
improvement. No fast multipoint implementation or benchmark is claimed.

One can also use Horner evaluation or finite-difference updates with their
larger honest cost. The explicit quotient numerator has
O(R logN+R+log(R+1)) bits; divide once by M, then gcd with N. All sign,
radix, reading and storage costs are retained. R is an N-only selected
parameter, not a hidden-factor input; any proposed polytime use must bound
R by poly(logN). The width in (1) is numeric 2R*logN, not constant width.

## Share starts rather than silently repeat their points

For K consecutive starts a0,...,a0+K-1 with h=1, acquire only K+m
residues r(a), since neighboring stencils overlap. Form all K weighted
sums as a convolution with the reversed signed-binomial kernel of length
m+1. Over the integers each output is exactly divisible by M. Fast
polynomial multiplication with enough signed coefficient width computes
all numerators in soft O((K+R)*(R logN+R+log(K+R))) bit work; point
evaluation has comparable soft linear dependence on K+R at modulus width
R logN. This is a supplied-start primitive with explicit data traffic,
not a free evaluation of exponentially many starts. Constructive sharing
removes a repeated factor of R relative to literal per-stencil work.

Initial point gcds and their failures, canonical endpoint checks, every K
output quotient and gcd, and batch localization if used must be charged.
Correlation among the K outputs is preserved. No independent-trial
probability can be asserted from overlapping stencils. A supplied K or
a favorable unbounded sequence of scales is not an all-input algorithm.

## Decisive next question

The actual computation is now a short rationally specified polynomial,
canonical reduction modulo a large power of N, and a normalized finite
difference of its residues. Increasing R enlarges the possible integer
quotient support exponentially while the acquisition stays polynomial in
R,logN per stencil. It does not show that those integers have any enhanced
chance of a proper common factor with N. Unit/full gcds and c=0 are failures.

First audit (1)-(4), the exact-divisibility scope, and the batch bit bounds.
Then a single preregistered small diagnostic can compare quotient support
and proper-gcd yield with paid ordinary random gcd arguments, retaining
all depth/guard failures. Such a finite run would only falsify obvious
degeneracy, not establish an asymptotic distribution or factoring bound.
No diagnostic is selected or executed in this note.
