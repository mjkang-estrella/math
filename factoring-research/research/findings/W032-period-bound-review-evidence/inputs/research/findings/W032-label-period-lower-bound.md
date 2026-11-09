# W032: unavoidable factors in every exact label period

Parent symbolic derivation, 2026-10-08. **Not independently reviewed.**
No experiment or program evaluation. Verified complete improvement: **NONE**.
This is a new argument after the exact-period algorithm was delegated;
it is not silently included in that review's frozen target or accepted scope.

Let R>=2, D=4^R(2R+1)!, and E(A)=C_R(A^2) from the accepted diagonal.
Any common label period S is, in particular, a positive function period
of E modulo D. Here is a proposed lower bound on every such period:

    S >= 2^(4R-s_2(R)-1-v_2(R))
         * product_(R+1 < l <= 2R-3, l prime) l.          (1)

The product is 1 for an empty band. A period need not be a divisor of D
for this necessary bound, although the minimal period is. Both arguments
below concern all integer inputs; the exact-period algorithm has this
contract. A period only on a specially selected unit domain is different.

## The power of two from a local derivative

Write j for the index contributing the monomial A^(2j) in E. Its integer
coefficient is

    [D/(4^j(2j+1)!)] * [Y^(R-j)] prod_(i=1..j)((2i-1)^2-Y).

The leading coefficient at j=R is the odd number prod_(i=1..R)(2i-1)^2.
For every j<R, the displayed multiplier contains both 4 and 2R: the
factorial quotient includes 2R, and 4^(R-j) includes 4. Consequently
every lower coefficient is divisible by 4*(2R). Differentiation at A=1
introduces the additional factor 2j, so lower derivative terms are
divisible by 8*(2R). It follows exactly that

    v_2(E'(1)) = v = 1+v_2(R).

The modulus has exponent

    d=v_2(D)=2R+v_2((2R+1)!)=4R-s_2(R),

where s_2 counts binary ones. If t is an integer with v_2(t)>v, the
integer-polynomial Taylor identity E(1+t)-E(1)=t E'(1)+t^2 B(t)
implies

    v_2(E(1+t)-E(1))=v_2(t)+v.                         (2)

Indeed the second term has strictly higher valuation than the first.

For R>=2, d-v-1>v. To see this, write R=2^r u with u odd: the small
R=2 boundary satisfies it directly, and the elementary bounds
s_2(R)<=R and r<=R-1 give 4R-s_2(R)-3-2r>=R-1>0 for R>=2.
Suppose a period S had v_2(S)<=d-v-1. Multiply S by a power of two to
obtain another period t with v_2(t)=d-v-1>v. Equation (2) then gives
valuation d-1, contradicting E(1+t)=E(1) modulo 2^d. Therefore

    v_2(S)>=d-v=4R-s_2(R)-1-v_2(R).                   (3)

This does not assume that equality is attainable, and does not identify
the whole minimal period. Odd coefficients in t do not affect (2).

## Each prime in a band forces its own period factor

Fix a prime l with R+1<l<=2R-3, and put j0=(l-1)/2. Then l is odd,
v_l(D)=1, j0<=R-2, and R<l-1. Reducing E's integer coefficients modulo l:

- If j<j0, the multiplier D/[4^j(2j+1)!] is zero modulo l.
- At j=j0, the odd residues 1,3,...,l-2 represent one element from each
  pair {x,-x}; their squares are exactly the nonzero quadratic residues.
  Hence the product polynomial is a nonzero scalar times Y^j0-1.
  Its coefficient at h=R-j0 lies strictly between degrees 0 and j0,
  so this contribution is also zero.
- If j>j0, the same product is a nonzero scalar times

      (Y^j0-1) * product_(s=0..j-j0-1)((2s)^2-Y).

  We need degree h=R-j<j0, so only the constant part of the first
  factor contributes. The s=0 factor is -Y. In particular the j=R
  contribution h=0 vanishes. The j=R-1 contribution h=1 is nonzero:
  it is a nonzero scalar times product_(s=1..R-j0-2)(2s)^2,
  with an empty product equal to 1. All these residues are nonzero.

Thus the surviving monomials have j0<j<=R-1, and the top surviving
one j=R-1 has a nonzero coefficient. As FUNCTIONS on F_l, replace
A^(2j) by A^(2j-(l-1)); both exponents are positive, so the replacement
also holds at A=0. The resulting even exponents are distinct and lie
between 2 and 2R-l-1, which is less than l. Therefore E induces a
nonconstant function: its reduced polynomial has degree less than l
and a nonzero positive-degree coefficient.

If a period S were nonzero modulo l, repeated translation by S visits
every element of F_l. Periodicity would make E constant there, contrary
to the preceding polynomial argument. Hence l divides S for every
prime in this band. These odd factors are coprime to the power in (3),
proving (1) if all the stated coefficient reductions pass review.

## Consequence for this changed filter, and its limits

The standard prime-number-theorem Chebyshev estimate theta(x)=x+o(x)
would give log(product in (1))=R+o(R). Together with (3), this yields

    log S >= (4 log 2+1+o(1))*R.

The exact finite bound (1) needs no asymptotic prime estimate. Under
the displayed asymptotic estimate and canonical width (2R+1)S<N,

    4^R <= N^(alpha+o(1)),
    alpha = (log 4)/(4 log 2+1) < 1/2.

Thus for any fixed epsilon>alpha, sufficiently large input families
with leastprime(N)>=N^epsilon cannot split by the high-order filtered
gcd, EVEN AFTER replacing D by the smallest common label period. Bounded
R is separately harmless because 4^R stays bounded. A uniform argument
can split at a fixed R threshold and use the asymptotic bound above on
the remaining depths. Balanced semiprimes with both factors of order
sqrt(N) satisfy this condition eventually.

This is weaker than the old N^o(1) obstruction under step D. It does not
prove factorial-scale minimal periods, address all smaller factor sizes,
or constrain individual digits, lower-order filters, wraparound schemes,
input subsets, or unrelated computations. It rejects a specific hoped-for
escape for balanced inputs if independently accepted. The next meaningful
change would have to relax global label equality, retain a different
signal, or change the scalar rather than merely compress this period.

The exact prime interval and inequalities, the Newton test's distinct
scope, and the PNT-based implication require independent audit before
acceptance. No new complete factoring runtime is obtained.
