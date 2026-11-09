# W031 continuation: higher precision exposes a public prime screen

Parent derivation, 2026-10-08 local. No numerical run. **Verified complete
factoring improvement: NONE.** This develops a materially different consumer
of the reversed circuit while its original jet audit is running. The exact
coefficient formula has since passed that audit. The continuation is now
accepted with the repairs in [the parent disposition](W031-screen-parent-disposition.md).

## 1. Scope repair: the first raw coefficient is not all normalized data

W031's index (p-1)/2 is the first nonzero RAW coefficient of J_N modulo p.
It does not prove that every arithmetic operation on legally normalized,
higher-precision coefficients is uninformative until that index. The
following computation is a concrete reason to keep that distinction.

For 0<=j<=n=(N-1)/2, define the rational polynomial

    A_j(Y)=product_(i=1..j)((2i-1)^2-Y)/(4^j*(2j+1)!)
          =sum_(r=0..j) c_(j,r)*Y^r.

The proposed W031 formula is

    [t^j]J_N(t)=N*(-4)^n*A_j(N^2).

Assume 2j+1 is below the least prime divisor of N. Every denominator in
A_j is a unit modulo any power of N. Compute the raw coefficient modulo
N^(2r+2), using the same truncated matrix powering, divide by N exactly,
and multiply by (-4)^(-n) modulo N^(2r+1). This returns A_j(N^2) at that
precision. Subtract

    sum_(h<r) c_(j,h)*N^(2h)

using rational residues whose denominators are checked units, with c_(j,h)
known modulo N^(2(r-h)+1), not merely modulo N. The remainder
is divisible by N^(2r). Exact division, then reduction modulo N, returns
c_(j,r) modulo N. No inverse of N is used. Lower coefficients and all
inverses must be acquired and charged. A failed denominator unit check
may itself return a proper factor; it is not silently cancelled.

For j=3 the numerator polynomial before rational reduction is

    (1-Y)(9-Y)(25-Y)=225-259Y+35Y^2-Y^3.

Thus c_(3,1)=-259/(64*5040)=-37/46080. If N=37*q with q coprime to
2*3*5*7*37, computing this residue by the staged procedure and taking its
gcd with N returns 37. The direct c_(3,1) test does not need the extra 7
condition; the staged procedure needs it for the lower coefficient c_(3,0).
For example q=41 meets those conditions. The jet has degree only three,
well below (37-1)/2. These are exact symbolic identities, not a numerical
run or evidence of an asymptotic speedup. A direct gcd(N,37) is a cheaper
implementation of this same public-coefficient test.

## 2. What work the higher-precision route replaces

One matrix power modulo z^(2K+3) and N^(2R+2) acquires the necessary raw
jet for all j<=K and normalization depths r<=min(j,R). It avoids building
the enormous full polynomial of degree (N-1)/2. Its dense polynomial
operations cost soft O((K+1)*(R+1)*poly(log N)), with the O(log N) binary
powering factor included in the polynomial-log factor. The modulus has
Theta((R+1)*log N) bits. Claiming the larger N-adic precision as one
ordinary O(log N)-bit operation would erase its main cost.

Every test ultimately has the form gcd(N,numerator(c_(j,r))), after checked
denominators. These rational numbers are independent of N. The reversed
circuit is therefore one generator for a PUBLIC prime-divisibility screen;
it does not supply factor-dependent advice. They can also be generated
directly from the truncated products A_j(Y), with the chosen arithmetic
and rational coefficient widths charged. No claim that the matrix route
is their fastest generator is made. The matrix bound above is raw acquisition,
not the full staged normalization cost. The accepted review supplies a
conservative additional R+1 factor for generating all necessary high-precision
lower lifts, and a direct recurrence at soft (K+1)(R+1) modular cost for the
same separate-gcd screen. See the parent disposition for its precise scope.

## 3. A cheap coverage obstruction for this explicit screen

Fix bounds K>=1 and 0<=R<=K, and use the raw coefficients c_(j,r) for
0<=j<=K and 0<=r<=min(j,R), with no extra arbitrary combinations. The
coefficients of product((2i-1)^2-Y) alternate signs and are nonzero. Their
absolute values are at most

    product_(i=1..j)(1+(2i-1)^2) <= (1+4j^2)^j.

Reducing a rational coefficient only decreases its numerator's absolute
value. Consequently the sum of binary logarithms of all nonzero reduced
numerators in this screen is

    O((R+1)*K^2*log(K+1)).

The number of distinct covered primes in [P,2P] is therefore at most

    O((R+1)*K^2*log(K+1)/log P).

For P>2K+1 none of these primes comes from the checked factorial
denominators. Compared with the standard asymptotic count of primes in
[P,2P], covering every such prime requires

    (R+1)*K^2*log(K+1) = Omega(P).

For fixed R this already needs K at least sqrt(P) up to logarithms.
For the displayed dense matrix method write its explicit precision-volume
as V=(K+1)*(R+1). Since (R+1)*K^2<=V^2, a universal prime-cover certificate
from this family requires V at least sqrt(P) up to logarithms. This does
not beat the small-factor block-product scale by a fixed power using the
current dense method. Do not confuse this volume comparison with a lower
bound for every way of generating or combining these coefficients.

The obstruction is stronger than the 37 example's favorable behavior but
has a narrow scope. A family with insufficient coverage leaves many primes
in the dyadic range outside every tested numerator; two such primes give
a semiprime missed by this screen, provided the same upper K,R limits hold
through that input range. Adaptive selection of coefficients within these
bounds cannot add a prime outside their union. Arbitrary new linear or
nonlinear combinations, input-dependent evaluation points, and a different
implicit consumer are not included in this argument. Neither is any claim
that factoring itself needs sqrt(P) work.

## 4. Constructive escape and its first paid test

The failed assumption would be that a few unusually large prime divisors
of universal coefficients imply broad prime coverage. A different
computation could evaluate combinations at input-dependent points instead
of testing the fixed coefficient numerators separately. That genuinely
changes the tested integer family and escapes the coverage count above.

The immediate simple version has its own check: a nonzero polynomial of
degree d over F_p vanishes at at most d residues, so uniform random point
evaluation gives at most d/p probability of a zero at that component.
This applies only when the specialized polynomial is not identically zero;
its coefficient gcds should be handled first. It does not analyze biased
point selection, compact high-degree circuits or dependence on the other
CRT component. No improved selector or whole factoring bound is supplied.

Next validation is symbolic: check exact N-adic extraction and the
coefficient-height/coverage count, including the difference between the
actual screen and larger unanalysed combinations. Do not rerun the initial
matrix-jet audit or count favorable examples as a success law.
