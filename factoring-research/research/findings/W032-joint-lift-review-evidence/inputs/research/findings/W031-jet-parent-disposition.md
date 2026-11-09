# W031 reversed-jet audit: parent disposition

Accept the scoped mathematical core of the [independent review](W031-reversed-jet-review.md).
The parent read the complete 359-line report. **Verified complete factoring
improvement: NONE.** No numerical certificate or new Lean theorem was needed.

The matrix identity and truncated powering are exact. Extracting a_j means
reading trace coefficient 2j+1 and multiplying by the INVERSE of 2 modulo
N^2. A canonical modular residue need not be even, so integer halving is
invalid. Removing z means shifting coefficient indices, not inverting z.
The proposed modulus z^(2K+3) suffices; z^(2K+2) is already enough.

The coefficient formula, legal division by N and universal normalized
residue all hold. For j<(p-1)/2, where p is the least prime factor, raw
gcds are N and the stated normalized residues are units. Their values
determine the entire raw coefficient modulo N^2. This exhausts only
that precision and those gcd observations. It does not exclude the
parent's separate [higher-precision continuation](W031-higher-precision-prime-screen.md),
which can expose other universal numerators such as 37.

Accept the new valuation extension, separately from formal component degree.
At j=(p-1)/2 the factorial denominator has p-valuation one, whereas every
numerator factor ((2i-1)^2-N^2) is a p-unit. Larger prime divisors of N
divide neither numerator nor denominator. Therefore, for arbitrary odd
composite N,

    gcd([t^((p-1)/2)]J_N, N) = N/p.

Earlier raw gcds are N. This includes prime powers; it does NOT revive
W029's rejected top-index inference over a nonreduced ring. For N=p^e,
the order modulo p is (p^e-1)/2 even though a proper raw gcd already
appears at (p-1)/2. The report's worked N=9 coefficients confirm the
distinction symbolically. For prime N the last gcd is 1, not a factor.

A dense geometric jet search has Theta(p) explicit coefficient traffic
and soft O(p*bitlen(N)^2) bit cost using the stated fast arithmetic. This
is a computation, but worse than the already-paid soft sqrt(p) small-factor
product method. A polynomially described matrix is not a free order-of-
vanishing oracle. Resident coefficient arrays cost O(K*bitlen(N)) bits;
total fast-arithmetic workspace needs its chosen routine's additional space.
No global lower bound on other circuit consumers is accepted.

All 15 manifest payloads and 10 frozen inputs match. The manifest matches
both the external terminal anchor and the local anchor file; the delivery
contains 17 files when those two inventory files are included.
[Parent intake](W031-jet-parent-intake-hashes.json).

The higher-precision extraction and restricted prime-coverage count have
a separate live task in tasks-W031.json. Main constructive work should
seek a paid computation outside the fixed coefficient-gcd screen, not
repeat a finite check of these already settled jet identities.
