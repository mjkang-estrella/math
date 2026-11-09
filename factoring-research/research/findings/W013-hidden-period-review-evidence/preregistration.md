# W013 hidden-period review: fixed exact certificate

Written before creating or executing the certificate. This is proof evidence,
not a candidate factoring benchmark. Standard-library integer/Fraction arithmetic
only; no parameter, prime, timing, or replacement-instance search. All writes
remain in `research/findings/W013-hidden-period-review*`.

The proof audit already establishes that the signed interval is translated by
`e+E=kB+j`; component order at least B makes a global baby match unique even
modulo a covered prime; and a nonzero leaf difference with nonunit gcd reveals
a proper divisor of an arbitrary composite. Fixed-degree integer-root recovery
is paid by exact finite-difference sign subdivision and binary search (described
in the report), not by trial division or factoring polynomial coefficients.

## Fixed cases

1. Lower signed endpoint: N=15, alpha=2, B=2, X=3, H=1, q=2,
   A(h)=9, E=1. True e=-1, global recovery gives 3; exponents are negative.
2. Upper signed endpoint and short last giant block: same parameters, A(h)=11.
   True e=1 lies in the last chunk; its extra baby position is retained/charged.
3. E=0 and composite q: N=35, alpha=2, B=3, X=5, H=1, q=3,
   A(h)=21. Component order modulo 7 equals B; global recovery gives 5.
4. Vacuous baby-order loop, p=2 and non-semiprime: N=12, alpha=5, B=1,
   X=2, H=1, q=1, A(h)=6, E=0. Global recovery gives 2.
5. Prime-power input: N=27, alpha=2, B=2, X=3, H=1, q=1,
   A(h)=9, E=0. Global recovery gives 3.
6. Wrong global match must be paid and removed: N=35, alpha=2, B=3,
   X=5, H=1, q=1, A(h)=7, E=5. The k=0 global match has e'=-4
   and no root; the true k=1,j=2 collision survives; batch gcd succeeds.
7. Necessary component check, deliberately invalid bypass: N=21, alpha=2,
   B=4, X=3, H=1, q=1, A(h)=7, E=2. ord_N(alpha)=6>=B,
   but gcd(alpha^2-1,N)=3. If that check is deliberately bypassed, the
   true k=0,j=2 collision globally matches j=0; both giants can be removed
   without recovering a root in this block. Correct precheck returns 3.
8. Squarefree full-product collision: N=35, alpha=2, B=3, retained giants
   2^3 mod 35 and 2^4 mod 35. At beta_0=1 the product gcd is N,
   with proper leaf gcds 7 and 5. No full-modulus baby match exists.
9. Prime-power full-product collision: N=49, alpha=3, B=2, retained giants
   3^6 mod 49 and 3^12 mod 49. At beta_0 the product gcd is N, with
   both leaf gcds 7. Also check two copies of 3^6 and its deduplicated list.
10. Repeated recovery root: N=49, alpha=1, B=1, X=7, H=1, q=1,
    A(h)=7-h, E=0. Recovery is -(x-7)^2; exact recovery returns 7.
11. Polynomial/block normalization: N=35, B(x)=2x^2+3x-4,
    A(x)=x^2+72x+114, C(x)=2x+3, b=-4, A'(x)=x^2+2x+9.
    Check polynomial identities, p=5,Q=7,e=72, shift X=5, and
    B_block(-X)=-4 != B_block(0)=61. Negating the normalized numerator,
    b, error and exponent handles b<0.
12. Zero cases: (A,B)=(N,x), (N+2,x), and (N+x,x), N=35.
    First two true-error recovery polynomials vanish; third is x(x-5)
    at p=5 and is nonzero. B=x-5 at p=5 separately checks that residual
    algebra remains defined while the rational ratio is undefined.
13. Exact exponent arithmetic for d=1,2,3,4 only. Check the formal
    unsaturated table 1/5,2/9,1/4,11/40; record E/H exponents; check
    the saturation-aware last entry 5/18 with active coordinates 2,3,4.
    These are arithmetic consistency checks, not denominator searches.

## Bounds and output

Thirteen named cases, fixed above. No input N exceeds 49; at most four giants
per consumer case and six powers for any order witness. Full-order witnesses
use only the explicitly supplied annihilating exponent and its prime divisors
(no trial order search). Each consumer case has one integer point in its block;
its public certificate is checked there by exact division. The tiny one-point
checks are fixtures, not a certificate generator or coverage-cost evidence.

At most 500 named assertions, polynomial degree at most four, at most 64 integer
bits per input/intermediate in the fixed arithmetic cases. The script must fail
closed if those bounds are exceeded. There is no timing measurement. Preserve
stdout JSON, stderr and exit status even on failure; do not replace a failed
case. Expected gate failure in case 7 and undefined ratio in case 12 are controls,
not failures of the conditional theorem. Root checking for these fixtures may use
only direct exact linear/quadratic formulas; the general fixed-degree root
algorithm is audited mathematically, not claimed implemented by this certificate.
