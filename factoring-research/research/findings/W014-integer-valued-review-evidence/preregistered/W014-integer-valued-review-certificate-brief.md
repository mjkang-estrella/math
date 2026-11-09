# Fixed exact algebra certificate — preregistration

This file and the certificate source are frozen and hashed before execution.
The analytic proof is the evidence for the theorem; these five predetermined
cases check arithmetic and expose invalid extensions. This is not a performance
experiment, a factoring attempt, or a parameter/prime/degree sweep. No random
seed, adaptive replacement, timing comparison, or unrecorded trial is permitted.
Every case, failure and exception will appear in the output. One execution only.

1. **Transfer and noncancellation.** Fix N=15, p=3, X=2, q=1,
   A(h)=h(h-1)/2, M=2 and alpha=2. Compute A(-1), e, D,
   M(D-e), both alpha and beta powers modulo p (negative exponents included),
   and all coefficients and the true-root value of
   F(x)=x(P(x-X)-M e)-M qN. Check integral negative-offset evaluation,
   powered equality, failure of unpowered equality and nonzero F(0).
2. **Order annihilation.** On the same N and alpha, use a degree cap 4,
   so the common denominator choice is M=4!=24. Verify alpha has order 4
   from its powers at 1,2,4; verify beta=alpha^24 is the identity. With
   M=2, verify the order is 2. These are fixed exponent checks, not searches.
3. **Dense affirmative instance.** Fix X=10^6, N=X^2, q=1, L=8, d=2,
   E=64/X and A(h)=X-h. Retain all nine exact grid values/errors,
   second differences, the density guard, and the exact A1 left side.
4. **Drop integrality only.** At the same X,N,q,L,d, take
   A(h)=X-h+h^2/X and E=512/X^2. Retain all nine values/errors and guards.
   Verify the nonaffine polynomial satisfies density and A1 but is not
   grid-integer. This is not a counterexample to the actual theorem.
5. **Drop density only.** At the same X,N,q,L and E as case 3, take
   A(h)=X-h+binomial(h,9), with actual degree d=9. Retain all nine
   values/errors, A1 and the density guard. Verify A1 and grid integrality,
   while the polynomial is nonaffine and L<2d^2. Retain A(9), which
   distinguishes it from the affine polynomial outside the grid.

All arithmetic uses Python standard-library integers and fractions. Iteration
over the nine grid points is evaluation of the prescribed certificate, not
a search over problem parameters. The output records exact rationals as strings.
If a check fails, the report must retain and explain it; no case replacement.

Success criterion: all five case-specific claims hold exactly. No percentage
from this certificate is an empirical success law for factoring or a proof of
the universal analytic theorem. Verified complete factoring improvement: NONE.
