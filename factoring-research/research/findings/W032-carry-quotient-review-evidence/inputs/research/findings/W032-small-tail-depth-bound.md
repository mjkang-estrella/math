# W032: small-tail filtering restores a subpolynomial residual bound

Parent symbolic derivation, 2026-10-08. **Unreviewed.** No experiment.
Verified complete factoring improvement: **NONE**. This goes beyond the
live unit-step algebra/cost review; do not treat its completed scope as
acceptance of this new conclusion.

The new unit-step evaluator has y_i=sigma_i+[P(a_i)-sigma_i]_D, where
P(A) is a polynomial modulo D of degree at most 2R-2. Consequently
y_i=P(a_i) modulo D for every i, even where the sign changes. For
m=2R+1 and a_i=a0+i, polynomial annihilation gives

    Delta^m y / D = c in Z,             |c|<4^R.        (1)

The strict bound follows from |Delta^m y|<D*4^R proved in the original
proposal. Since gcd(D,N)=1, gcd(Delta^m y,N)=gcd(c,N). Thus the factor D
in that proposal's residual bound does NOT increase its useful argument.
This exact division is an additional computation, not an assumed inverse
of D before proving integer divisibility.

## The exact guard itself limits depth

Assume R>=2 and every point in a full consecutive stencil satisfies
|epsilon(a_i)|<1, where

    epsilon(A)=sum_(k<R) N^(2k-2R) C_k(A^2).

Let d=2R-2. Its leading coefficient is L_R/N^2, with

    L_R=4*(2R)*(2R+1)*product_(j=1..R-1)(2j-1)^2 > 0.

This is the j=R-1 leading coefficient of C_(R-1), since
D/D_(R-1)=4*(2R)*(2R+1). The degree-d forward difference is exactly
d!*L_R/N^2. Apply it to the first d+1 points of the larger stencil.
All their epsilon values have absolute value less than 1, so the sum
of absolute binomial weights gives

    d!*L_R/N^2 < 2^d,
    N^2 > d!*L_R/2^d.                                (2)

This holds regardless of a0 and the signs, and does not require the
stronger conservative max-coefficient guard. No probability assumption
or modular root bound is used.

Put t=R-1. Since (2t)!>=(t!)^2 and product_(j=1..t)(2j-1)>=t!,
the right side of (2) is at least 4*(2R)*(2R+1)*(t!)^4/4^t.
Elementary factorial growth therefore implies

    log N >= (2+o(1))*R*log R,
    R=O(logN/loglogN),             4^R=N^o(1),         (3)

uniformly along legal growing-depth stencils. Bounded R gives the same
subpolynomial conclusion directly; a uniform proof can use the same
split-at-sqrt(logN) argument as earlier factorial-width reviews.

Combining (1) and (3), for any fixed epsilon0>0 and sufficiently large
N with leastprime(N)>=N^epsilon0, this small-tail filtered gcd cannot be
proper. c=0 gives N; any nonzero c is smaller than the least prime factor.
R=1 is separate: P modulo D is constant zero, epsilon=D/N^2>0, y=0,
and the filtered gcd is N whenever the guard holds. Initial nonunit exits
and individual digit gcds remain separate channels.

This rules out a particular scalar-free small-tail amplifier if reviewed,
not unguarded carry quotients, other output channels, or factoring. The
exact failed assumption was that avoiding factorial stencil spacing would
also avoid a factorial depth restriction. The small-tail guard imposes
one through its high finite difference, even on a unit-spaced stencil.

The constructive replacement is to compute the full lower-digit remainder
and its exact finite-difference quotient with no small-tail guard. A
separate note supplies that computation and its coefficient recurrence;
the larger possible depth alone will not establish useful factor yield.
