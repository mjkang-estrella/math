# Preregistration: finite class-number certificate

Frozen before the single run. No parameter search, no rerun under this
registration, and no use as a timing or factoring experiment.

## Purpose

Evaluate the finite maximal-order formula displayed by Schoof, printed
p. 245, at the two fundamental discriminants -23 and -115. Use the
resulting class numbers only to test whether an integer next to their
geometric mean annihilates both form class groups.

## Formula, copied before the run

For a maximal order of discriminant Δ ≠ -3, -4, Schoof displays

    h = 1/(2 - χ(2)) * sum_{0 < x < |Δ|/2, gcd(x,Δ)=1} χ(x),

where χ is the Kronecker symbol (Δ/·). The sum is over positive x only.
Both chosen discriminants are odd, so the upper bound is the integer
|Δ|//2.

Character rules fixed before the run:

- (-23/2) = +1 because -23 ≡ 1 (mod 8). For odd m coprime to 23,
  (-23/m) = (m/23). For general positive n = 2^v m, (-23/n) = (m/23).
- (-115/2) = -1 because -115 ≡ 5 (mod 8). For odd m coprime to 115,
  (-115/m) = (m/5)(m/23), because the two sign factors
  (-1/m) and the quadratic-reciprocity sign of (23/m) cancel.
  For n = 2^v m, multiply by (-1)^v, and return 0 if 5 or 23 divides n.

Legendre symbols at the odd primes 5 and 23 are Euler's criterion.

## Assertions

The run prints every summand. It must stop without rewriting this file if
any of the following fails:

1. There are φ(23)/2 = 11 summands for -23 and φ(115)/2 = 44 for -115.
2. The -23 evaluation equals 3.
3. The -115 evaluation is a positive integer; call it h115. Record it.
   Do not replace the discriminant or the formula if h115 is unexpected.
4. Let H = 3 * h115. Compare H with the squares surrounding it and record
   every nearest integer g. A tie records both integers.
5. If h115 is prime, both groups are cyclic of prime order, so a positive
   integer annihilates both groups exactly when 3 and h115 divide it.
   Record whether each nearest g has that property.

Budget: one process, at most 60 seconds, fewer than 20,000 arithmetic
operations. No seed, no corpus, and no second execution.

## Frozen source

The executed file is `class-number-certificate.py`. Its SHA-256 is recorded
in `class-number-certificate-freeze.json` before execution.
