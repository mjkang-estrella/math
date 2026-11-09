# W031 normalized screen: parent disposition

Accepted with the corrections below. Verified complete factoring improvement:
**NONE**. The original reversed-jet identity has independently passed review,
so the continuation review's provisional imported dependency is satisfied.
The full 126-line report was read. All 19 payload hashes and sizes match;
the delivery manifest matches the external terminal SHA-256
`662892856e2f681371e96a79eb0299acd8a8026955254f9e218a8bd75c16bfad`.
See `W031-screen-parent-intake-hashes.json`. No numerical experiment ran.

Accepted results:

- Raw precision N^(2r+2), exact division by N, unit normalization, subtraction
  of correctly lifted lower terms, and exact division by N^(2r) recover c_(j,r).
  The lower c_(j,h) must be known modulo N^(2(r-h)+1), not merely modulo N.
- The staged 37 example requires the extra 7-unit condition. For q=7 the
  initial raw coefficient is not divisible by N. Direct gcd(N,37) remains
  legal, while a checked denominator can find 7. Use prime q>37 when comparing
  against the least-factor raw onset.
- The soft (K+1)(R+1) matrix cost is raw acquisition. A conservative complete
  staged normalization costs an additional factor R+1. A direct recurrence
  c_(j,r)=((2j-1)^2*c_(j-1,r)-c_(j-1,r-1))/(4(2j)(2j+1)) instead supplies the
  same separate-gcd screen in soft (K+1)(R+1) modular work, with checked units
  and O(R+1) streamed residues. This does not improve its prime coverage.
- Numerator log-height H bounds covered primes in (P,2P] by H/log P.
  Universal semiprime splitting requires covering all but at most one such
  prime, not necessarily every prime. Under uniform caps and P>2K+1,
  H/log P < pi(2P)-pi(P)-1 gives two missed primes and a missed semiprime.
  The reviewed Rosser--Schoenfeld bound makes H>3P/5-log P necessary.
- Parameter volume V=(K+1)(R+1) must be Omega(sqrt(P/log P)) for that
  coverage. This is a work/storage obstruction for the literal dense matrix
  implementation only, not a runtime lower bound for all generators.
- Fresh uniform field points obey d/p for a nonzero degree-d polynomial;
  uniform units obey d/(p-1). Identically zero components require a separate
  coefficient-content check, and full gcd N is not itself a split.

The rejected assumption is that isolated large prime divisors of universal
coefficients imply broad coverage. W032 changes the computation to an
input-dependent scalar and retains canonical carries, so it is outside
this fixed-numerator argument. Its acquisition, exact digit identities and
factor yield are separate obligations under two live W032 tasks. This
disposition accepts no improved complete factoring bound.
