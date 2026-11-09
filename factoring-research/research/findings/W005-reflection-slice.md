# W005 — parent screen of short-direction reflection on the twin shell

Date: 2026-10-08. Parent symbolic deduction from the accepted B/D identities;
not separately reviewed or formally verified. No numerical execution.
Verified new complete factoring improvement: NONE.

A concrete alternative to scanning every binary slice is:
given primitive integer A of odd norm N, choose B0=i*A, enumerate short nonzero
integer C perpendicular to A, put c=Norm(C), b=<C,B0>, and test c|2b.
If m=-2b/c is integral, B=B0+m*C is automatically integral, orthogonal to A,
and has norm N. Check the at-most-twelve unit exceptions and extract the
content gcd. LLL can prioritize short C, but all enumeration remains charged.
This replaces a quadratic discriminant-square test with one divisibility test.

There is a sharp local cost gate, stronger than a vague low-density objection.
If gcd(c,N) is proper, it already factors N. On the unit-c branch, B's
right gcd with B0 has norm gcd(N,2b)=gcd(N,m), by the accepted
single-reflection theorem; B0 and A have the same right kernel at each
prime power, so the same splitting test applies to A.

Cauchy gives |m|<=2*sqrt(N/c). A nonexceptional B must have a proper right
gcd with A by the accepted twin theorem, so m is nonzero and |m|>=p,
where p is the smallest prime factor. Therefore necessarily

    c <= 4N/p^2.                                           (1)

For balanced semiprimes p<q<2p, this forces c<8. Thus all useful outputs of
this unit-norm-direction generator come from a fixed, finite set of very
short integer directions. Typical reduced-lattice directions of norm around
N^(1/3) cannot supply a useful twin through a single integral reflection.
Small-direction exceptional inputs remain possible; no universal failure or
general shell lower bound is claimed. If gcd(c,N)=N, the unit theorem does
not apply; that branch already requires c>=N and needs a different argument.

The failed assumption was that shortening the direction makes the integral
reflection coefficient easier to use. It makes that coefficient too small
to contain an unknown factor. For c satisfying (1), acquiring a useful
divisible coefficient is still the work, and the same factor is visible
directly in gcd(m,N).

A materially different operation would allow two rational reflections with
only their FINAL vector integral; their difference from B0 need not be a
scalar times one norm-unit direction. This is not a supplied escape algorithm:
one must explicitly generate the two directions, enforce final cancellation,
bound all heights and denominator checks, and show useful probability.
Requiring the whole product to be an integral lattice automorphism would
introduce an additional restriction and cannot be assumed to mix shell points.
Do not run a larger one-reflection/LLL sweep: inequality (1) already settles
the advertised balanced-input mechanism without an experiment.
