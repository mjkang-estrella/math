# W029: exact formal invariant, scalar derivative route rejected

Read the [review](W029-frobenius-degree-review.md) in full (239 lines), the
entire certificate source, its freeze record and all output rows. Accept
the semiprime component-degree formula and the normalized derivative
identity. Reject the derivative's scalar gcd test as a new mechanism:
for unit x,

    H_N(x)=(F_N(x)-G_N(x))/(2x)=-2*U_(N-1)(2,4x) mod N.

It is already base-ring evaluation data of the companion circuit output.
The companion Frobenius identity is
G_N=(1-4X)^((p-1)/2)*G_q(X^p) modulo p. This resolves the proposed
information gain without relying on a broad hardness claim or an unchecked
prior-art classification. W001-algebra Card D is the local antecedent.
**Verified complete factoring improvement: NONE.**

For distinct odd primes p,q, put

    g_plus=gcd(p-1,q-1), g_minus=gcd(p+1,q+1),
    Z=(g_plus+g_minus)/2-2.

Accept the exact count Z of zeros of H_N over each prime field and the
uniform-x proper-gcd probability

    (Z/p)*(1-Z/q)+(Z/q)*(1-Z/p).

The reciprocal-pair parametrization accounts for the two excluded torus
elements, and the exceptional x values give nonzero H_N. For p=5 and a
prime q=7 modulo 12, Z=0; N=35 is the explicit smallest recorded example.
This is failure of the H_N gcd test. A separate gcd(x,N) preprocessing test
has its own small success probability and is not counted in this formula.
No distributional statement about random primes or typical gcd sizes is
accepted without a specified distribution and proof.

Keep the review's other claims narrow:

- If p^k exactly divides general odd N, deg(F_N mod p)=(N-p^k)/2.
  This does NOT imply the asserted top-degree recovery modulo nonsquarefree
  N. Nilpotent coefficients matter: F_9 modulo 9 has degree 3, whereas
  F_9 modulo 3 is constant. Indeed its X^3 coefficient is -7680=6 mod 9
  and its X^4 coefficient is 2304=0 mod 9. The semiprime claim stands;
  the proposed general top-index extension is not adopted.
- Frobenius on a general finite quotient ring is an endomorphism. Calling
  it an automorphism requires the appropriate reduced/finite-etale
  hypothesis. Extensions change the observation model; their known
  Frobenius relation is not a proof that all extension methods fail.
- The first nonzero formal Hasse derivative modulo p has order p in the
  stated semiprime family. Dense jets of that precision cost p coefficients
  per stored jet. This is a cost for that implementation, not a lower bound
  for every high-index derivative algorithm.
- The listed higher normalized derivatives depend on existing pair-power
  data at the stated unit arguments, with the derivative order and public
  coefficient work paid. Do not promote this functional dependence to
  'no other cheap invariant is left' or a lower bound for processing many
  evaluations. The proof using inverses of 1-4x needs that unit condition.

Evidence: all 13 frozen input checks and the frozen certificate source
match. No complete child delivery manifest or external manifest anchor
was supplied; the parent separately inventories the delivered report and
evidence in [intake](W029-parent-intake-hashes.json). The single recorded
run used 4,634 charged events, retained all rows, and has no mismatches in
C1–C5. The source's status field does not itself assert every prediction;
the parent inspected those rows. Events count selected operations, not
all arithmetic or bit cost. No run was repeated.

The formal degree remains a factor-bearing invariant with no cheap
acquisition. Main constructive work has moved to W030's uncarried digit
representation of pair roots and an actual digit-cut product recursion,
which do not depend on this derivative test succeeding.
