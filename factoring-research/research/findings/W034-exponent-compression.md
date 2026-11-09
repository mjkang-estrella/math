# W034: price exponent compression before increasing the order cutoff

Parent symbolic analysis, 2026-10-08. **Unreviewed. No experiment.**
Verified complete factoring improvement: **NONE**. The first W034 audit
is independent and does not yet cover these additional deductions.

## Concrete replacement: lcm instead of product

The original E_k(N)=product_(j<=k)(N^j-1) repeats many cyclotomic factors.
An actual compressed candidate is

    L_k(N)=lcm(N-1,N^2-1,...,N^k-1).

Construct N^j successively and update L <- L/gcd(L,N^j-1)*(N^j-1)
with exact integer division. This needs neither factoring an exponent nor
knowing p or q. Its construction uses at most k gcds on O(k^2 logN)-bit
integers and explicit products; direct powering still pays the final
exponent's bit length. This is a concrete alternative, not a unit-cost
compressed exponent oracle.

For integer N>=2, the proposed exact identity is

    L_k(N)=product_(d<=k) Phi_d(N).                   (1)

Here is a valuation proof. For an odd prime ell not dividing N, let
r=ord_ell(N), e=v_ell(N^r-1). Then v_ell(N^j-1) is zero unless r|j,
and otherwise is e+v_ell(j/r). Factoring N^j-1 into its cyclotomic
values and inducting over divisors shows contributions e at d=r and
1 at d=r*ell^t (t>=1), with no others. The sum of those contributions
for d<=k is exactly the maximum valuation among j<=k. Primes dividing
N contribute neither side. For ell=2 and N odd, write e=v2(N-1),
f=v2(N+1). The cyclotomic contributions are e at d=1, f at d=2, and
1 at d=2^t for t>=2. Their partial sum is again the maximum valuation
of N^j-1 for j<=k, treating k=1 separately. This proves (1) primewise.

The polynomial version and its totient degree are classical, not a new
identity; see [Sanna, Remark 1.2 and Lemma 4.1](https://link.springer.com/article/10.1007/s40993-021-00242-4).
That source treats polynomial q-integers; the integer-specialization
valuation argument above is stated separately rather than assumed from it.

Moebius inversion gives

    log Phi_d(N)=phi(d)*logN
                +sum_(e|d) mu(d/e)*log(1-N^(-e)).

The error in this formula has absolute value at most 2, uniformly for
N>=2: use -log(1-x)<=2x for 0<=x<=1/2 and sum_(e>=1)2*2^(-e)=2.
Consequently

    log L_k(N)=logN*sum_(d<=k) phi(d)+O(k)
              =Theta(k^2 logN).

The totient sum's quadratic growth is also covered by the cited primary
source. Thus removing cyclotomic multiplicities changes a leading constant,
not the k^2 scale of exponent bits. Worse, L_k can have smaller prime-power
valuations than E_k; replacing E by L does not preserve every annihilation
condition of the original product. Their radical coverage agrees, their
full order coverage need not. No same-success speedup is inferred.

The elementary addition-chain observation is scoped: a straight-line
calculation that starts with exponent 1 and only adds/subtracts previous
formal exponents needs at least log2(E) steps to reach positive E. This
does not lower-bound arbitrary modular arithmetic exploiting identities
specific to N, nor provide a factoring lower bound.

## An exact local model for the remaining coverage cost

For a safe-prime component p=2*ell+1 with ell odd prime, and q nonzero
modulo ell, put

    A_ell(k)=sum_(d | ell-1, d<=k) phi(d).

These are exactly the nonzero residues q for which some q^j-1, j<=k,
vanishes modulo ell. Since E is even,

    gcd(E_k(pq),p-1)/(p-1)
      = 1     if ord_ell(q)<=k,
      = 1/ell otherwise.

Under the explicitly hypothetical uniform distribution on nonzero residues
q modulo ell, its exact mean is (1+A_ell(k))/ell. Since
A_ell(k)<=sum_(j<=k)j, this particular coverage model buys at most
quadratic-in-k local mass for a quadratic-in-k exponent length. This is
not a theorem about prime q, about adversarial semiprimes, or about the
full two-component splitting probability. It does identify why simply
raising k has no justified end-to-end advantage in that model.

## Constructive consequence

The failed assumption is that cyclotomic overlap might make a large order
cutoff cheap. Exact lcm construction resolves that question at the exponent
bit level. A useful next mechanism must instead select an input-dependent
small exponent that covers a substantial part of an actual component order,
or share the consumption of many separate exponents without materializing
their product. Partial annihilation can be followed by an explicitly paid
small-order collision search; it is not free complete annihilation.

The next mathematical task is to price a schedule of separate exponents
and its collision consumer, including full-gcd recovery, against one product
exponent. Merely describing such sharing as an oracle would not advance
the factoring goal. No new numerical cases or protocol are selected here.
