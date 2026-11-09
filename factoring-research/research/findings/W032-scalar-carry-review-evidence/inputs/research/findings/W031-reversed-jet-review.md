# W031 review: reversed jets, legal normalization, and the first coefficient gcd

**Disposition: accept W031 B–D's mathematical core with the implementation and
scope clarifications below. Reject the displayed dense-jet route as an
asymptotic improvement over the paid small-factor product comparator. Verified
complete factoring improvement: NONE.** No novelty or global lower bound is
claimed. Section A and both completed W030 audits are outside this audit.

For distinct odd primes p<q, N=pq, the exact first proper coefficient gcd is
indeed at j=(p−1)/2 and returns q. Every earlier coefficient is zero modulo N;
its permitted normalization is the stated universal **unit** modulo N. In fact,
its entire residue modulo N² is determined by that universal value and the
public multiplier. No earlier extra digit is hidden in this observation.

Two clarifications matter. Removing the factor 2 from a modular trace requires
its modular inverse; the canonical trace residue need not be even. Also,
prime-power controls have different component orders, but their raw coefficient
gcd can appear at the same small-prime index. That statement has a separate
valuation proof here; it does not revive W029's rejected nonsquarefree
formal-top-index extension.

## 1. Scope, frozen inputs, and evidence level

The complete user brief and ten input files were frozen before the symbolic
audit. The target is the frozen W031 with SHA-256
`d19196b1023f0df813812e5b75d8beec1f8062422b1f6db546cf8e53ca7bedd2`.
See [input manifest](W031-reversed-jet-review-evidence/input-manifest.json),
[full brief](W031-reversed-jet-review-evidence/brief.txt), and
[actual read scope](W031-reversed-jet-review-evidence/read-scope.json).

Governing documents, W031, both named W029 reports, and the W028 comparator
were read in full. W031 A was read only for context; only B–D were audited.
STATE was frozen in full and read only at lines 1–130 and 1189–1378 for
read-only context. Its stale live-task descriptions do not override this
brief. Filename searches also exposed archived paths; their contents were not
read. W030 reports, old certificate sources/results, solver code, Lean code,
and task registries were not read or modified.

The imported W029 fact is its accepted **semiprime** component-degree formula.
The parent disposition controls overstatements in the original review:

- No nonsquarefree top-index recovery is imported; the N=9 correction stands.
- Frobenius on a general finite quotient ring is only an endomorphism without
  the needed additional hypotheses. No extension-ring exclusion is adopted.
- No generic-random-prime probability assertion is adopted.
- No global complexity exclusion, or exclusion of all processing of evaluations,
  high-index coefficients, or implicit valuations, is adopted.

W028 is a paid coefficient-or-factor construction, not a free or unconditional
coefficient oracle. Its stated arithmetic construction is the local comparator;
this audit makes no fresh literature-priority claim. No web source was fetched.
The identities below are proved directly by polynomial recurrences and integer
valuations, so an external Lucas-identity citation is unnecessary.

No numerical certificate was run. The optional single experiment was declined:
the symbolic proof settles the stated onset and low-normalization question;
a finite pass would not strengthen its complexity scope. The small controls
below are worked symbolic identities, not experimental output. No installs,
delegation, commits, shared solver/Lean/STATE/task edits, or project test runs
were performed. Only this report and its assigned evidence directory were
written. No executable solver or certificate source was added.

## 2. Matrix identity, parity, and exact truncation

Throughout N=2n+1≥3 is odd. Let

    F_m(X)=((1+a)^m+(1−a)^m)/2,   a²=1−4X,
    T_m(z)=trace(D(z)^m),          D(z)=[[2z,−4],[1,0]].

The basis expansion F_m=Σ_k binom(m,2k)(1−4X)^k shows integrality.
Cayley–Hamilton gives

    T_0=2, T_1=2z, T_m=2z T_(m−1)−4 T_(m−2).

In the Laurent-polynomial ring, 2z^m F_m(z^(−2)) obeys exactly this recurrence
and the same initial conditions: its two formal roots have sum 2z and product
4. Thus, after clearing the powers of z,

    T_N(z)=2z^(2n+1) F_N(z^(−2))=2z J_N(z²).

This is an integer polynomial identity; no eigenvalue extraction or inversion
of z occurs in the algorithm. Also T_m(−z)=(−1)^m T_m(z), by the recurrence.
Consequently the odd-N trace has only odd powers, even over the composite
coefficient ring. J_N has degree n because F_N(0)=2^(N−1)≠0 over the integers.

Take 0≤K≤n, d=2K+3, and R=(Z/N²Z)[z]/(z^d). Projection into R is a ring
homomorphism, so binary matrix powering in R produces the exact reductions
of all trace coefficients below d. Terms removed at high degree never feed
back into lower degrees. The needed coefficient for a_j is [z^(2j+1)]T_N,
whose largest index is 2K+1. The proposed precision is therefore sufficient.
In fact z^(2K+2) suffices; z^(2K+1) generally does not. The extra retained
z^(2K+2) coefficient in the proposed version is a forced zero.

Extraction means a **coefficient shift** for z and multiplication by
2^(−1) modulo N². It is not division by z inside the quotient ring, nor
integer halving of an arbitrary canonical trace residue. For example,
T_3=8z³−24z; modulo 9 its z coefficient is 3, although the true coefficient
is even. Multiplication by 2^(−1)=5 modulo 9 correctly gives a_0=6 modulo 9.

An explicit implementation of the requested observation is:

    m = N²; d = 2K+3
    B = D(z)^N in (Z/mZ)[z]/z^d, by binary powering
    c = trace(B)
    h = inverse(2, m)                    # legal because N is odd
    u = inverse(pow(−4, n, N), N)        # legal because N is odd
    for j = 0,...,K:
        r = (h * coefficient(c, 2j+1)) mod m   # canonical 0≤r<m
        g = gcd(r, N)
        if 1 < g < N: return factor g
        if g == N:
            b = ((r // N) * u) mod N     # exact integer division
            record b                    # normalization allowed here only
        else:
            record coefficient r        # no normalization by N

The quotient in the g=N branch is well-defined modulo N: changing a lift of
r by kN² changes r/N by kN. The unit scale is computed once. N itself is
never inverted. "Exact coefficients" here means exact **residues** modulo
N², not reconstruction of the potentially much larger integer coefficients.

## 3. Closed coefficient formula and its legal interpretation

The recurrence in §2 has the formal generating identity

    Σ_(m≥1) T_m(z) s^m/m = −log(1−2zs+4s²).

This follows by differentiating with respect to s and using the recurrence;
its constant term is zero. Expanding the formal logarithm over Q gives

    T_m(z) = Σ_(k=0..floor(m/2))
        [m/(m−k)] binom(m−k,k) (−4)^k (2z)^(m−2k),   m≥1.

These formal rational operations prove a polynomial identity; they are not
operations required of the modular algorithm. For m=N and k=n−j, dividing
the coefficient of z^(2j+1) by 2 yields exactly

    a_j = N(−4)^n (−1)^j (n+j)! / ((n−j)!(2j+1)!),   0≤j≤n.

The endpoint checks are a_0=N(−4)^n and a_n=2^(N−1). In particular, the
formula does not imply that a_j/N is always integral.

The 2j numerator factors pair as

    (n−i+1)(n+i) = (N²−(2i−1)²)/4,   i=1,...,j.

Hence, as an exact rational identity,

    a_j/[N(−4)^n]
      = Π_(i=1..j)((2i−1)²−N²) / [4^j(2j+1)!].                (1)

If gcd((2j+1)!,N)=1, its denominator is a unit modulo every prime power
dividing N. Since a_j is an integer, cross-multiplication in (1) first
proves **N divides a_j**. Only then is reduction of a_j/N modulo N legal.
Reducing the numerator of (1) gives

    b_j := (a_j/N)(−4)^(−n)
         ≡ Π_(i=1..j)(2i−1)²/[4^j(2j+1)!]
         = binom(2j,j)/[16^j(2j+1)]  (mod N).                  (2)

The last equality is rational cancellation using
Π_(i=1..j)(2i−1)=(2j)!/(2^j j!). Every denominator used here is a unit
under the stated hypothesis. The formal rational series with these
coefficients is 2 asin(sqrt(t)/2)/sqrt(t), with constant term 1. This is a
series identity only; no analytic or transcendental oracle is supplied.

## 4. What the earlier normalized jet contains

Let p be the smallest prime divisor of odd N, without a squarefree assumption
for this paragraph. For 0≤j<(p−1)/2, we have 2j+1<p. The hypothesis of (2)
then holds. Every numerator factor 2i−1 is also a unit modulo N, so b_j is a
unit. More precisely, for every prime r with r^e exactly dividing N,

    v_r(a_j)=e,       gcd(a_j,N)=N,       gcd(b_j,N)=1.          (3)

Both numerator and denominator of (1) are r-units; this proves (3) directly.
Thus the full canonical residue modulo N² is already

    a_j mod N² = N * (( (−4)^n b_j ) mod N).                   (4)

Equation (4) exhausts the N²-level observation used by the proposed algorithm.
It is stronger than just saying that the raw coefficients vanish modulo N:
there is no unaccounted earlier N-adic digit in these residues. The public
unit (−4)^n costs a modular exponentiation; the rational b_j is independent
of any supplied factorization. For instance the public recurrence

    b_0=1,
    b_(j+1)=b_j (2j+1)²/[8(j+1)(2j+3)]

generates the same prefix with checked unit denominators.

This is an equality of observation data, not an information-theoretic or
computational impossibility result. Arbitrary processing of the public
numbers, changing the modulus or precision, combining many observations,
using an implicit representation, or selecting distant coefficients is not
ruled out. No proof is given that such processing cannot factor N. The
claim is exactly that legal normalization supplies the displayed universal
unit values, and testing their gcds gives no earlier split.

## 5. Exact semiprime onset and prime-power controls

For N=pq with distinct odd p<q, the accepted W029 identity is

    F_N(X) ≡ F_q(X^p) mod p,
    deg(F_N mod p)=(N−p)/2.

Its leading coefficient is q(−4)^((q−1)/2), nonzero modulo p. Reversing at
the integer degree n therefore gives

    ord_t(J_N mod p)=n−(N−p)/2=(p−1)/2.

Interchanging p and q proves ord_t(J_N mod q)=(q−1)/2. At j_0=(p−1)/2,
the coefficient is nonzero modulo p and still zero modulo q, so

    gcd(a_(j_0),N)=q.

Every smaller j has gcd N. This is the **first proper raw-coefficient gcd**,
not just a possible onset. Its residue is not divisible by N, so the
normalization branch must not be entered there.

There is also a separate useful valuation control that avoids all formal-degree
inference over a nonreduced ring. For arbitrary odd N, let p be its smallest
prime factor and p^e exactly divide N. At j_0=(p−1)/2, the denominator of (1)
is 4^j_0 p!, with p-adic valuation exactly 1. All numerator factors have odd
arguments ≤p−2, hence are p-units. At any other prime r dividing N, both
numerator and denominator are r-units, since r>p. Thus

    v_p(a_(j_0))=e−1,
    v_r(a_(j_0))=v_r(N) for every other r|N,
    gcd(a_(j_0),N)=N/p.                                      (5)

For **composite** odd N this is proper. Together with (3), this proves the
same first proper gcd index for general odd composites, now by an explicit
local valuation argument. It does not extend W029's rejected formal-top-index
claim. W031's squarefree restriction is essential to its displayed component
orders, but is unnecessary for the raw-gcd index after this separate proof.

The controls distinguish the notions:

- If N=p is prime, F_p≡1 modulo p and J_p≡t^((p−1)/2) modulo p. Earlier raw
  gcds are p, normalized gcds are 1, and the last raw gcd is 1. No proper
  factor is returned. Equation (5) correctly gives N/p=1.
- If N=p^e, e≥2, Frobenius instead gives F_N≡1 modulo p, so
  ord_t(J_N mod p)=(p^e−1)/2. Nevertheless (5) gives the earlier proper
  gcd p^(e−1) at j=(p−1)/2. Nilpotent coefficients modulo p^e carry that gcd.
- Explicitly,

      J_9(t)=2304−7680t+6912t²−2304t³+256t⁴,
      J_9 mod 3=t⁴,       J_9 mod 9=6t+4t⁴.

  The constant gcd is 9, the next gcd is 3, and −7680/9 is not an integer.
  This preserves the parent's N=9 correction and demonstrates why reduction
  modulo the prime cannot determine onset over its power.

These controls neither import blanket extension automorphisms nor make any
random-prime assertion. No randomized claim is needed for this algorithm.

## 6. Complete cost of the displayed computation

Write L=bit_length(N); this differs from the polynomial index n=(N−1)/2.
Let d=2K+3, with K≤n, and let P(d,L) be the bit cost of a truncated degree-<d
polynomial multiplication over Z/N²Z, including coefficient reductions.
Binary powering uses O(L) matrix multiplications and a constant number of
polynomial multiplications per matrix multiplication. Additions and extraction
are charged too. A transparent bound is

    O(L [P(d,L)+dL] + (K+1)[G(L)+M_int(L)] + L M_int(L)+G(L)),

where G(L) bounds a gcd or extended gcd on O(L)-bit integers and M_int is
integer multiplication cost. This includes the per-coefficient gcds and
normalizations, the one-time unit exponentiation/inversion, and extraction.
Exact division by N of a known multiple has O(L)-bit operands and is included
in the arithmetic cost, using ordinary fast integer division if needed.
The upper bound computes the whole requested jet even if scanning it later
finds a factor. No preknown p or q is used by the algorithm.

All stored modular coefficients have at most 2L bits. A scalar product before
reduction has at most 4L bits; accumulating a full convolution coefficient
without intermediate reduction adds O(log d) bits. Since K≤n, log d=O(L).
A constructive fast multiplication option packs nonnegative coefficients in
base 2^w with w≥4L+ceil(log_2 d)+1, multiplies two O(dL)-bit integers, unpacks,
and reduces each coefficient modulo N². There is no carry between packed
convolution coefficients with this choice. It yields, for example,

    P(d,L)=O(M_int(O(dL))+d M_int(O(L)))

with fast integer reduction. Thus standard quasi-linear integer arithmetic
gives a soft O((K+1)L²) bit upper bound for powering, with the gcd terms
included up to logarithmic factors. The claim is conditional on that chosen
arithmetic, not that a naive polynomial implementation has linear cost.
Schoolbook polynomial multiplication and schoolbook scalar arithmetic instead
give the conservative O((K+1)² L³) powering bound.

The resident matrix coefficient arrays require O((K+1)L) bits, including the
K=0 case. This is also a total working-space bound with a straightforward
schoolbook multiplication routine. A fast multiplication implementation must
add its own workspace; the coefficient-array count alone is not a proof of
its total memory. Storing the full exponentiation history is unnecessary.
No factorial-sized integers are needed in the actual modular matrix algorithm.

An expanding search with geometrically increasing K, scanning coefficients
in index order and stopping on a proper gcd, reaches j_0=(p−1)/2 with
Θ(p) explicitly represented coefficients overall. Geometric recomputation
has the same soft cost scale as its last stage. With fast arithmetic the
resulting bound is soft O(p L²); the displayed dense representation itself
has Ω(p) coefficient traffic. Its early canonical N² residues are nonzero
multiples of N by (3), so storing that raw prefix even costs Ω(pL) bits.
These are counts for this representation and search, not for all algorithms
that receive the compact matrix circuit. There is no uniform poly(L) bound
from this procedure when p grows as a power of N. Small-p families are a
separate scope.

## 7. Paid comparator, possible replacement, and disposition

The W028 construction costs soft O(sqrt(j)) ring work for a **supplied**
central-binomial index j, plus its stated gcds and bit widths, and returns
either that coefficient or a proper factor. Computing the rational b_j also
requires testing/inverting 2j+1 and paying for the unit 16^j. None of these
primitives is a free dense jet or a free formal-degree query.

A concrete already-known way to remove the linear prefix traffic is to test
the denominator factorial in blocks. For a public bound B<N, take
b=ceil(sqrt(B)), construct Π_(i=1..b)(T+i), evaluate at the O(sqrt(B)) block
starts by monic remainder trees, multiply the tail, and take gcd(B! mod N,N).
Use the stored block values and, if necessary, expand one full-gcd block to
localize a proper factor. Every expanded integer is in [1,B] and <N, so a
nonunit entry gives a proper gcd. This is exactly the paid product mechanism
explained in W028. Applying it at B=2K+1 reaches the same denominator crossing
with soft O(sqrt(K)) work, without producing all a_0,...,a_K. A geometric
schedule of B for composite N reaches the least prime with soft O(sqrt(p))
ring work; it can be capped at floor(sqrt(N)) to keep B<N and ensure coverage.
This supplies an actual replacement computation, but only recovers the
existing comparator. No new gain is claimed for it.

To improve beyond that comparator, a proposal must give an actual cheaper
computation and pay for its selected indices, polynomial arithmetic, any
precision or modulus changes, and factor extraction. Simply asking for
ord_t(J_N mod p) without knowing p, or calling the compact circuit's formal
degree available, would assume the missing computation. This review supplies
no new operation beating the block-product cost and makes no impossibility
claim about such an operation.

No further small-case sweep of the displayed dense jet is needed to establish
its symbolic onset. A different consumer with a proved cost below the paid
comparator, or a concrete counterexample to one of the stated identities,
would change the disposition. Verified complete factoring improvement remains
**NONE**; the parent retains constructive work and intake of W030.

## 8. Delivery integrity

[delivery-manifest.json](W031-reversed-jet-review-evidence/delivery-manifest.json)
records every delivered payload's complete bytes and SHA-256, including this
entire report, all frozen inputs, and the read-scope record. The manifest
excludes itself and the hash-anchor file to avoid a circular hash definition.
[terminal-manifest.sha256](W031-reversed-jet-review-evidence/terminal-manifest.sha256)
contains the SHA-256 of the exact manifest bytes; the same hash is supplied
in the terminal handoff outside the report. Those two inventory files plus
the enumerated payloads are the entire delivery. The report is finalized
before the manifest; no post-manifest paragraph is appended to it.
