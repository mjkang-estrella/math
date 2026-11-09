# W015 Composite factorial routing and implicit survivor products

2026-10-08. Parent constructive wave, independent of the three live W014
audits. Verified new end-to-end factoring improvement: NONE. The proposed
operation routes a long product into one shared short prefix and a residual
product, rather than enumerating modular exponent targets or smooth relations.

## Source and scope

Yann Tal's September 2026 preprint,
[Computing Modular Factorials Below the Square-Root Barrier](https://eccc.weizmann.ac.il/report/2026/211/download),
studies factorials modulo a supplied prime, with additional cyclotomic-divisor
inputs for its exponent savings. Its separate Appendix H uses modular halving
and simultaneous product evaluation for a logarithmic refinement. Section 1.4
does not give an unknown-factor composite-modulus algorithm. The parent read
the theorem statements, reconstruction overview, section 1.4 and Appendix H's
routing/evaluation passages; the full paper is not independently verified here.

The following is the parent's explicit odd-composite adaptation and its own
cost/fragmentation analysis. It does not import the prime-modulus theorem as
a factoring bound. The character, prime-ideal and local-reduction inputs of
the exponent-saving algorithm are not supplied by knowing N alone.

## A product routing algorithm valid for every odd modulus

Let N>=25 be odd, n=isqrt(N), and choose an integer prefix length 1<=H<n.
Write P(a,b)=product_(a<j<=b) j modulo N, for 0<=a<=b<N. The map

    T(x)=x/2 if x is even, and (x+N)/2 if x is odd

is multiplication by the inverse of 2 modulo N, on the nonzero representatives.
Splitting an interval into its even and odd indices gives the exact identity

    P(a,b)=2^(b-a)
      *P(floor(a/2),floor(b/2))
      *P(floor((a+N)/2),floor((b+N)/2)) (mod N).     (1)

Begin with (0,n]. Remove and retain its portion in [1,H]. At each subsequent
round apply (1) to every active interval, add the old interval length to E,
retain any new prefix portion, and continue with the portions above H.
Empty intervals are omitted. The current active intervals are disjoint because
T is a permutation; prefix intervals stopped at different depths may overlap
and must retain their multiplicities. After t rounds,

    n! = 2^E * product_(stopped intervals) P(a,b)
             * product_(active intervals) P(c,d) (mod N).  (2)

This is an executable interval-list algorithm with integer endpoints. E has
at most O(log n+log(t+1)) bits, since E<=nt. Negative or zero factors are
not introduced, and every represented index remains strictly below N.

## Pay for all product evaluation and nonunit recovery

Let R be the total number of final stopped/active interval records, U the
total active length, and C_route the actual work creating/updating records.
An available conservative envelope, up to polynomial logarithms, is

    C_route + R + sqrt(H) + sqrt(U).                    (3)

Here is an explicit route to the prefix term, without a selected-term oracle.
Set b=ceil(sqrt(H)). Build product_(j=1)^b (Z+j) and evaluate at all complete
b-block offsets through H by monic product/remainder trees. Prefix products
of these O(sqrt(H)) values give factorials at block boundaries. For each
requested endpoint m, its residual interval has length less than b. Split
all such residual intervals into dyadic lengths and batch their products,
grouping equal lengths. If there are O(R) endpoints, this costs

    O~(sqrt(H)+R+sqrt(R*b)) = O~(sqrt(H)+R).

The standard batched interval construction used here builds a degree-w block
polynomial and evaluates it at all U0/w starts in an equal-length group of
total length U0. Choosing w near sqrt(U0), capped at the individual length,
gives O~(number_of_intervals+sqrt(U0)); summing dyadic groups costs logarithms.
This works with repeated intervals and composite coefficients using monic
division. No arbitrary field inverses are presumed. It also prices the active
intervals at O~(R+sqrt(U)). Coefficient packing, comparisons and gcds have
their actual O(log N)-bit costs within the displayed polynomial logarithms.

For a stopped interval, divide the computed endpoint factorials only after
checking that the denominator is a unit. A proper denominator gcd is already
a factor. If its gcd is N, localize a nonunit leaf in that factorial prefix
using interval products; the successive square-root costs sum to O~(sqrt(H)).
Every leaf is a positive integer below N, so a nonunit leaf has a PROPER gcd.
The algorithm terminates with that factor before trying another such recovery.

If all stopped products are units, any nonunit in n! is retained by the active
product. A full active-product gcd is handled by finding a nonunit interval
and bisecting it, with O~(R+sqrt(U)) additional work. Again every final leaf
is below N. These branches handle arbitrary odd composites, not just semiprimes.
Every composite has a prime factor at most n, so exact evaluation/recovery
would produce a factor. Prime inputs may return no factor; the research
splitter contract promises a composite and does not need to infer primality
from an incomplete computation.

The primitive product methods in this envelope are known-scale operations;
no new fast factorial algorithm is claimed for them. All endpoints, pieces,
duplicate multiplicities and gcd=N recovery are explicitly charged.

## What would remove enough work

If one could route with H=O(n^(2/3)), U=O(n^(2/3)) and both R and C_route
of O(n^(1/3)) up to polynomial logarithms, (3) would give N^(1/6) scale.
This is an input-to-cost calculation, not a supplied routing guarantee.
It identifies what computation needs replacing in the explicit algorithm.

A first elementary constraint is valid for ANY sequence of unit permutations
with a common prefix [1,H]: each round can stop at most H distinct initial
points, because its map is injective. Including depth zero, stopping n-U
points requires (t+1)H>=n-U. Reusing a compact multiplier formula does not
by itself perform all these preimage intersections or evaluate their products.

Also gcd(T(x),N)=gcd(x,N). A point divisible by a prime p>H can never stop
in that prefix. That fact preserves the sought factor in the residual product;
it does not alone prove the residual is large or the algorithm slow.

## Exact fragmentation test for the literal binary interval router

The following parent proof is provisional pending independent review. It is
a bound on (3) for the SPECIFIED explicit interval representation, not on
all compressed routing methods or on factoring.

Assume H<=n/4 and put s=ceil(log2 n), so n<=2^s<2n. For any odd x in
(H,n] and any 1<=r<=s,

    T^r(x)=(x+k*N)/2^r

for some odd k in {1,...,2^r-1}. Thus T^r(x)>=N/2^r>=N/2^s>n/2>=H.
This x survives all of the first s rounds. There are at least
floor((n-H)/2) such odd x. If the algorithm stops before round s, therefore,
U>=floor((n-H)/2)=Omega(n); the sqrt(U) term in the chosen evaluator's
bound gives no smaller exponent than sqrt(n).

At round s no two distinct points from T^s({1,...,n}) are consecutive.
Otherwise their original difference, of absolute value at most n-1, would
be congruent to 2^s or -2^s modulo N. But

    2^s>=n,             N-2^s>n-1

for n>=5, using N>=n^2 and 2^s<2n. Neither congruence is possible.
Every surviving point is consequently an isolated singleton in any exact
representation by ordinary consecutive integer intervals. A run reaching
round s must create at least floor((n-H)/2)=Omega(n) active interval records
at that depth, even if they might merge in a later round. This cost is inside
C_route, not erased by reporting only the final list length.

If H>n/4 instead, the planned sqrt(H) prefix computation is already at
sqrt(n) scale. These cases show that the displayed upper-bound recipe does
not certify a power saving with the literal interval router. They do NOT
prove every implementation of prefix or residual evaluation needs sqrt(n)
work; a new evaluation mechanism would be a different algorithm.

## Materially different continuation

The full image after s rounds has a short description as a modular arithmetic
progression, despite its many ordinary intervals. Stopped-prefix exclusions
must be retained as well. This is the representation change the fragmentation
proof actually suggests. However, the product over the uncut progression is
only a known unit multiple of the original n!, so using that equality to
claim a cheap residual product would be circular. The next mechanism must
give a new noncircular recurrence or character identity for the cut progression,
including construction and full-gcd localization. Modulo a known prime, the
new source provides additional arithmetic data; acquiring corresponding data
for an unknown prime factor is a separate unresolved task.

Do not launch another arbitrary parameter sweep. Preserve the three W014
audits. When capacity becomes available, delegate a narrowly scoped audit of
(1)--(3), composite recovery, fragmentation, and the primary-source boundary.

## Fixed algebra certificate preregistration

Before implementation/execution, fix N in {25,35,77,101,143,21311}; the prime
101 is an algebra-only control. For each take n=isqrt(N), H=floor(n/4),
s=(n-1).bit_length(). Run exactly s routing rounds. Check interval identity
(1), the cumulative product identity (2), disjoint current images, prefix
stopping, gcd preservation for all points, survival of all odd x>H, the
nonadjacency assertion and singleton count at depth s. Compare the interval
representation with an independent pointwise permutation at each round.
Use exact integer arithmetic; do not time or fit growth rates. Preserve every
case/round and all failed assertions. Maximum 60 seconds, 20000 point visits;
no extra cases, replacements, searches, dependencies or solver registration.
Owned files: research/findings/W015-routing-certificate* and its evidence
directory. Frozen hypothesis/script hashes accompany the output. These fixed
certificates do not prove the universal theorem or an asymptotic speedup.
