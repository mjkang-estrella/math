# Ordinary proof of DeWitt–Keith, arXiv:2507.13566v1, Conjecture 1

Written 2026-10-29. This is a full ordinary proof of the **numbered conjecture**,
conditional only on the established unrefined congruences explicitly identified
below. It is not an eligibility, independent-review, journal-equivalence, novelty,
or formal-proof claim. The subsequent prose observation concerning individual
residue-zero classes is not asserted here. Routine adaptation is a serious
objection to campaign credit; see discovery.md.

## Exact endpoint and known inputs

Write a two-part-size partition as (a^c b^d), where a>b>=1 and c,d>=1, and
ac+bd=N. Define r=a-c-d and s=a+b-2c-d. Put
P={(16,14),(36,30),(72,42),(196,70),(252,114)}.
For every (A,B) in P and every integer n>=0, both counts with s even and s odd
are divisible by four at N=An+B. Both counts with r even and r odd are likewise
divisible by four for the four pairs other than (16,14). No claim of failure at
every point of the omitted progression is made.

Known input: the total number nu_2(N) is divisible by four on all five
progressions. For the last four this is Keith, arXiv:1502.00366v4, Theorem 1
(actual PDF p2), whose stated theorem is used, not reproved. For the first it
is DeWitt–Keith Theorem 1 (also Keith v4 Theorem 5). All arithmetic and counting
bridges from those totals to the refined endpoint are proved below.

## 1. Nine classes and the even counts

Throughout this section N=2m with m odd. For a partition, encode the parities
of a,c,b,d by a word with letters O and E. The possible words are
OOOO, EOOE, EEOE, EOEO, OEEE, EEEO, EOEE, OEOE, OEEO.
Indeed the two products must have the same parity; if both even, their
2-adic valuations cannot both exceed one or both equal one. Inspection gives
exactly this list.

Conjugation is the involution
C(a,c,b,d)=(c+d,b,c,a-b).
It preserves N and interchanges EOEE with OEOE, and EEOE with EOEO.
Let X count OEOE, Y count OEEO, and Z count EOEO. Inspection of the nine words
therefore gives, for the even-rank counts,

E_s=2X+Y,                       E_r=2Z+Y.                 (1)

Here OEOE means both sizes odd and both multiplicities even; EOEO means both
sizes even and both multiplicities odd. Neither notation concerns partitions
with more than two distinct sizes.

## 2. An exact identity relating the two ranks

There is an injection from OEOE to EOEO: swap the powers of two in each
size/multiplicity pair, keeping their odd factors in their respective slots,
then sort by size. The image is exactly the EOEO partitions whose two sizes
have different largest odd divisors. To see this, applying the same operation
to an EOEO partition produces distinct odd sizes if and only if its original
sizes have different odd factors. These two operations are mutually inverse
when defined; sorting loses no information because the sizes are distinct.

An omitted EOEO partition has sizes 2^(t+1)k and 2k with t>=1 and k odd,
and has odd multiplicities u,v. The smaller power is exactly 2, since their
sum N has valuation one. Its equation is
m=k(2^t u+v).
For each positive divisor k of m, choose a positive even x<m/k; uniquely
x=2^t u with t>=1,u odd, and v=m/k-x is positive odd. Hence the complement
has size sum_{k|m}(m/k-1)/2=(sigma_1(m)-d(m))/2. Consequently

E_r-E_s=2(Z-X)=sigma_1(m)-d(m).                          (2)

This is the source Lemma 9 operation, with the complement counted explicitly.

## 3. Reduction of E_s modulo four to an involution

Let S consist of partitions satisfying

a=2 mod4, c odd, b odd, d=0 mod4, a != 2b.

We prove

E_s = 2|S| mod4.                                         (3)

Split X according to which odd size has multiplicity of valuation one.
Doubling that size and halving its multiplicity preserves N. If that size is
a, the resulting even size is larger than twice the odd size, giving the part
of S with a>2b. If it is b and its doubled size exceeds a, the image is the
part of S with a<2b. If it is b and its doubled size is smaller than a, the
image belongs to OEEO with its even-size product contributing 2 mod4.
Equal sizes cannot occur, since an odd size cannot equal twice an odd size.
All maps are reversible by halving the even size and doubling its odd
multiplicity. The even size in an S image has valuation one: its product
contributes 2 mod4, whereas the other product contributes 0 mod4.
Thus X=|S|+Y_1, where Y_1 is that indicated subclass of OEEO.

In OEEO, the odd size a and odd multiplicity d leave b,c even. Exactly one of
b,c has valuation one. Conjugation interchanges b and c, pairing the two
subclasses Y_1 and Y_2. Therefore Y=2Y_1. Equation (1) gives
E_s=2|S|+4Y_1, proving (3).

## 4. The fixed points, including the non-6-mod8 case

Suppose now N is not a sum of two integer squares. Conjugation identifies S
with the following set W of quadruples (u,x,v,y):

u>v>=1, all four entries odd, u=v mod4, x=y mod4, x!=y,
and ux+vy=N.

For clarity, C(a,c,b,d) has u=c+d, x=b, v=c, y=a-b.
The conditions follow from d=0 mod4 and a=2 mod4. Conversely C on a member
of W has even size x+y=2 mod4, odd multiplicity v, odd second size x,
and multiplicity u-v=0 mod4, and its size is not twice x since x!=y.
Thus this is a genuine bijection.

On W, interchange size and multiplicity in BOTH pairs, then reorder by size.
Distinctness of x,y ensures definition; distinctness of u,v ensures the
returned multiplicities differ. Equal residues modulo four are preserved
under sorting. This is an involution.

Its fixed points are of two kinds:
(i) u=x and v=y, requiring N=u^2+v^2; or
(ii) u=y and v=x, requiring N=2uv.
There are no other possibilities, because the unordered pair of ordered
size/multiplicity pairs must be invariant under simultaneous reversal.
Kind (i) is excluded by hypothesis. In kind (ii), u>v are odd, uv=m, and
u=v mod4. If m=3 mod4 there are none. If m=1 mod4 every factor pair
has this property. Also m cannot be a square, since then N is a sum of two
equal squares. Thus in the latter case there are exactly d(m)/2 fixed points.
Every nonfixed orbit has size two, so (3) yields

E_s = 0 mod4                 if m=3 mod4,
E_s = d(m) mod4              if m=1 mod4.                 (4)

This explicitly handles the fixed-point contribution that prevents simply
extending source Lemma 8 to every N=2 mod4. For example N=10 has E_s=2;
it would invalidate such an extension without the contribution.

## 5. Arithmetic of all five source progressions

At N=16n+14, m=8n+7 is 3 mod4 and N is 6 mod8, which cannot be a sum of two
squares. Equation (4) gives E_s=0 mod4.

For the other four progressions the following table writes m=p h:

| N | p | h | obstruction to h being a square |
|---|---:|---|---|
|36n+30|3|6n+5|h=2 mod3|
|72n+42|3|12n+7|h=3 mod4|
|196n+70|7|14n+5|h=5 mod7|
|252n+114|3|42n+19|h=5 mod7|

In each row p does not divide h. The primes 3 and 7 have -1 as a quadratic
nonresidue, so valuation one at p prevents N=2ph from being a sum of two
squares: if p divides a square sum, both coordinates are divisible by p,
forcing valuation at least two. Moreover h is not a square by the last column,
so d(h) is even by pairing complementary divisors. Thus

d(m)=2d(h)=0 mod4,             sigma_1(m)=(p+1)sigma_1(h)=0 mod4. (5)

Equations (4) and (5) give E_s=0 mod4 in all four rows, regardless of m mod4.
Equation (2) gives E_r=0 mod4 in all four rows as well.

Finally the known unrefined counts nu_2(N)=0 mod4 subtract these even counts
to give the odd counts. This proves every clause of the numbered Conjecture 1
for every n>=0. No finite verification is used in the proof. QED.

## Eligibility warning

The nine-class grouping, conjugation, valuation-switch operation, and
conjugate/reversal/conjugate mechanism already occur in the source. The
additional fixed-point count is a modest all-progression extension. This proof
should receive independent mathematical and substantive review before any
further investment; ordinary completeness does not establish campaign novelty.
No worldwide-priority claim or count is made.
