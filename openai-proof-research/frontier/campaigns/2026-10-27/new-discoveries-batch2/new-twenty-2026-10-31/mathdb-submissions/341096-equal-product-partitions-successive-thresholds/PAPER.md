# Successive thresholds for equal-product partitions

**MathDB 341096. Computer-assisted proof with a Lean 4 kernel certificate.**

We give the elementary stability argument, an explicit cubic-size family, and
finite certificates for Cha et al.'s three successive-threshold conjectures.
The accompanying Lean development proves all three statements with their literal
positive-multiset definitions, including existence and minimality of both
permanent-tail thresholds. The proof combines a structural stability lemma,
explicit infinite collision families, and certified finite negative bounds.

## Source statement and literal definitions

The source is B. Cha, A. Claman, J. Harrington, Z. Liu, B. Maldonado, A. Miller,
A. Palma, T. W. H. Wong and H. V. Yi, *An Investigation on Partitions with Equal
Products*, arXiv:1811.07451v1, 19 November 2018, Introduction, Theorem 4.1,
and Conjecture 5.2; Int. J. Number Theory **15** (2019), 1731–1744,
DOI 10.1142/S1793042119500969. The cached primary text was read directly.
[Primary preprint](https://arxiv.org/abs/1811.07451).

Conjecture 5.2, verbatim (mathematical notation transcribed into TeX):

> (a) For all integers $n\geq9$, $s^*_{n-2}(n)=s^*_{n-2}(n-1)+1$.
>
> (b) For all integers $n\geq7$, $s^*_{n-1}(n)=s^*_{n-1}(n-1)+1$.
>
> (c) For all integers $n\geq10$, $s^*_n(n)=s^*_n(n-1)+1$.

The Introduction's definitions, verbatim apart from mathematical typesetting:

> A multiset $X=\{x_1,x_2,\ldots,x_n\}$ of $n$ positive integers is an
> $n$-partition of the sum $s=x_1+x_2+\cdots+x_n$. Define the function
> $T\{x_1,x_2,\ldots,x_n\}=(s,p,n)$, where $p=x_1x_2\cdots x_n$.

The source first defines a stronger function with globally distinct parts.
Its condition (b) is:

> there exists $p\in\mathbb N$ such that for all $i=1,2,\ldots,r$,
> $T\{x_{i1},x_{i2},\ldots,x_{in}\}=(s,p,n)$.

It then defines the function used here:

> If condition (a) is removed, then let $s^*_r(n)$ be the smallest positive
> integer, if it exists, such that for all integers $s\geq s^*_r(n)$, there
> are at least $r$ different $n$-partitions of $s$ satisfying only condition (b).

Immediately alongside those definitions are their literal Lean counterparts:

```lean
def IsPartition (n s : ℕ) (X : Multiset ℕ) : Prop :=
  Multiset.card X = n ∧ (∀ x ∈ X, 0 < x) ∧ X.sum = s

def Good (r n s : ℕ) : Prop :=
  ∃ p : ℕ, ∃ F : Finset (Multiset ℕ), r ≤ F.card ∧
    ∀ X ∈ F, IsPartition n s X ∧ X.prod = p

def IsTail (r n h : ℕ) : Prop := 0 < h ∧ ∀ s, h ≤ s → Good r n s

def IsSStar (r n h : ℕ) : Prop :=
  IsTail r n h ∧ ∀ h', IsTail r n h' → h ≤ h'
```

A finite set enforces distinct **multisets**, with repeated parts permitted.
The product can depend on the sum. `IsSStar` describes a permanent tail and
its least **positive** starting point, rather than a first successful sum.
`EqualProduct.sStar_unique` proves uniqueness. The full Lean endpoints are exactly:

```lean
theorem conj52a : ∀ n, 9 ≤ n → ∃ h,
  IsSStar (n-2) (n-1) h ∧ IsSStar (n-2) n (h+1)
theorem conj52b : ∀ n, 7 ≤ n → ∃ h,
  IsSStar (n-1) (n-1) h ∧ IsSStar (n-1) n (h+1)
theorem conj52c : ∀ n, 10 ≤ n → ∃ h,
  IsSStar n (n-1) h ∧ IsSStar n n (h+1)
```

Natural numbers faithfully represent the positive integer sums and the
admissible integer n in these ranges. Every asserted threshold is accompanied
by an existence proof. No invocation of Kelly's existence theorem is needed.

## 1. Definitions and a stability lemma

Write P(r,d,s) if at least r distinct multisets of d positive integers have
sum s and one common product. The common product can depend on s. Define a
tail threshold to be a positive h such that P(r,d,s) holds for every integer
s >= h; if any such h exists, its least value is s*_r(d).

**Appending lemma.** If P(r,d,t), then P(r,d+1,s) for every s >= t+1.

Indeed, append the same positive integer u=s-t to each multiset. The sum
becomes s and the product becomes pu, where p was the common product.
Appending is injective on multisets: cancel one copy of u from both sides
of any asserted equality. This is the elementary content of source Theorem
4.1, proved here so no effective-existence premise is imported.

**Forced-one bijection.** If n <= s < 2n, removing one copy of 1 is a
product-preserving bijection between n-partitions of s and (n-1)-partitions
of s-1. Every n-partition in this range has a 1, since otherwise its sum
would be at least 2n. Appending 1 is the inverse, and multiplicities make
removal unambiguous. Consequently

    P(r,n,s) iff P(r,n-1,s-1),       n <= s < 2n.             (1)

**Stability lemma.** Suppose r >= 2, n >= 4, and there are r distinct
(n-2)-partitions of one sum t <= 2n-4 and one product. Then both thresholds
exist and

    s*_r(n) = s*_r(n-1)+1.                                  (2)

Proof. The appending lemma makes every (n-1)-part sum >= t+1 successful.
Thus h=s*_r(n-1) exists and h <= t+1 <= 2n-3. At sum n-1 there is only
the all-ones (n-1)-partition, so r >= 2 implies h >= n. Minimality of h
implies P(r,n-1,h-1) is false: if it held, h-1 would also be a positive
tail threshold. Since n <= h < 2n, (1) implies P(r,n,h) is false. Hence
any n-dimensional tail threshold is at least h+1. Conversely, appending 1
to the partitions at each sum s-1 >= h makes every n-part sum s >= h+1
successful. This proves existence and (2). Notice that no monotonicity of
P(r,d,s) in s was assumed. QED.

## 2. A common-product construction for every n >= 152

We construct at least n distinct (n-2)-partitions with common sum 2n-4
and common product. This implies (2) for every 2 <= r <= n, stronger than
the three required values of r.

Put n-2=30m+q with 0 <= q < 30. For n >= 152, m >= 5. Independently
choose u,v,w in {0,...,m}. Use the following numbers of non-one parts:

| Part | Multiplicity |
|---|---|
| 2 | 5u+3v+2w+q |
| 3 | m-v |
| 4 | 4(m-u)+2(m-v) |
| 6 | 2(m-w)+v |
| 8 | u |
| 9 | w |

Every multiplicity is nonnegative. If c_j denotes the multiplicity of j,
direct addition gives

    c_2+2c_3+3c_4+5c_6+7c_8+8c_9 = 30m+q = n-2,
    c_2+c_3+c_4+c_6+c_8+c_9 = 9m+2u+v+w+q <= 13m+q <= n-2,
    c_2+2c_4+c_6+3c_8 = 14m+q,
    c_3+c_6+2c_9 = 3m.

The first identity is the surplus, the sum of (part-1). The second bounds
the length. The last two show that every multiset has product

    2^(14m+q) * 3^(3m),

independent of u,v,w. Append enough ones to give exactly n-2 parts; this
keeps the product and gives sum (n-2)+(n-2)=2n-4.

Distinct triples give distinct multisets. Recover u from the count of 8,
w from the count of 9, and v from m minus the count of 3. Padding with
ones cannot change any of those counts. There are therefore (m+1)^3
distinct partitions. Since n=30m+q+2 <= 30m+31, it suffices to prove
(m+1)^3 >= 30m+31. Writing m=5+a, a >= 0, its difference is

    (m+1)^3-(30m+31) = a^3+18a^2+78a+35 >= 0.

The stability lemma proves all three asserted equalities for n >= 152.
The finite parameter checks in the verifier are only sanity checks on these
identities; the displayed algebra and inequality prove this infinite range.

## 3. Explicit families for 38 <= n <= 151

For a sorted list A of parts >= 2, write T(A)=sum(a-1). If |A| <= n-2,
padding with ones gives a unique (n-2)-partition of sum n-2+T(A). Two
different lists of non-one parts remain different after padding.

`partition-stability-families.json` contains the complete explicit lists for
these five families:

| n range | Common surplus T | Common product | Distinct lists |
|---|---|---|---|
| 38 | 36 | 1658880 | 38 |
| 39..40 | 37 | 3317760 | 40 |
| 41..51 | 39 | 829440 | 51 |
| 52..140 | 50 | 59719680 | 140 |
| 141..151 | 60 | 1194393600 | 151 |

There are 420 listed multisets. Every list is sorted, has parts >= 2,
and has exactly the indicated surplus and product. The independent verifier
checks these integer identities and pairwise distinctness directly; it does
not regenerate a family by trusting the multiplicity search.

In every row T <= (left endpoint)-2, and |A| <= T because all a-1 >= 1.
Thus for every n in that interval the lists pad to n-2 parts with common
sum n-2+T <= 2n-4. The cardinality is at least the right endpoint and hence
at least n. Choosing any r of them proves the stability lemma's hypothesis
for every 2 <= r <= n. The five intervals cover 38..151 with no gap.

## 4. Exact finite base, below n=38

There remain precisely 29+31+28=88 instances: (a) n=9..37, (b) n=7..37,
and (c) n=10..37. We certify their exact thresholds, not just successful
sums in a bounded search.

Let M(d,s) be the largest product multiplicity among the d-partitions of s,
with M=0 when there are none. Define a histogram H(d,s,b) whose coefficient
at p is the number of nondecreasing positive lists of length d, sum s,
all parts >= b, and product p. It has the exact recursion

    H(0,0,b) = {1:1},       H(0,s,b) = {} if s != 0,
    H(d,s,b) = sum over b <= v <= floor(s/d)
               of multiply_keys_by_v(H(d-1,s-v,v)),   d > 0.    (3)

Histogram addition adds multiplicities, including collisions. If s < db the
sum is empty. The first part of any sorted list is a unique permitted v;
deleting it gives exactly one term on the right. Conversely, prepending v
to a list counted on the right produces a permitted sorted list. Induction
on d proves (3) counts every multiset exactly once. Therefore M(d,s) is the
maximum coefficient of H(d,s,1), defaulting to zero.

For each claimed threshold h at dimension d, the finite certificate gives
an integer U >= h and verifies

    M(d,h-1) < r,
    M(d,s) >= r for h <= s < U,
    M(d-1,U-1) >= r.                                         (4)

The last inequality and the appending lemma make every s >= U successful
at dimension d. The middle line supplies the remaining finite interval.
The first line rules out every positive tail threshold below h. Thus (4)
proves **h=s*_r(d)**, even if successful and unsuccessful sums alternate
below h. No first-success/monotonicity assumption is hidden here.

Here is the complete table of the two thresholds in each equality. Each
entry is `s*_r(n-1) → s*_r(n)`; a dash denotes an n outside that part's
asserted range.

| n | (a), r=n-2 | (b), r=n-1 | (c), r=n |
|---|---|---|---|
| 7 | — | 26 → 27 | — |
| 8 | — | 28 → 29 | — |
| 9 | 29 → 30 | 30 → 31 | — |
| 10 | 31 → 32 | 31 → 32 | 33 → 34 |
| 11 | 32 → 33 | 34 → 35 | 34 → 35 |
| 12 | 35 → 36 | 35 → 36 | 36 → 37 |
| 13 | 36 → 37 | 37 → 38 | 38 → 39 |
| 14 | 38 → 39 | 39 → 40 | 40 → 41 |
| 15 | 40 → 41 | 41 → 42 | 42 → 43 |
| 16 | 42 → 43 | 43 → 44 | 43 → 44 |
| 17 | 44 → 45 | 44 → 45 | 45 → 46 |
| 18 | 45 → 46 | 46 → 47 | 47 → 48 |
| 19 | 47 → 48 | 48 → 49 | 48 → 49 |
| 20 | 49 → 50 | 49 → 50 | 50 → 51 |
| 21 | 50 → 51 | 51 → 52 | 51 → 52 |
| 22 | 52 → 53 | 52 → 53 | 52 → 53 |
| 23 | 53 → 54 | 53 → 54 | 53 → 54 |
| 24 | 54 → 55 | 54 → 55 | 55 → 56 |
| 25 | 55 → 56 | 56 → 57 | 56 → 57 |
| 26 | 57 → 58 | 57 → 58 | 57 → 58 |
| 27 | 58 → 59 | 58 → 59 | 59 → 60 |
| 28 | 59 → 60 | 60 → 61 | 60 → 61 |
| 29 | 61 → 62 | 61 → 62 | 61 → 62 |
| 30 | 62 → 63 | 62 → 63 | 62 → 63 |
| 31 | 63 → 64 | 63 → 64 | 64 → 65 |
| 32 | 64 → 65 | 65 → 66 | 65 → 66 |
| 33 | 66 → 67 | 66 → 67 | 67 → 68 |
| 34 | 67 → 68 | 68 → 69 | 68 → 69 |
| 35 | 69 → 70 | 69 → 70 | 69 → 70 |
| 36 | 70 → 71 | 70 → 71 | 71 → 72 |
| 37 | 71 → 72 | 72 → 73 | 72 → 73 |


The exact h,U records and product-multiplicity maxima are in
`partition-small-results.json`. Its search uses surplus partitions: delete
the ones and replace each remaining part a by a-1. This gives a partition
of t=s-d with at most d parts, and product equal to the product of (x+1).
`scripts/search_partition_small.py` uses that bijection, independently of
the direct sorted fixed-length recursion in
`scripts/verify_partition_stability.py`.

The latter imports no build/search code and checks all of (4) by direct
enumeration of actual positive parts. It also checks that the input set is
exactly the 88 required instances, the compared dimensions and r agree,
all h <= U, and the five family intervals cover precisely 38..151. Its
record is `partition-stability-independent.json`:

* 88 conjecture equalities, with 120 distinct exact thresholds;
* 127 distinct dimension/sum histogram enumerations;
* 714219 partitions in total; largest single enumeration 17977 partitions;
* largest surplus needed 36, largest enumerated sum 72, largest tail bound U=73;
* largest enumerated product 68719476736 = 2^36, a 37-bit integer;
* all 420 explicitly listed family members and their distinctness verified.

For example, at n=7 in (b), the thresholds are 26 and 27. The general
certificate verifies failures at sums 25 and 26 respectively, finite
successes until their U values, and lower-dimensional witnesses at U-1.
The full table is not inferred by extrapolating this example.

For clarity, these are exactly the five threshold records with a nonempty
middle interval in (4); every other record has U=h:

| r | d | h | U | Sums checked between h and U-1 |
|---|---|---|---|---|
| 6 | 6 | 26 | 31 | 26..30 |
| 7 | 7 | 28 | 29 | 28 |
| 10 | 9 | 33 | 34 | 33 |
| 11 | 10 | 34 | 35 | 34 |
| 12 | 11 | 36 | 37 | 36 |

In particular, the smallest case does not rely on mistaking the first
lower-dimensional success for the exact higher-dimensional threshold.

Equation (2), the five finite families, the infinite construction, and the
88 finite checks together cover every n in all three frozen assertions.
This completes the proof. QED.


## Kernel verification and finite certificates

The formal appendix proves the append lemma, the forced-one equivalence,
minimality of the threshold, the stability lemma and the full infinite family.
The 420 explicit bridge-family lists and the 1,535 finite positive witnesses
are checked by ordinary `decide`. Filtering away the padding ones and sorting
recover the source multiset representatives, so their distinctness is proved
in Lean. The positive witnesses establish every one of the 120 claimed
permanent tails, including all five finite success intervals.

The relaxed stability lemma only needs t ≤ 2n−2: its least threshold h then
satisfies h ≤ t+1 ≤ 2n−1 < 2n. Four additional positive families prove (a)
for n ≥ 34 and (b),(c) for n ≥ 35. The already certified boundary case (b,7)
leaves 77 finite identities and 105 distinct preceding-sum failures.

For these failures we use a further elementary reduction. Appending k ones
maps any r-element equal-product family at (d,d+t) injectively to one at
(d+k,d+k+t). Decreasing the required family size also preserves success.
Consequently a failure for a multiplicity R at dimension D and surplus t
implies failure for every r ≥ R and d ≤ D at the same surplus. All 105
obligations are covered by the following 14 negative certificates:

| Surplus t | Dimension D | Required multiplicity R | Maximum multiplicity |
|---:|---:|---:|---:|
| 20 | 9 | 7 | 6 |
| 21 | 11 | 8 | 7 |
| 23 | 13 | 10 | 9 |
| 24 | 14 | 12 | 11 |
| 25 | 15 | 13 | 12 |
| 26 | 16 | 14 | 13 |
| 27 | 18 | 15 | 14 |
| 28 | 19 | 17 | 16 |
| 29 | 21 | 18 | 17 |
| 30 | 25 | 20 | 19 |
| 31 | 28 | 24 | 23 |
| 32 | 32 | 27 | 26 |
| 33 | 33 | 31 | 30 |
| 34 | 34 | 33 | 32 |

The largest certificate represents 12,310 partitions. In Lean,
`partitionEnum_complete_multiset` proves that every literal source partition
occurs in the fixed-length sorted-list generator. Its product projection is
proved equal to `fixedProducts`. Negative bounds need only completeness:
any hypothetical family injects into the canonical sorted representatives,
so its size cannot exceed the corresponding product count in the list.
Duplicates in an overcount would only make this upper bound weaker.

The certificate producer supplies sorted product lists for recursively
selected generator nodes. Leaves with at most 32 entries are directly
kernel-enumerated and structurally sorted. For larger nodes, a streaming
Boolean merge checker consumes two supplied child lists and a proposed merged
list. Its soundness theorem proves that the proposed output is a permutation
of the concatenated inputs. Mapping multiplication by the chosen first part
and composing these permutations proves a permutation of the complete product
generator, inductively on the number of parts. No external count, completeness
claim, or sorting algorithm is trusted.

A separate linear adjacent-order test proves sortedness; a proved run-length
bound bounds every product count. Ordinary kernel reduction checks the merges; separate named lemmas use
`decide +kernel` for sortedness and maximum runs. These checks are distributed
among modules. Thus the expensive global
generator/sorter reduction is replaced by small leaf enumerations and linear
streaming checks. The producer is ordinary Python, but all its outputs are
verified by the kernel and are absent from the theorem assumptions.

Combining the 105 transferred failures with the proved permanent tails gives
all 77 remaining identities. Case splitting against the infinite ranges
proves `conj52a`, `conj52b`, and `conj52c`. The original table's extra exact
numerical values in the already-covered range n=35..37 are independently
checked as described above; the universal Lean endpoints use stability there
and do not require those additional numerical minima. The three full
endpoints and uniqueness use only `propext`, `Classical.choice`, and `Quot.sound`.

## Prior art and significance

The independent adversarial review (Claude Opus, 20 November 2026) found no
public resolution. Its bounded search checked Principia's id list and cached
clone; current Omega issue searches for the arXiv id, title terms, and MathDB
id; a GitHub code search whose only hit was a bare arXiv-id list; the arXiv
version history; OpenAlex citing works; indexed web sources; and OEIS A317254
and its cross-references. The single located citing work, Youmbai, Zargar and
Voznyy, arXiv:2408.13867 (2025 journal version), concerns fixed triples and
elliptic curves and does not resolve these tail-threshold identities. The
review found no formula or resolution in OEIS A317254, which is labelled
“more, hard”. The zbMATH review of the journal source says the numerical
conjectures are still stated there.

The journal body was not read: World Scientific refused access. No refusal
was bypassed or retried here. The discovery search also recorded unavailable
current full Omega Blueprint content, the Kelly AMS PDF, and several denied
or rate-limited scholarly services. No acceptance date for the source journal
article was located. These limits prevent a claim of an exhaustive priority
search. This implementation stage relies on the supplied review and does not
claim a new live registry search of its own.

The quantitative low-sum collision family is the ingredient absent from the
source's one-sided appending inequality. A finite table alone cannot settle
the universal statements, and the structural low-sum argument does not apply
to the small range where the thresholds exceed 2n. The written proof therefore
needs both construction and exhaustive base certificates. Nevertheless, the
infinite construction is elementary and short, and the finite part implements
the source's own algorithm. The review explicitly flagged borderline
routine/novelty significance; root must adjudicate that question. This packet
claims formal completion of the three specified conjectures, while leaving
priority and the routine/novelty assessment to independent review.

## Reproduction

The retained `partition-small-results.json`, `partition-stability-families.json`
and `scripts/verify_partition_stability.py` reproduce the written finite
calculation with `python3 -I` from this folder. `LEAN-SOURCE-APPENDIX.md`
contains every retained production module, byte-identical to `src/`, in
import order. The copied 32 GiB runners and PINS.json specify the trusted
Lean/Mathlib environment. REPORT.md records the full clean rebuild time and
every compile and standalone kernel-check receipt.
