# The exact sign table for the square partition inequality

## Statement and source

For each integer \(t\geq 0\), let \(P(t)\) count unordered partitions of \(t\) into positive perfect squares, with unrestricted multiplicities. The partition of zero is the empty multiset. For positive integers \(a,b\), put \(m=\min(a,b)\), \(n=\max(a,b)\). The sign of \(P(a)P(b)-P(a+b)\), taken in the integers, is given by the following table.

| \(m\) | Equality values of \(n\) | Failure values of \(n\), meaning \(P(a)P(b)<P(a+b)\) |
|---|---|---|
| 1 | 1, 2, 4, 5, 6, 9, 10, 13, 14, 18, 22 | Every other \(n\geq1\) |
| 2 | 4, 5, 9, 13 | Every other \(n\geq2\) |
| 3 | 4 | Every other \(n\geq3\) |
| 4 | 5, 6, 7 | None |
| 5 | 5, 6, 8, 11, 15 | 7 |
| 6 | 8, 10, 12, 14 | 6, 7, 11, 15 |
| 7 | 8, 9, 12, 13, 19 | 7, 10, 11, 14, 15 |
| \(m\geq8\) | None | None |

The product is strictly greater at every pair outside the equality and failure columns. There are 33 equality pairs and 10 failure pairs with \(m\geq4\), counted on \(m\leq n\).

This is the classification in MathDB 362601, whose retained statement gives the equality lists and refers to the source for failure. The source is Arindam Roy, *Log-concavity and the Multiplicative Properties of Restricted Partition Functions*, arXiv:2404.03153v4, dated 10 May 2025, §3.1 and Conjecture 3.2, Table 2 on p. 10. Both columns are headed \(n\geq m\). The failure exclusions \(n=1\) at \(m=2\) and \(n=1,2\) at \(m=3\) are below that domain. The failure cell at \(m=4\) is blank.

## Counting by the multiset of parts greater than one

Let \(F_t\) consist of the multisets of squares at least 4 whose sum is at most \(t\). Write \(\operatorname{wt}(x)\) for the sum of a multiset, \([q]\) for one copy of \(q\), and use \(+\) for multiset addition. Every part of a square partition is either 1 or belongs to the allowed set for \(F_t\). Delete all ones. Conversely, for \(x\in F_t\), insert exactly \(t-\operatorname{wt}(x)\) ones. The two operations are inverse on multisets, including multiplicities. In particular \(P(t)=|F_t|\), and \(F_t\subseteq F_{t+1}\) makes \(P\) nondecreasing. Finiteness also follows directly since each part is positive, at most \(t\), and occurs at most \(t\) times. At \(t=0\) the unique multiset is empty.

## The first suffix below the weight bound

Fix \(1\leq m\leq n\) and \(x\in F_{n+m}\). If \(\operatorname{wt}(x)\leq n\), set its image to \((x,\varnothing)\). For every other \(x\), sort its parts in nonincreasing order and delete the shortest prefix leaving a suffix \(y\) of weight at most \(n\). The empty suffix guarantees existence. Write the deleted prefix as \(U+[w]\), where \(w\) is the last removed part, and write \(h=n-\operatorname{wt}(y)\). The preceding suffix weighed \(\operatorname{wt}(y)+w>n\), so
\[
  0\leq h<w,\qquad \operatorname{wt}(U)+w-h\leq m.
\]
The sorted order makes every part of \(U\) at least \(w\) and every part of \(y\) at most \(w\). If equal values straddle the cut, the prefix length fixes their multiplicities on each side. The data \((y,U,w)\) recover \(x=U+[w]+y\).

For a fixed \(y\in F_n\), let \(s\) be the least integer \(s\geq2\) with \(s^2>h\) and \(q\leq s^2\) for every part \(q\) of \(y\). Large \(s\) exist. The root of any last removed part satisfies these conditions, so \(w=(s+j)^2\) for a unique \(j\geq0\). The case \(s=2\) requires \(y\) to consist entirely of fours and \(h\leq3\). It is equivalent to \(y=y_0=\lfloor n/4\rfloor[4]\), whose slack is \(n\bmod4\). Call all other remainders ordinary.

## Bulk range \(m\geq8,\ n\geq24\)

We code every crossing input as \((y_*,C)\in F_n\times F_m\) with \(C\ne\varnothing\), and recover it by a decoder. The identity inputs already use the empty second coordinate.

For an ordinary remainder \(y\), keep \(y_*=y\), so its \(s\geq3\) is known to the decoder. If \(j=0\) and \(U\ne\varnothing\), take \(C=U\). Its weight is at most \(m\), and its parts are at least 9. If \(j=0\) and \(U=\varnothing\), take \(C=[4]\), of weight \(4\leq m\). Both cases decode by adjoining \([s^2]+y\) to the recovered \(U\).

For \(j\geq1\), let \(v=(j+1)^2\) and use \(C=U+[v]+k[4]\), with \(k=1\) for \(s=3,4\) and \(k=2\) for \(s\geq5\). Since \(h\leq s^2-1\),
\[
 w-h-v \ \geq\ (s+j)^2-s^2+1-(j+1)^2
           \ =\ 2(s-1)j \ \geq\ 4k.
\]
The last inequality uses \(s\geq3\) for one marker and \(s\geq5\) for two. Thus the weight is at most \(m\). There are at least two parts and a four, identifying this format. Remove exactly \(k\) occurrences of 4, then the smallest remaining part is \(v\), since \(v<w\) and all of \(U\) is at least \(w\). Its root gives \(j=\sqrt v-1\). Erase one occurrence of \(v\) to recover \(U\). This also works when \(v=4\), since one four is left after marker deletion. For \(s=3,4\) there are at most two fours. For \(s\geq5\) the two-four multiset \(2[4]\) is unavailable to every ordinary code, and the only ordinary code with exactly one four is the singleton \([4]\).

For \(y=y_0\), write \(y'=y_0-[4]\) for deletion of one copy of 4. This is defined since \(y_0\) has at least six fours. Use the following codes, where \(b\) is the positive integer root of \(w\).

| \(w\) | \(U\) | \(y_*\) | \(C\) |
|---|---|---|---|
| 4 | Nonempty | \(y_0\) | \(U\) |
| 4 | Empty | \([4]\) | \(2[4]\) |
| 9 | Nonempty | \(\varnothing\) | \(U+[4]\) |
| 9 | Empty | \(\varnothing\) | \(2[4]\) |
| 16 | Any | \(y'\) | \(U+3[4]\) |
| 25 | Any | \(y'\) | \(U+3[4]+[9]\) |
| \(b^2,\ b\geq6\) | Any | \(y'\) | \(U+4[4]+[(b-2)^2]\) |

Each first coordinate has weight at most \(n\). For \(w=4\) with \(U\ne\varnothing\), \(U\) fits by the crossing bound. The two double-four codes cost 8. For \(w=9\) with \(U\ne\varnothing\), the added 4 is at most \(9-h\). The costs 12 and 21 at 16 and 25 are at most \(16-h\) and \(25-h\) since \(h\leq3\). In the last row \(b^2-16-(b-2)^2=4b-20\geq4>h\), giving the required weight bound.

The remainders \(y_0,y',\varnothing,[4],2[4]\) are distinct by their cardinalities. The slack of \(y'\) is \(4,\ldots,7\), so its ordinary root is 3 and ordinary codes there have at most two fours. The slacks of \(\varnothing,[4],2[4]\) are at least 16, so their ordinary roots are at least 5. Consequently the double four at \([4]\) and the double four or nonsingleton one-four code at \(\varnothing\) are reserved for the transported inputs. They identify \(w\) and \(U\) by the table, removing the marker at \(\varnothing\) when needed. A nonempty second coordinate at \(y_0\) recovers \(w=4\) and \(U=C\). At \(y'\), exactly three fours distinguish the 16 and 25 cases from the \(b\geq6\) case. After deleting three fours, the presence of a 9 identifies 25, since \(U\) has parts at least \(w\). Erase that 9 in the 25 case to recover \(U\). In the last row, delete four fours and take the least remaining part, which equals \((b-2)^2<b^2\). It gives \(b\) and can then be erased. Each transported input is recovered using \(y_0\) as its original suffix.

This decoder proves injectivity. The pair \((2[4],2[4])\) is admissible because \(m\geq8\) and \(n\geq24\). It has nonempty second coordinate, its first coordinate is unused by exceptional transports, and its second coordinate is omitted by ordinary codes at that first coordinate. The injection is therefore nonsurjective, and finiteness gives \(P(n+m)<P(n)P(m)\).

## Thin range \(4\leq m\leq7,\ n\geq52\)

Now \(F_m=\{\varnothing,[4]\}\). Retain the identity branch. For ordinary \(y\), \(j\geq1\) would give \(w-h\geq(s+1)^2-s^2+1=2s+2\geq8\). Any nonempty \(U\) would already weigh at least 9. Thus any crossing with this \(y\) has \(U=\varnothing\) and \(w=s^2\), and \((y,[4])\) decodes it by adjoining \([s^2]\). At \(y_0\) the crossing with \(w\geq16\) is impossible by \(h\leq3\). For \(w=9\) the prefix \(U\) must be empty. For \(w=4\), \(U\) is empty or \([4]\) because its weight is at most \(m-(4-h)\leq6\). Keep \((y_0,[4])\) for the case with \(U=[4]\).

For \(L=25,36,49\), let \(z_L=\lfloor(n-L)/4\rfloor[4]\) with slack \(h_L=L+((n-L)\bmod4)\). The three slacks lie in disjoint intervals \([25,28]\), \([36,39]\), \([49,52]\), all above the slack of \(y_0\). They are attainable since \(n\geq52\). A zero quotient gives the empty multiset. The least squares strictly above those intervals are 36, 49, 64, respectively. Any crossing leaving one of these remainders would have \(w-h_L\geq8,10,12\), respectively, which exceeds \(m\). Therefore all three pairs \((z_L,[4])\) are available. Send \(w=4,U=\varnothing\) at \(y_0\) to \((z_{25},[4])\), and \(w=9,U=\varnothing\) there to \((z_{36},[4])\). These pairs recover the stated data. The pair \((z_{49},[4])\) is omitted by the whole injection, proving the same strict inequality.

## The first three rows

For \(1\leq m\leq3\), \(P(m)=1\) since the only allowable part is 1. At each \(t\geq1\), deleting one occurrence of 1 from partitions that contain it is a bijection with square partitions of \(t-1\). Consequently \(P(t)-P(t-1)\) counts partitions of \(t\) without ones. Below 24, representability by squares at least 4 reduces to representability by 4 and 9, since 16 can be replaced by four fours and 25 is too large. For residues \(0,1,2,3\) modulo 4, the minimum number of nines is \(0,1,2,3\), respectively, with weights \(0,9,18,27\). All values in each residue at or above its minimum are obtained by adding fours. The four consecutive values \(24,25,26,27\) are \(6\cdot4,4\cdot4+9,2\cdot4+2\cdot9,3\cdot9\), and adding fours proves representability for every larger total. Thus the positive gaps are exactly
\[
 \{1,2,3,5,6,7,10,11,14,15,19,23\}.
\]
The increment from \(P(n)\) to \(P(n+m)\) vanishes precisely when \(n+1,\ldots,n+m\) are all gaps. For \(m=1\) use the gaps at least 2 and subtract 1. For \(m=2\) the consecutive pairs beginning at least at 3 start at \(5,6,10,14\). For \(m=3\) the only consecutive triple beginning at least at 4 starts at 5. These give the three equality lists. Every other window includes a positive increment, so there is strict failure.

## Finite verification by hand

It remains to check \(4\leq m\leq7,\ m\leq n\leq51\), and \(8\leq m\leq n\leq23\). All sums in those regions are at most 58. With the ones handled by padding, the coefficient \(Q(t)\) counting just fours and nines is
\[
 Q(t)=\sum_{i=0}^{\lfloor t/9\rfloor}\bigl(1+\lfloor(t-9i)/4\rfloor\bigr)
 \quad (t\geq0).
\]
Use zero for every count at a negative argument. On adjoining a new allowed part \(d\), the count becomes \(A_{\rm new}(t)=A_{\rm old}(t)+A_{\rm new}(t-d)\), by separating the multisets lacking \(d\) from those from which one \(d\) can be removed. Equivalently sum over its multiplicity. For \(0\leq t\leq58\), first set \(B(t)=Q(t)+Q(t-16)+Q(t-32)+Q(t-48)\). Then
\[
 P(t)=B(t)+B(t-25)+B(t-50)+B(t-36)+B(t-49),
\]
because 36 and 49 each occur at most once there, and each precludes 25 and the other. No square above 49 fits. This gives the following consecutive coefficients.

| Start | \(P(t)\) |
|---|---|
| 0 | 1 1 1 1 2 2 2 2 3 4 |
| 10 | 4 4 5 6 6 6 8 9 10 10 |
| 20 | 12 13 14 14 16 19 20 21 23 26 |
| 30 | 27 28 31 34 37 38 43 46 49 50 |
| 40 | 55 60 63 66 71 78 81 84 90 98 |
| 50 | 104 107 116 124 132 135 144 154 163 |

For each \(4\leq m\leq7\), the following differences \(2P(n)-P(m+n)\) run from \(n=m\) to \(n=19\).

| \(m\) | Differences |
|---|---|
| 4 | 1 0 0 0 1 2 2 2 2 3 2 2 4 5 6 6 |
| 5 | 0 0 −1 0 2 2 0 1 2 2 0 3 4 6 4 |
| 6 | −1 −2 0 2 0 −1 0 2 0 −1 2 4 4 1 |
| 7 | −2 0 0 −1 −2 0 0 −1 −2 2 2 1 0 |

For \(20\leq n\leq51\), on each interval \([l,u]\), use \(2P(l)\leq P(m)P(n)\) and \(P(n+m)\leq P(u+7)\).

| Interval | \(2P(l)>P(u+7)\) |
|---|---|
| 20, 21, 22, 23, 24 as singletons | \(24>21,\ 26>23,\ 28>26,\ 28>27,\ 32>28\) |
| 25–27 | \(38>37\) |
| 28–29 | \(46>43\) |
| 30–32 | \(54>50\) |
| 33–36 | \(68>66\) |
| 37–41 | \(92>90\) |
| 42–46 | \(126>124\) |
| 47–51 | \(168>163\) |

For \(8\leq m\leq n\leq23\), use the product at the lower endpoints and the count at the sum of the upper endpoints. Intersect each rectangle with \(m\leq n\).

| \(m\) | \(n\) intervals in order | Lower product \(>\) upper count |
|---|---|---|
| 8 | 8, 9–11, 12–15, 16–19, 20–23 | \(9>8,\ 12>10,\ 15>14,\ 24>21,\ 36>28\) |
| 9–11 | 9–11, 12–14, 15, 16–19, 20–23 | \(16>14,\ 20>19,\ 24>20,\ 32>27,\ 48>37\) |
| 12–15 | 12–13, 14–15, 16–19, 20–23 | \(25>23,\ 30>27,\ 40>37,\ 60>49\) |
| 16–23 | 16–19, 20–23 | \(64>63,\ 96>81\) |

The short differences give exactly the zeros and negatives in rows 4 through 7. The remaining finite comparisons are strict. Together with the first three rows and the two injections these cover all \(1\leq m\leq n\). Commutativity of addition and multiplication proves the classification for all positive \(a,b\).

## Lean certificate and independent replay

The [Lean source appendix](LEAN-SOURCE-APPENDIX.md) contains the 14 canonical modules in build order. It is byte-identical to the frozen appendix, SHA-256 d305f6140abb1b06364dc88ded7ab46a5b010f8de95c746b6cbe9c53dfe95416. The endpoint is Roy362601.restricted_sign_table in Certificates.lean. For the predicate Sq q defined as the existence of a natural \(r\geq1\) with \(q=r r\), its count is the cardinality of Nat.Partition.restricted t Sq. The predicate is decidable by finite search up to \(q\), since \(r\leq r^2=q\) for a witness. The theorem requires only positive \(a,b\) and a decision procedure for Sq, and gives the equality, strict failure and strict success equivalences using min and max. A [crosswalk](CROSSWALK.md) ties the statement and proof pieces to declarations.

Lean checks the counting bijections, the cutoff, the code constructors and left inverses, and the omitted outputs of the injections. The named encoders use classical choice over proved witnesses. For the finite region, the formal proof counts multisets by allowed parts, proves the erase/insert recurrence, and identifies the count at \(t\leq58\) with C t, a fuel-bounded recurrence proved equal to the well-founded recurrence. The kernel checks the coefficient vector and the finite signs by decide on exact arithmetic. Its finite hypothesis also covers the small rows with \(n<23\). Small.lean checks the positive gaps through 23 through the same recurrence, proves representation from 24 onward by adding fours, and proves the small-arm tail from \(n\geq23\). The hand calculation above uses the explicit gap residue argument and monotone rectangles. The formal certificate decides the bounded comparisons directly.

The independent extraction started with empty or absent source, build and cache directories. All 14 exact source hashes and all fresh olean hashes matched the canonical replay. Each module was compiled and separately kernel-checked before moving to the next. The exact Lean audit output matched, and all 57 audited declarations use only propext, Classical.choice and Quot.sound or a subset. Lean 4.34.1 and mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612 were the pinned environment. Pin verification covered the two binary hashes and available mathlib source metadata. The prebuilt upstream oleans are trusted dependencies.

The result addresses Roy v4's square comparison. It provides explicit finite-to-infinite boundaries and strictness by a combinatorial argument, whereas Roy v4 Theorem 3.1 gives an eventual inequality. Roy's Springer final, DOI 10.1007/s00026-026-00847-5, is held after the recorded robots HTTP 406. Current registry freshness remains held. The evidence supports the proof and the retained native statement. Priority and campaign acceptance remain open.
