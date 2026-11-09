# 367397: independent replay. Publicly resolved; NO credit.

Bosma et al. (arXiv:2503.04122v1, Conjecture 5) is proved in full by O. Shtrezi,
arXiv:2606.17447v1 (13 Jun 2026), Theorem 1. That paper's title is "The greedy
3-sumfree sequence S_{1,g,g+1}". It is retained at
`sources/c367397-successor-pdf/body`, sha256 `2d7ca98f…7b8a`, and its proof is
described as a "direct interval-sumset argument". This lane derived the argument
below before finding that paper. It is kept only as an independent confirmation. It
is not a proposal.

## Setup

- m = 10g+3.
- A = [g, 2g] and B = [6g+2, 7g+1]. These are the residue blocks.
- T = {1, 2g+1, 6g+1} ∪ {z ≥ 1 : z mod m ∈ A ∪ B}.

The greedy sequence S satisfies S ∩ [1, g+1] = {1, g, g+1}. For z > g+1, z ∈ S iff z
is not a sum of three distinct elements of S smaller than z. By strong induction, T
equals S if T satisfies the same three properties (I)–(III) below.

## Proof

**(I) Initial segment.** T ∩ [1, g+1] = {1, g, g+1}:
- 1 is special.
- g and g+1 lie in A, since g ≥ 2 gives g+1 ≤ 2g.
- 2, …, g−1 have residues below g.

**(II) Elements of T are not sums.** Specials can be used at most once each. Sums of
three residues from A ∪ B ∪ {1, 2g+1, 6g+1}, reduced mod m:

| Combination | Integer range | Range mod m |
|---|---|---|
| AAA | [3g, 6g] | [3g, 6g] |
| AAB | [8g+2, 11g+1] | [8g+2, 10g+2] ∪ [0, g−2] |
| ABB | [13g+4, 16g+3] | [3g+1, 6g] |
| BBB | [18g+6, 21g+3] | [8g+3, 10g+2] ∪ [0, g−3] |
| 1+AA | [2g+1, 4g+1] | same |
| 1+AB | [7g+3, 9g+2] | same |
| 1+BB | [12g+5, 14g+3] | [2g+2, 4g] |
| (2g+1)+AA | [4g+1, 6g+1] | same |
| (2g+1)+AB | [9g+3, 11g+2] | [9g+3, 10g+2] ∪ [0, g−1] |
| (2g+1)+BB | [14g+5, 16g+3] | [4g+2, 6g] |
| (6g+1)+AA | [8g+1, 10g+1] | same |
| (6g+1)+AB | [13g+3, 15g+2] | [3g, 5g−1] |
| (6g+1)+BB | [18g+5, 20g+3] | [8g+2, 10g] |
| 1+(2g+1)+A | [3g+2, 4g+2] | same |
| 1+(2g+1)+B | [8g+4, 9g+3] | same |
| 1+(6g+1)+A | [7g+2, 8g+2] | same |
| 1+(6g+1)+B | [12g+4, 13g+3] | [2g+1, 3g] |
| (2g+1)+(6g+1)+A | [9g+2, 10g+2] | same |
| (2g+1)+(6g+1)+B | [14g+4, 15g+3] | [4g+1, 5g] |
| all three specials | 8g+3 | 8g+3 |

None of these ranges meets A ∪ B. So no element with residue in A ∪ B is a sum of
three distinct elements of T.

The two remaining specials are also not sums of three distinct smaller elements:
- 2g+1: the smallest such sum is 1 + g + (g+1) = 2g+2.
- 6g+1: the smaller elements are 1 and [g, 2g+1]. The largest sum of three distinct
  ones is (2g+1) + 2g + (2g−1) = 6g < 6g+1.

**(III) Non-elements are sums.** Let z ∉ T with z > g+1.

At level 0 (z < m):
- [2g+2, 4g+2]: z = 1 + a + b with a < b in [g, 2g+1].
- [3g+3, 6g]: z is a sum of three distinct elements of [g, 2g+1].
- [7g+2, 10g+2]: z is covered by 1 + (6g+1) + A' = [7g+2, 8g+3], by
  1 + B + [g, 2g+1], and by (6g+1) + (pairs from [g, 2g+1]) = [8g+2, 10g+2].

At level q ≥ 1, write z = qm + r:
- r ∈ [2g+1, 6g+1]: z = (x+qm) + s1 + s2 with x ∈ A, and s1 < s2 from
  {1} ∪ [g, 2g+1]. These pair sums fill [g+1, 4g+1].
- r ∈ [7g+2, 10g+2]: x ∈ A, with pair sums from W = {1} ∪ [g, 2g+1] ∪ [6g+1, 7g+1].
  These fill [6g+2, 9g+2].
- r ∈ [0, g−1]: z = (x + (q−1)m) + s1 + s2 with x ∈ B and s1 ≠ s2 in [g, 2g+1].
  Then x + s1 + s2 fills [8g+3, 11g+2], which contains [m, m+g−1].

In every case the three summands are distinct and smaller than z. ∎

## Machine check (not the proof)

`checks/c367397_greedy_and_lemmas.py`:
- the greedy sequence equals T for g = 2..40, up to 12m;
- every residue lemma above holds for g = 2..120;
- exit 0.
