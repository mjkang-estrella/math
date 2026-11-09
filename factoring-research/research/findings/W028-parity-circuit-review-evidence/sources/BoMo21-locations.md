# BoMo21 locations checked

PDF SHA-256 `9643b42053b86f41a376af10aa040c761d5a907fc946d2b0e65d05069c7d7029`.
`pdfinfo`: 15 pages, producer pdfTeX-1.40.17, creation date Thu Nov 26 09:48:30 2020 PST.

Two `pdftotext` extractions of this same file disagree with the parent locator "lines 454–548, including the effective-ring setup".

| Extraction | Effective ring (footnote 0) | Algorithm 1 and the unit-constant proof |
| --- | --- | --- |
| `pdftotext` default, 2111 lines | lines 38–39 | assumptions and body about 421–470; "Q(0) invertible" at 399–403; "V(0)=Q(0)^2 is invertible" at 472–474 |
| `pdftotext -layout`, 1138 lines | lines 48–52 | Algorithm 1 at 269–293; unit-constant argument at 253–340 |

Default-extract lines 454–548 are a two-column scramble. They contain the tail of Algorithm 1, the Graeffe remark, the sentence that V(0) stays invertible, and the start of the Fibonacci example. They do not contain footnote 0.

The mathematical claim survives the locator. Footnote 0 defines a commutative unital effective ring with operations +, −, × and equality tests. Section 2.1 says that Q(0)=1 is the normalized case and that the algorithm assumes only that Q(0) is invertible. Algorithm 1's printed assumptions are: Q(0) invertible and deg(P) < deg(Q) = d. The body multiplies P(x)Q(−x) and Q(x)Q(−x), keeps one parity, and replaces the index by its floor half. The return value is P(0)/Q(0), one division by a unit. The stated cost is 2 M(d) ceil(log(N+1)) arithmetic operations. Theorem 1 takes the order-d recurrence coefficients and d initial terms as input.

Footnote 8 says the same method computes the Nth Fibonacci or Chebyshev polynomial in O(M(N)) operations, which the paper calls quasi-optimal. That is a dense-output cost linear in the index, not an O(log N) scalar extraction for a recurrence whose order grows with N.
