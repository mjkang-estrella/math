# Prior-art scope for the W030 digit-kernel product

Searched on 2026-10-09 UTC. The question was whether a published algorithm computes the scalar

\[
\prod_{i,j}\Bigl(1-r_i s_j\prod_k X_{j,k}^{a_{i,k}}\Bigr)\in\mathbb Z/N\mathbb Z
\]

for logarithmic dimension, digits \(a_{i,k}\in\{0,\ldots,\ell-1\}\), and the triangular column recurrence, strictly cheaper than explicit pairs, with localization paid. No broad factoring survey was run.

## Sources opened

1. Van der Hoeven and Lecerf, "Fast multivariate multi-point evaluation revisited", Journal of Complexity 56 (2020). HTML text of the introduction and the complexity-model section was fetched from `https://www.texmacs.org/joris/kucomp/kucomp.html`. Used for: the quotation of Kedlaya–Umans Corollary 4.3; the statement that univariate multipoint is a remainder tree as in von zur Gathen–Gerhard, Chapter 10; the Cartesian-product reduction; the recursive dense representation; the Turing-machine transposition overhead. The fetch truncated during Lemma 2.10. Theorem 5.5 was not re-read from the PDF in this round. The in-project W021 review's paraphrase of that theorem was read only as a neighboring application, lines 1–80 of `W021-quadratic-product-review.md`.

2. Kedlaya and Umans, SIAM J. Comput. 40 (2011), Corollary 4.3, as quoted in source 1. The SICOMP PDF was not reopened. The quoted hypotheses are a supplied polynomial of partial degree \(<d\), \(m\le d^{o(1)}\), \(N\) points, and a RAM bit-cost \((d^m+N)^{1+\delta}\log^{1+o(1)} r\).

3. Bhargava, Ghosh, Guo, Kumar, and Umans, arXiv:2205.00342. Abstract and theorem statement: finite-field multipoint from a coefficient vector, time \((d^m+N)^{1+o(1)}\operatorname{poly}(m,d,\log|\mathbb F|)\), every \(m\), \(d\) large. Proof body not re-derived.

4. Bhargava, Ghosh, Kumar, and Mohapatra, arXiv:2111.07572. Abstract: the same coefficient-vector problem over small characteristic. Proof body not re-derived.

5. Nüsken and Ziegler, arXiv:cs/0403022. Abstract and theorem statement: a bivariate polynomial given by its \(n^2\) coefficients, generic points, field operations, subcubic in \(n\).

6. Bostan and Schost, Journal of Complexity 21 (2005), "Polynomial evaluation and interpolation on special sets of points." The abstract was read through a search snippet, and source 1 cites the geometric-progression bound \(M(n)+O(n)\). The article PDF was not reopened. Used only as a logarithmic improvement inside one geometric orbit.

7. Van der Hoeven and Lecerf, arXiv:2312.17664, sparse interpolation from a modular black box. Abstract and Theorem 1.1 statement. This recovers a sparse support; it does not evaluate the digit product.

8. Bhargava, Ghosh, Guo, Kumar, and Umans, together with Moroz, as summarized by the abstract of arXiv:2304.01191. Numerical and rational-reconstruction multipoint. Excluded as an approximate model.

9. In-project comparator, not re-audited: `W025-consumer-and-cost-frontier.md` lines 1–68, the explicit-anchor envelope \(\widetilde O(K+\sqrt{KT})\). Lines 69–165 were not used.

The monic block decomposition that prices a carry progression on one separable bucket is derived in the review from remainder trees. It is not a named theorem from the list above.

## Hypothesis that fails for the residual kernel

Every dense multipoint theorem above receives the coefficient tensor as input. For \(L\) digit variables and \(b\) rows that tensor has size \((b+1)((\ell-1)b+1)^L\) before any evaluation saving. The product-of-binomials circuit of size \(O(bL)\) is not an accepted input. Cartesian-grid evaluation wants a dense polynomial and a full grid; the columns are \(V\) triangularly related points, and the full digit grid has cardinality \(Q\). A univariate resultant reproduces only the separable product \(\prod(1-r_is_j)\). Sparse evaluation is linear in the number of known terms, and no source gives a support \(o(b)\) for these root digits. Rank-\(L\) factorizations of the exponent matrix produce \(L\) monomial variables and do not multiply the resulting leaf factors.

## What was not searched

Number-field sieve variants, ECM parameter literature, class-group algorithms, and general circuit lower bounds. A miss outside the list above would be a gap in the search, not a proof that no algorithm exists.
