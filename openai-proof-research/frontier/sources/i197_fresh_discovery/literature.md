# I197 primary literature and comparison limits

Completed 2026-10-12. This supersedes the initial statement that no external primary source had been used. Retrieval and reading scopes are hash-bound in [input-authentication.json](../../experiments/i197_fresh_discovery/input-authentication.json). Partial PDF reading is reported as partial, and no such PDF is retained under the full-read-copy permission.

## Corpus 026

Pinned root: [Positive lower density of large prime gaps](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Positive-lower-density-of-large-prime-gaps-September-25-2026/README.md).

Full files read: README; `build/main.tex`; `build/references.bib`; `build/sections/01-introduction.tex`, `02-counting.tex`, `03-moments.tex`, `04-weights.tex`, `05-cancellation.tex`. They are retained under [corpus](corpus/README.md). The full labels used are `thm:main`, `cor:ratios`, `prop:weights`, `lem:adjacent-gaps`, `prop:weight-moments`, `eq:prime-deletion`, `lem:small-first-moment`, `prop:dimension-cancellation`, `prop:mixed-moments`, `lem:arithmetic-1`, `lem:arithmetic-2`, and `lem:singular-average`.

**Source fact:** the source proves single-gap ordinary lower index density at every fixed threshold and supplies one-mark smooth-divisor-sum moments, a uniform external detector bound and cancellation making a marked interval's prime mass arbitrarily small. **Our inference:** the same operations on a finite union of cells give the technical chain deduction proved in the analytic record. The source statement itself is not represented as already stating that chain theorem.

## Retrieved external primary sources

**Ford, Maynard and Tao, [Chains of large gaps between primes, arXiv:1511.04468v1](https://arxiv.org/pdf/1511.04468v1).** Read PDF pages 1–3 and 5–7, including Theorem 1, Theorem 2, Lemma 3.1 and the page 7 extraction. Theorem 1 concerns the extremal statistic G_k(X), with scale `k^{-2} log X log_2 X log_4 X/log_3 X`; it does not assert positive ordinary index proportion. The proof excerpt uses one-prime lower bounds, pair upper bounds, first/second moments and removal of nearby pairs. This is methodological overlap, not a proof that our density statement is verbatim known. The paper's account of Maier and Pintz is read as that account; their original proofs were not retrieved here.

**Bazzanella, Languasco and Zaccagnini, [Prime numbers in logarithmic intervals, arXiv:0809.2967v1](https://arxiv.org/pdf/0809.2967v1).** Read PDF pages 1–6, including Theorems 1–6 and the definitions distinguishing integer-start B_1 and prime-start A_1. Theorem 5 gives a prime-start lower proportion in its restricted small-threshold range, while Theorem 3 treats empty integer-start intervals and Theorem 6 has additional tail assumptions. No all-threshold multi-gap ordinary-density theorem was supplied by these inspected statements.

**Mastrostefano, [Positive proportion of short intervals containing a prescribed number of primes, arXiv:1812.11784v1](https://arxiv.org/pdf/1812.11784v1).** Read PDF pages 1–3: Theorems 1.1–1.5, definitions and the beginning of section 3 through (3.6). Theorem 1.1 gives positive integer-start proportion with a prescribed total count m for sufficiently small length parameter depending on m. The section 3 score works with well-spaced admissible tuples. Neither this statement nor the inspected proof supplies a lower bound for a product of prescribed-window counts under our separately constructed suppression weight.

The live arXiv submission histories were checked for these three IDs; the displayed records list v1 only. The failed inherited v2 retrievals for the first two papers are retained in the failure record. A published Cambridge version appeared in the search results; its proof was not read or substituted for v1.

## Search chronology and limits

Before proof selection, searches included `chains large gaps positive proportion primes`, `consecutive prime gaps positive density large`, `Maier chains large gaps consecutive primes theorem` and `Ford Maynard Tao chains large gaps 1511.04468`. After the two routes took shape, the search was repeated for `prime gaps chains positive lower density`, `consecutive large gaps positive proportion primes`, `prime gaps prescribed positive proportion`, and `Mastrostefano Positive proportion of short intervals`.

Searches located the classical chain paper, the exact-count paper and several secondary or unrelated pages. Secondary summaries, web-generated mathematical pages, and unpinned current OpenAI pages are discovery leads only; they are not theorem dependencies. No absence result is inferred. These are targeted comparisons, not an exhaustive bibliography or worldwide priority certification.

The contribution conclusion is stronger than an absence-of-search claim: the complete Route A proof uses only the accepted analytic operations plus standard finite-union expansion, moment inequalities and chain extraction. It is therefore technical under this project's gate. The prescribed narrow-box target remains unproved, with exact sufficient missing estimates recorded separately.
