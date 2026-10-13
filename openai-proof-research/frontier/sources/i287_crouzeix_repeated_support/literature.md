# I287 — primary literature, collisions, and exact reading scopes

## Pinned complete-Crouzeix inputs

Revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. All results at this revision are stipulated true; no upstream truth audit was performed. The two retained snapshots below were independently retrieved from immutable raw URLs. Their Git blob hashes match the exact entries of `sources/preprints-tree.json`.

- [Direct proof, pinned main.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/main.tex), retained as `direct-pinned-main.tex`. Read lines 37–76, 162–241, 246–284, 286–452, 454–462. Actual labels: `thm:main`, `lem:faber`, `prop:coefficients`, `lem:resolvent`, `thm:domain`, `lem:approx`; equations `eq:R`, `eq:ordered-products`, `eq:weighted-dual`, `eq:diagonal-L2`, `eq:cross-L2`; final positive block comparison. SHA-256 `54a429fe7129b4760b3015fabf2269d4de5fa38aba9539b18542c1df7e58333f`, Git blob `5976502d77febf477933f36f6205c6e1aa6370ae`.
- [Structural companion, pinned main.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-complete-Crouzeix-theorem-September-23-2026/build/main.tex), retained as `structural-pinned-main.tex`. Read lines 92–147, 316–375, 831–966, 977–1065. Actual labels: `thm:structural`, `thm:representation`, `prop:density`, `eq:fiber-equality`, `eq:positive-block`, `eq:projected-densities`, `lem:comparison` and its proof. SHA-256 `8a5de532bd3bd4c0b84cc8114c22175968813a6e984ced0d1bf48011270e621c`, Git blob `2ace452c83a9ceb994a87ae9009441706d90a961`.

The direct manuscript's three nonnegative comparisons algebraically assemble the residual identity used in I242; the combined identity is bookkeeping, not a separately labeled upstream theorem. I287 reads the actual comparisons and realizes their zero residuals directly. The companion's mass-one density represents a similar matrix. The rank-two calculation here uses the original mass-two field; its equality fibers were screened for duplication, not substituted for that field.

## Nearest old construction: Li–Spitkovsky–Shukla and Lawrence

[Li, Spitkovsky, Shukla, *Equality of higher numerical ranges of matrices and a conjecture of Kippenhahn on Hermitian pencils*, LAA 270 (1998), 323–349](https://doi.org/10.1016/S0024-3795(97)00251-6). The publisher abstract was screened. The original full article was not obtained; no original theorem number or full-proof reading is claimed.

[Ben Lawrence, *Examples for the Quantum Kippenhahn Theorem*, arXiv:1809.02779v2](https://arxiv.org/html/1809.02779v2), especially Section 4's displayed six-dimensional LSS matrix. This primary mathematical reproduction supplies the credited base family. Its Section 5 reproduces Laffey's example; the introduction and Lemma 2 distinguish repeated-factor and all-even-spectrum constructions. Sections 4 and 5 were read fully in memory, together with the numbered primary paragraphs listed in the JSON. Raw HTML SHA-256 `fc158711eee63ea9ffcf90d501799b92b3452d7fc7ade2e30d7b02834b2ae269`. No full external section is retained.

The I287 polynomial and compression obstruction are proved independently. The old base pencil and its numerical-range geometry receive no novelty credit. Lawrence's tensor quantization changes the Hermitian pencil; it is not an admissible transformation of a one-variable matrix-polynomial witness.

## Shapiro hypotheses: screened, not imported as a dimension upgrade

- [Shapiro I, author repository](https://works.swarthmore.edu/fac-math-stat/227/), title, bibliographic metadata and primary abstract, web-rendered lines 17–38. Its condition is a linear factor of multiplicity strictly greater than n/3, yielding a common eigenvector. Direct raw HTTP retrieval returned 403; no raw-page hash is claimed.
- [Shapiro II, publisher primary record](https://doi.org/10.1016/0024-3795(82)90212-9), publisher abstract from search retrieval. It discusses the pure quadratic-power case and a linear-times-quadratic form; the displayed pure-power formula was missing in the rendered abstract. A later open returned Internal Error. No unread precise theorem or mixed-factor classification is imported.
- [Shapiro, *Hermitian pencils with a cubic minimal polynomial*, author repository](https://works.swarthmore.edu/fac-math-stat/226/), title, bibliographic metadata and primary abstract, web-rendered lines 17–40. Its hypothesis concerns degree three of the pencil's minimal polynomial; the conclusion is unitary blocks of size at most three. Raw retrieval returned 403. The I287 support pencil has four distinct eigenvalues, so that hypothesis is unavailable.

These are exact primary-abstract read limits, not full-paper reading claims. No Shapiro theorem is a mathematical dependency of the counterexample, and no size-five plug-in corollary is nominated.

## Current Stessin companions and interior-factor warning

[Stessin, *Kippenhahn's conjecture revisited*, arXiv:2603.09915v1](https://arxiv.org/html/2603.09915v1): abstract and entire Introduction; Section 2.2 including Definition 2.22 and Theorem 2.2; Section 3 opening through Theorem 3.1, before subsection 3.1. The theorem assumes an admissible invertible Hermitian tuple with a pure kth-power determinant and additionally tests specified algebra words. Repeated support alone does not satisfy those hypotheses. Raw HTML SHA-256 `c10a1adacdf78b3c3a93b6b0fea80e2f1c726db7cf3eb0faa63c93d994f1b40c`.

[Stessin–Yang, arXiv:2608.14194v1](https://arxiv.org/html/2608.14194v1): primary web-rendered Example 8.2 and the opening through Theorem 8.3/Remark 8.4, with the precise raw read extent in the JSON. Its Waterhouse example has a repeated zero branch and nonzero paired outer branches. That zero branch is interior for a nonzero real pencil; it must not be counted as a repeated maximum. Theorem 8.3 retains additional algebra-word conditions. No result from either preprint supplies or forbids the I287 witness.

For the actual LSS member, I287 proves maximal multiplicity two in every direction and a disk. The larger Laffey example cannot have a disk: its displayed H has diagonal values spanning at least 98, so its horizontal support width is at least 98, whereas its displayed K has width 16. This geometric check produces no finite-polynomial equality witness for Laffey and is not a nomination.

## Closest complete-equality literature and local collision

[Åhag–Czyż–Virtanen, arXiv:2608.27346v3](https://arxiv.org/html/2608.27346v3). Read supplied primary excerpts: Section 5 lines 1–154 (through Proposition 5.4's proof), Section 7 lines 1–98 (complete bound and equality proofs), Section 11 lines 1–137 (through Corollary 11.5's proof). Theorem 5.3 permits orthogonal non-scalar Schmidt supports. Its low-dimensional equality results do not construct a size-six counterexample. Proposition 11.1 concerns scalar polynomial equality; I287's proof of failure of coefficient compression does not need it. Live introduction/version and literal searches for Kippenhahn/Shukla were also screened. The JSON distinguishes inherited excerpt hashes from newly fetched raw bytes.

Accepted R016, I242's full analytic attempt, and the requested independent I245/I246 proof/contribution records were read fully, with exact hashes and line counts in `input-authentication.json`. Their older weighted-chain obstruction attacks scalar output rigidity and still has an extremal scalar input compression. I287 instead excludes every extremal constant scalar input compression of its specified P. R016 remains valid in its accepted size range.

The pinned companions were checked at the actual statement and equality-operation level. Bounded primary-directed searches for LSS/Crouzeix equality, complete equality in size six, coefficient scalarization and matrix inner witnesses found no matching statement among the inspected material. This is a bounded duplication check, not proof of worldwide priority. The claimed increment is the explicit attained polynomial and its exact irreducible rank-two obstruction, subject to independent contribution review.
