# Source contracts and reading boundaries

Author: Myeongjin Kang, no affiliation. Original commentary CC BY 4.0.

The upstream commit is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
The complete `preprints-tree.json` has 13,223 entries and `truncated: false`.
It was parsed, not treated as a truncated root-tree cache. Every retained
pinned blob is checked against its tree SHA1 in `retrieval-pinned.json` and
again by the read-only verifier. SHA256 and sizes are in the input manifest.

The primary family base URL is
<https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/>.
The following exact file URLs and read extents specify the contract.

* [build/introduction.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/build/introduction.tex): full text read. `thm:signing` is the all-d,N, all unit-ball vectors, ONE prescribed-order signed-prefix theorem. `thm:steinitz` is a free ordering of a zero-sum indexed family. No arbitrary second prescribed order is stated. The transference proof and historical distinctions were read.
* [build/assembly.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/build/assembly.tex): entire file read, including `prop:adaptive`, `prop:filtered`, `lem:slab-energy`, and the full signing construction. The identity `eq:predictor-columns`, the all-diagonal estimate `eq:predictor-weighted-cost`, and `eq:feedback-cancellation` are the exact operation interfaces reconstructed in candidate §§2–5. Initial state coordinates, zeroing x^0, distinct noise axes, strict predictor slabs and clipping removal are retained.
* [build/signing.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/build/signing.tex): full file and proofs read. `lem:simultaneous-density` uses all positive diagonal Q and separation; `lem:shift-section` preserves energy under a lifted symmetrization; `prop:adaptive` concludes by backward domains and forward causal shifts. None permits incompatible future-dependent shifts assigned to one coordinate.
* [build/survival.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/build/survival.tex): full file and proofs read, including `lem:ou-energy`, `lem:epoch-prob`, and the full proof of `prop:filtered`. Gaussian correlation controls continuous linear path events; it supplies no correlation law on the final sign choices.
* [build/brownian.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/build/brownian.tex): full file and proofs read. `lem:brownian-rate`, `lem:gaussian-path-correlation`, and the slab-energy proof clarify that intersections cost continuous survival energy, not a discrete sign-intersection argument.
* [build/matrix.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/build/matrix.tex): lines 1–75 read; all labels and relevant order/permutation terms searched. In particular `eq:speed-recursion` and `eq:trace-budgets` require a genuinely new noise coordinate and give a trace loss/gain budget. The remaining technical matrix proofs were not fully read. Their stipulated filtered-body conclusion is used with all hypotheses; no extension beyond it is assumed.
* [build/consequences.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/build/consequences.tex): full file and proofs read, especially `cor:colorful-steinitz` and `cor:lp-steinitz`. The colorful claim allows each row's permutation to be chosen and controls synchronous aggregate prefixes; it is not a theorem about the same signs in two fixed orders.
* `build/references.bib`: the bibliography entries exposed with the introduction/consequences retrieval were inspected; not all cited papers were independently read. `build/main.tex` and README were retained and searched, not proof inputs.

The only other top-level tree match for the bounded filename terms was
[Prefix-Instructions-and-Incompressible-Flows/README.md](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Prefix-Instructions-and-Incompressible-Flows-September-27-2026/README.md).
That README was read. Its catalogue abstract was also read and identifies a
fluid-computation construction, not vector balancing. No theorem of that
paper is used. Catalogue excerpts for Foulkes and the three hyperbolicity-cone
papers were selection screens only; their theorem proofs were not read or
invoked. This distinction prevents treating catalogue summaries as premises.

Context: AGENTS.md, upstream pin, the campaign ledger, the twenty-findings
ledger, all four current accepted finding records R023–R026 and the entire
poly-zp contribution review were read. Earlier R001–R022 records were retained
and their leading claim sections screened for overlap; not every old
publication package was re-audited. The catalogue's 372 numbered result
headings were screened, and abstracts for the short-listed structural
families were read. The entire catalogue was retained, not claimed to have
been proof-read. The explicit user exclusions are binding independently of
whether their older full packages were read.

Primary external texts:

* Donald E. Knuth, *Two-way rounding*, SIAM J. Discrete Math. 8 (1995), 281–290. Author-hosted [TeX](https://www-cs-faculty.stanford.edu/~knuth/papers/twr.tex). The server returned a gzip stream; the original response is retained unchanged as `knuth-twr.tex`, and `knuth-twr-decoded.tex` is its decompressed text. Read the initial lemma and its full network-flow proof, following corollary, through the Theorem 1/2 discussions, and Theorem 3 statement/proof opening. The remainder was not fully read. The exact publication metadata was checked at [SIAM](https://epubs.siam.org/doi/10.1137/S0895480194264757). Rounding-error sums are unweighted; applying the lemma coordinatewise need not share a signing.
* Victor Reis, *Vector Balancing and Integer Programming*, University of Washington PhD dissertation, **2023** (verified title page). [Institutional PDF](https://digital.lib.washington.edu/server/api/core/bitstreams/a92e53bd-06e4-4b1d-9221-51ba75b0aded/content). Title/metadata and Chapter 8 printed pp.120–124 read, with complete proofs at those pages. PDF pages 130–132, printed pp.122–124, rendered and visually inspected. Extraction text lines 6320–6550 cover the operative material. Its conjectural universal weighted bound is not assumed as a premise. Web crawl age is not publication year.
* Jiří Matoušek, Aleksandar Nikolov, Kunal Talwar, *Factorization Norms and Hereditary Discrepancy*, [arXiv:1408.1376v2](https://arxiv.org/pdf/1408.1376v2). Read introduction factorization definition and triangular example, §2.1 Theorem 2.4, and §4.1 complete direct spectral proof of Proposition 4.1, through its characteristic-polynomial discussion. PDF pp.16–17 rendered and inspected. The second Fourier proof and the rest of the paper were not fully read. This primary text explicitly credits the triangular spectrum calculation; candidate §4 reproduces it rather than claiming it.
* Kristóf Bérczi, Siyue Liu, Victor Reis, Jakub Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, [arXiv:2608.13983v1 HTML](https://arxiv.org/html/2608.13983v1). Read introduction through §1.1 (web-extracted lines 41–144), including the actual prefix-basis, weighted-carpooling and prefix Beck–Fiala statements. Later sections were retained as HTML but not fully read or used. This external post-pinned reference is comparison evidence only.

No external theorem about the status of T2 is inferred from these bounded
readings. All new supporting propositions have standalone proofs in
candidate.md. Their ordinary linear-algebra and factorization cost is stated
explicitly; they are not nominated as substantial corollaries.
