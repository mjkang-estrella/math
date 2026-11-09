# Source and novelty review

Review performed by the implementing agent, 2026-10-25. This is not an independent reviewer endorsement.

- Target: MathDB369280, preserved byte-for-byte in `sources/mathdb-369280.json`.
- Primary source: Alexander Clay, *Guessing Strategies for Shelf-Shuffling Machines*, arXiv:2507.10294v1 (14 July 2025). Read Theorem 1.1, Definitions 2.1 and 2.2, their subsequent derivation, and Conjecture 1 from the actual versioned HTML, saved in `sources/`.
- Theorem 1.1 has denominator `2^i`, binomial row parameter `i-1`, and second lower parameter `n-j`. Definitions 2.1 and 2.2 draw from the bottom. The later introductory prose about top-draw machines is not the convention used for this kernel.
- Conjecture 1 specifies all `n>=3` and precisely `n^2-3*n*k+3*k*(k+1)/2-1`. The formal theorem gives the actual nonzero eigenvector predicate plus a separate lower bound of one on eigenspace dimension. It does not claim simplicity.
- Source-to-code indexing is checked by `positionMatrix_one_based` and `quadraticVector_one_based`. All divisions are over the reals; no natural-number division is used in the vector polynomial.

## Literature search and duplicate finding

Queries: `"Guessing Strategies for Shelf-Shuffling Machines" "conjecture"` and `"2507.10294"`. A search result led to Raghavendra Tripathi, *On the position matrix of single-shelf shuffle and card guessing*, arXiv:2602.07920v1 (8 February 2026). The actual primary versioned HTML and arXiv abstract were then read; HTML is saved here. Theorem I gives the spectrum and eigenvectors, including degree two. Taking its degree-two formula and B0=1, B1=-1/2, B2=1/6 gives

`zeta2(k) = (2/3)(n-1)(n-2) - 2(n-2)(k-1) + (k-1)(k-2)`.

Expansion gives `v(k) = (3/2)*zeta2(k)`. Thus the requested mathematical assertion is already a special case of this earlier theorem. The present result is a new-to-this-package checked proof, not a claimed new-to-literature resolution. The MathDB snapshot's `open` status is not evidence that no later paper exists. There is no exhaustive priority claim for the Lean formalization.

Read the pinned OpenAI-math `sources/upstream.json` (commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb) and catalogue. Searches for shelf/shuffle/Clay/Tripathi in the catalogue and preprint path listing exposed Thorp-shuffle results, not a relevant dependency for this proof. No upstream theorem or repository manuscript is assumed.

## Scope

Only the explicit kernel and quadratic eigenpair are addressed. The probabilistic derivation of the kernel is reviewed textually and checked by finite exhaustive enumeration, but not formalized for arbitrary n. This is not a gap in the target algebraic theorem, since the kernel is explicitly specified in the task. Full spectral classification and the neighboring target are outside this package.
