# Independent review: MathDB 347481 geometric Vandermonde inverse

Date: 2026-10-26. Reviewer: polynomial lane. Candidate authored by the matrix lane. No candidate files, shared indexes, or git state were edited during review.

## Verdict

**ACCEPT mathematical correctness and exact-source coverage. REJECT acceptance as a genuinely new mathematical discovery under the user's strict objective. REVISE the attribution of the specific positive-definiteness observation.**

The single Lean module proves the full source conjecture, with the advertised stronger all-positive-orders conclusion, without a missing mathematical bridge. A fresh independent pinned compilation and audit passed. However, the exact matrix family's positive definiteness was explicitly published in 2006. The all-orders diagonal maximum is an immediate classical consequence; combining it with the source's own proved localization gives the full cutoff conclusion. This is a valid resolution by connecting known results, and a useful formalization, but the packet does not establish substantive new mathematics beyond that connection. Preserve it as an **uncounted source-conjecture resolution / known-results connection**. This review has no authority to update any discovery tally.

I did not locate an earlier document explicitly announcing the later conjecture's resolution. Accordingly, the rejection is not a claim that a previously posted proof was found. It is a conservative assessment of the mathematical novelty actually demonstrated. It would be misleading to identify the family's positive definiteness itself as a new discovery.

## Reviewed bytes

Paths are relative to `../matrix/vandermonde-diagonal/` unless otherwise specified. These hashes identify the packet before the requested attribution revisions; later edits require a new hash-bound addendum.

| File | SHA256 |
|---|---|
| `formal/VandermondeDiagonal.lean` | `66d10ceda83fb070d09108d34a8056de92405245d6c945cbdcd0d98208626fec` |
| `main.tex` | `fbef44eb778ae84f33374501ed3220fdc4446297bbb17237a02077b156e3a521` |
| `PROOF.md` | `04ff8a7ed1c6768e01d42475ee8ff672a2415c09edec1710a5609f1bce16dbcd` |
| `NOVELTY.md` | `18d32a437a2b2b25d7f1db1bc00fed886002d44fc8996a57d9a69bd5c375d2c5` |

All six source snapshot hashes in `source-provenance.json` were independently recomputed and matched. In particular the accepted manuscript PDF hash is `989c01ff5055a63cf2f07b8f5164fae030ca1e3bbd93b56e805dbc34f12f528f`.

## Exact source and scope

I read the actual [arXiv 2008.01012v1](https://arxiv.org/html/2008.01012v1) and the [institutional accepted manuscript](https://iris.polito.it/retrieve/handle/11583/2898892/481296), dated 11 December 2020. The latter is the accepted version of Carlo Sanna, Jeffrey Shallit, and Shun Zhang, *The largest entry in the inverse of a Vandermonde matrix*, Linear and Multilinear Algebra 70(20) (2022), 5634–5641, DOI 10.1080/03081087.2021.1922337. I also rendered and visually inspected accepted-manuscript printed p. 7 (PDF p. 8), confirming Conjecture 12 and its ceiling/index notation. The first arXiv version labels the same conjecture 11.

The source takes real b>1, positive integer n, zero-based indices below n, and the inverse of V(b^0,...,b^(n−1)), where a Vandermonde row consists of successive powers of its node. Its cutoff is the integer ceiling of log_b(1+1/b). The conjecture asks for an eventual diagonal maximum at an index at most that cutoff. The source's Theorem 1 already supplies localization. No change of transpose, base, ceiling, or endpoint convention was found.

The packet's all-orders theorem is genuinely stronger in its n-quantifier. It does not rely on treating an out-of-range entry at the cutoff as defined: if the cutoff is outside the matrix, every legal index already satisfies the bound. The Lean proof handles this case automatically. For b>1, log_b(1+1/b)>0, so its natural-number ceiling agrees with the source's ordinary integer ceiling. The n=1 case is included; n=0 is correctly excluded because a maximizing index would not exist.

An independently refreshed MathDB API snapshot is saved at `review-vandermonde/347481-live.json`. It still has status `open` and empty solutions/comments/model-attempts/human-solves/replies. This is database evidence, not proof of novelty.

## Independent mathematical audit

The short written argument is valid. Leading principal determinants of the symmetric matrix (b^(ij)) are positive Vandermonde products, so Sylvester's criterion gives positive definiteness. Inversion preserves positive definiteness. Applying Cauchy–Schwarz to coordinate vectors gives |C_jk|²≤C_jj C_kk. A largest positive diagonal entry therefore bounds every absolute entry.

The alternative kernel proof in Lean is also valid. Each term of exp(c x_i x_j), c≥0, is a nonnegative scalar times the outer product of the vectors (x_i^k). Finite sums are positive semidefinite, the cone is closed, and the exponential series converges entrywise in the finite matrix space. Vandermonde invertibility then gives strict positive definiteness. This is an ordinary scalar exponential kernel, not a mistaken use of the matrix exponential.

I checked the localization rather than accepting it as an assumed source theorem. Lagrange evaluation proves the actual inverse/coefficients identity with the correct row and column roles. Alternating signs are removed by composition with −X, leaving nonnegative coefficients of the plus-node product. Excluding the larger adjacent node decreases those coefficients. The positive denominator products satisfy the two stated shift/append recurrences, and the cutoff implies the required monotonicity. The proof uses only legitimate adjacent indices inside the matrix. Symmetry then transfers the column bound to the diagonal. No global maximum is inferred merely from a bottom-right submatrix bound without the additional diagonal-maximum argument.

The TeX theorem's strict positivity follows from the proved positive-definite inverse, although the main source-conjecture endpoint itself only needs the absolute-value statement. The displayed denominator ratio in the prose should explicitly carry the range 0≤j<n−1; its intended use is correct.

## Fresh formal replay

A byte-identical source copy was compiled in my own `review-vandermonde/` directory using `twenty-proof-campaign/verify_outcome.py`, Lean 4.34.1 (commit `5045d0056413266e57c625dcd7c365b10e377c52`) and the pinned 2026-10-14 packages. The independent result is `review-vandermonde/build/audit.json`.

- Status PASS; all 28 declarations audited.
- Main declaration: `VandermondeDiagonal.source_conjecture_all_orders`.
- Only axioms: `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, custom axiom, `native_decide`, assumed positive definiteness, assumed inverse formula, or assumed localization bridge.
- Its only mathematical input hypotheses are b>1 and n>0; b and n are universally quantified.
- `geometric_vandermonde` proves the exact source matrix bridge, and `geometric_det_ne_zero` rules out the totalized-inverse singular case.
- The existential index itself belongs to `Fin n`; its diagonal entry is included among the entries it bounds, which gives equality to the finite global maximum without assuming a separately defined maximum.

No authored PDF was built in this review.

## Decisive prior-art finding

Froilán M. Dopico and Plamen Koev, *Accurate Symmetric Rank Revealing and Eigendecompositions of Symmetric Structured Matrices*, SIAM Journal on Matrix Analysis and Applications 28(4), 1126–1156, DOI [10.1137/050633792](https://doi.org/10.1137/050633792), published electronically 18 December **2006**. The [public author-hosted PDF](https://gauss.uc3m.es/fdopico/papers/SIMAX2006.pdf) is available; no access restriction was bypassed. Equation (9), printed p. 1135, defines precisely A_ij=a^((i−1)(j−1)), the same family after shifting indices. Printed p. 1136 explicitly says: “The matrix A is positive definite if a > 1”. I visually checked that page and read the surrounding Section 4. It studies symmetric factorizations and eigenvalue algorithms, and does not explicitly state the inverse-entry maximum or the later cutoff conjecture. The file is saved as `review-vandermonde/Dopico-Koev-2006.pdf`, SHA256 `021fd296ca40be17addaca2758e53d7f2a4c846e359c44d68867a0b148e39bff`.

Thus there are three distinct claims:

1. **Specific-family positive definiteness:** explicitly known by 2006. Rediscovery or formalization earns no new-discovery credit.
2. **All-orders diagonal inverse maximum:** immediate from that known fact and the standard coordinate Cauchy–Schwarz inequality. I found no earlier explicit announcement, but no new inequality or structural fact is needed.
3. **Full source index bound:** follows by combining item 2 with Sanna–Shallit–Zhang's own localization. The later source explicitly leaves the conjecture open, so recognizing this connection resolves what those authors asked. That does not establish substantive new mathematics beyond an elementary connection of published results.

The packet's proposed contribution should consequently be described as an application of known positive definiteness to resolve the source conjecture. The current phrase identifying the positive-definiteness observation as the proposed new contribution needs correction.

## Further novelty checks and limits

Independent searches included the exact title and DOI with proof/solution/conjecture; both conjecture numbers; all three authors with diagonal/positive-definite; geometric and symmetric Vandermonde with inverse/largest/maximum. I inspected Shallit's author bibliography and the source's accepted version. These checks found no explicit earlier resolution. Total positivity and the diagonal-maximum fact are classical and cannot be represented as new ingredients.

I also independently read the relevant Section 3 and Proposition 4 of Feng Qi's 2025 Mathematics article 13(2), 223, DOI [10.3390/math13020223](https://doi.org/10.3390/math13020223), through its [public primary full-text copy](https://www.researchgate.net/publication/387814254_Series_and_Connections_Among_Central_Factorial_Numbers_Stirling_Numbers_Inverse_of_Vandermonde_Matrix_and_Normalized_Remainders_of_Maclaurin_Series_Expansions). It handles consecutive integer nodes and Stirling formulas, not this geometric diagonal-maximum problem. It cites the source generically. The publisher returned HTTP 429. That inspected citation is not a proof that all later citations have been located.

No absence-of-search-hits argument can certify worldwide novelty. There may be an unindexed explicit solution. Conversely, the known 2006 fact does not by itself prove someone published this exact connection. This review distinguishes those questions and rejects the strict discovery claim on the demonstrated mathematical scope, while accepting the full proof and its useful source correspondence.
