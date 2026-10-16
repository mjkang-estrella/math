# Source contracts

Author: Myeongjin Kang (no affiliation). Original prose CC BY 4.0.

Pinned upstream: openai/math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
(commit date 2026-10-08, from `sources/upstream.json`, snapshot in
`inputs/context/upstream.json`). Directory
`preprints/Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/`,
catalogue entry 374. Files were fetched from pinned raw URLs; their Git
blob identities equal the entries in `sources/preprints-tree.json`.

| Local copy (`inputs/pinned/brenier/`) | Git blob | Read |
| --- | --- | --- |
| README.md | 575cccc262d3d9c9e7a87df235884857a1620f79 | full |
| main.tex | 676dc958b88fa0062b3949895c4b01092a9bab64 | full |
| references.bib | ef5e68b8d708d1a263e6db20f873a76bfba5776b | entries used |
| sections/introduction.tex | a3f79cd0ba261e054ad3ebb0a5641453788f20ef | full |
| sections/sharpness.tex | ae214b7d19cd630fccf6da61b4e169fd329b28e8 | full |
| sections/cells.tex | 15cf607375c84a422c8aa4b69c9b2791651fd13c | full |
| sections/moments.tex | b1645cc9b0cf7982c28ba13b1138b86cbd664b2c | full |
| sections/finite_stability.tex | ebb83b10ad60efd546708576f5a6fd339a8eb90e | full |
| sections/gradient.tex | baebc01672a5e6e1e83838192e4fb3a56ab201b6 | full |

`article.pdf` (blob 8eb88c37…) was not fetched; the build sources were read
instead.

## How each pinned statement is used

Per `AGENTS.md`, pinned theorems are accepted as true. Theorem LC concerns
a different source measure, so the pinned *statements* about the uniform
source are not applied to `rho = f dx`. Instead their *proofs* are re-run
under hypotheses (H); every changed step is re-proved in `candidate.md`.

| Pinned label | Hypothesis on source in pinned text | Use in candidate | Status |
| --- | --- | --- | --- |
| `main:stability` (sharpness half) | uniform on `[-1,1]^d` | LC-c: the uniform cube satisfies (H) | applied as stated |
| `sharpness:exponent` | uniform cube | LC-c | applied as stated |
| `cells:optimality` | absolutely continuous source (proof uses null ties only) | Lemma 3.3 | proof re-run; unchanged |
| `cells:calculus` | uniform | Proposition 3.1 | proof re-run with weight `f`; changed steps written out |
| `cells:weights` | uniform | Proposition 3.2 | proof re-run; uses only listed properties |
| `moments:midpoint` | uniform laws on `U, V` | Lemma 4.1 | replaced; new weighted proof (log-concavity) |
| `moments:derivative` | uniform | Proposition 5.1 | proof re-run with Lemma 4.1; algebra rechecked |
| `finite:potentials` | uniform | Proposition 6.1 | proof re-run; uses only listed properties |
| `gradient:interpolation` | uniform (translation invariance) | Lemma 7.1 | replaced; new direction-switching slice proof |
| `gradient:finite` | uniform | Section 8 | new constant `C_LC` |
| `gradient:extension`, proof of `main:stability` | uniform | Section 8 | proof re-run; uses `rho`-null = Lebesgue-null on `K` |

Geometric facts reused from the pinned proofs without change: `partial K`
has zero volume; relative interiors of sections through `int K` lie in
`int K`; slice boundaries are slice-null; coordinate partials of a convex
function form its gradient a.e.; the Knothe substitution inequality
`int G(H) prod d_{s_k} H_k ds <= int G dx` for nonnegative Borel `G`.

## External literature

See `literature-screen.md` for extents. No external theorem is used in the
proof; external items bear only on novelty and context. McCann 1997
(displacement concavity) is mentioned in the pinned text as an alternative
route to the uniform midpoint bound and is not used here.
