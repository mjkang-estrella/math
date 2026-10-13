# I241 — primary literature and source contracts

The new argument is an application of an established small-solution regularity theorem to a growing-cylinder selection. This bounded comparison does not establish worldwide novelty or an accepted tenth finding.

## Savin: the decisive input

Ovidiu Savin, [Small Perturbation Solutions for Elliptic Equations](https://www.math.columbia.edu/~savin/Small_pert.pdf), *Communications in Partial Differential Equations* 32 (2007), 557–578, DOI [10.1080/03605300500394405](https://doi.org/10.1080/03605300500394405).

Read and retained complete PDF pages 1–4 and 14–18, corresponding to printed pp. 557–560 and 570–574:

- [Pages 1–4](savin-pages-1-4.txt): H1, H2, H3/H3', H4, Theorem 1.1, Corollary 1.2, Theorem 1.3 and the beginning of its underlying contact argument.
- [Pages 14–18](savin-pages-14-18.txt): Corollary 3.3, complete Section 4/Proposition 4.1 and the start of Section 5.

H1 is ellipticity in the Hessian; H2 is uniform ellipticity only in a fixed neighborhood of small jets; H4 is C² control near the zero solution. Global uniform ellipticity in the gradient variable is not required. Theorem 1.3 supplies C^{2,alpha} regularity from small oscillation. Theorem A checks all these assumptions for an explicit polynomial family, including zero/one endpoints of its two parameters.

For parameter uniformity, the essential read is Proposition 4.1: its improvement radius depends on the jet neighborhood, the common C² bound and universal constants. Its proof explicitly treats varying operators F_k, passes their derivatives to a limit on the fixed local jet set, and identifies a constant-coefficient linear limit. The I241 use of a common smallness threshold is grounded in that proof, not in an unsupported assertion that every “depending on F” constant is uniform.

The text extraction loses some Greek glyphs. The roles of the ellipticity constants, jet radius, smoothness bound K, and varying-operator compactness are identifiable throughout these excerpts; no numerical value or optimal exponent is extracted from them. The entire PDF was retrieved solely for bounded extraction and hashing, then removed because the remaining pages were not fully read.

## Actual weak p-solutions

Vesa Julin and Petri Juutinen, [A new proof for the equivalence of weak and viscosity solutions for the p-Laplace equation, arXiv:1104.2197v1](https://arxiv.org/abs/1104.2197v1). Reused and read completely the existing [PDF pages 1–6](../i236_viscous_contact_propagation/julin-juutinen-1104.2197v1-pages-1-6.txt).

Definitions 2.1–2.3 distinguish weak and viscosity solutions; the introduction identifies the established easy weak-to-viscosity implication, and Section 3 proves the reverse implication for p>=2. I241 needs only the former. Multiplication to the continuous polynomial test equation at a zero gradient gives zero on both sides, so no critical test is silently divided out. The later singular-p argument and Appendix A are not used or claimed read.

## Fixed-p regularity does not supply uniformity in p

Aelson Sobral, Eduardo V. Teixeira and José Miguel Urbano, [Qualitative-to-quantitative regularity for degenerate equations, arXiv:2610.13137v1](https://arxiv.org/abs/2610.13137v1). Reused and read the complete [PDF pages 1–4](../i224_infinity_gradient_stability/sobral-teixeira-urbano-2610.13137v1-pages-1-4.txt).

Theorem 1.1 states constants C(n,p,gamma,beta), uniform in the solution but not in p. Its shifted limiting matrix is I+(p-2)e tensor e, with degenerating ellipticity ratio as p grows. That theorem cannot substitute for the I241 scaled small-jet check. Theorem 1.3 in that paper is planar and infinity-harmonic. No later sections were newly read for I241.

## Value convergence is different from this estimate

Leon Bungert, [The convergence rate of p-harmonic to infinity-harmonic functions, arXiv:2302.08462v2](https://arxiv.org/abs/2302.08462v2). Reused the local full-text copy and read lines 1–210, through Theorem 1 and the beginning of Remark 2.4.

Theorem 1 is a value estimate. It assumes a uniform Hölder seminorm bound for u_p, identifies the general p^{-1/4} asymptotic rate, and improves it under a positive global essential infimum of the limiting gradient. It does not give the small affine-value error O(1/p) required by the simple fixed-ball Savin corollary. I241 does not derive a general gradient rate from it.

## Pinned manuscript and completed I236

The complete pinned family prefix in sources/preprints-tree.json was checked; it contains one manuscript, not a separate same-family viscous or p-uniform result. This is a path-catalogue check, not a semantic audit of unrelated manuscripts.

Read the full [01-introduction.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/01-introduction.tex) and all of [03-reduction.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/03-reduction.tex), using existing corpus copies. Git blob hashes were matched to the complete path catalogue.

The relevant contracts are thm:liouville, eq:limit-fit, lem:bad-scales, eq:running-maximum, lem:cylinder-comparison, and prop:nonaffine-limit. The same-center vector comparison is actually reproved in I241 without its lower slope-norm assumption. The source's linear lift and qualitative-family flatness apply to infinity-harmonic functions; they are not extended to the p-equation by assertion.

Read the entire completed I236 analytic proof and verified its supplied SHA-256. Its finite-positive-tau fitted-class affinity is accepted as an available completed input. No REG_tau, uniform-in-tau conclusion, or p-gradient convergence is inferred. No I238 or I240 output was read.

## Contribution boundary

Savin's theorem is established prior art, and the elementary selection is not individually novel. The candidate new bridge is the quantitative interaction of the growing selected fit, its inscribed epsilon-ellipsoid, and a fine-cylinder Taylor estimate for actual p-solutions. It pays the enlargement cost and excludes the high-viscosity branch with nonzero selected slopes. Whether that combination meets the independent-contribution gate remains for a separate review. The full gradient-convergence theorem is not claimed.
