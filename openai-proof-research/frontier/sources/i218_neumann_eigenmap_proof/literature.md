# I218 — Primary-source comparison and exact reading limits

This file records the independent proof review's bounded literature comparison. It is not a priority, significance, contribution, or count decision. No new primary copies were created; all retained sources were read in place under `frontier/sources/i214_neumann_eigenmap/`.

## Pinned manuscript

Repository `https://github.com/openai/math`, revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, family `preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/`.

Read every line of retained `pinned/01-introduction.tex` (1–65), `02-preliminaries.tex` (1–100), `03-vector-form.tex` (1–80), `04-boundary-kernels.tex` (1–179), `05-reciprocal-kernels.tex` (1–265), `06-conclusion.tex` (1–59), `main.tex` (1–70), and `README.md` (1–18). These copies were already retained from pinned raw GitHub URLs; their hashes and original URLs are in the I218 authentication file. All pinned theorems/lower operations are stipulated; they are not audited.

Actual proof inputs: `thm:main`, the final regularity paragraph of section 01, and `lem:nodal`/`lem:conformal` in section 02. The source quantifies over every nonzero member of V and explicitly addresses multiplicity. Section 02's existing multiplicity bound is not a new result. Sections 03–06 contain the vector/kernel proof of the source theorem and do not state the global eigenmap conclusion. The exact family path listing shows no second companion manuscript within this family. No inference about other families is made. The listed bibliography and figure source were not read, nor was the compiled source PDF.

## Jones–Maggioni–Schul (2008)

Peter W. Jones, Mauro Maggioni and Raanan Schul, *Manifold parametrizations by eigenfunctions of the Laplacian and heat kernels*, PNAS 105(6), 1803–1808. [DOI](https://doi.org/10.1073/pnas.0710175104). Retained original retrieval: [NOAA-hosted PDF](https://www.aoml.noaa.gov/ftp/phod/pub/thacker/SSAmanifoldPapers/JonesMaggioniSchul2007.pdf).

Read `primary/jones-maggioni-schul-2008.txt`, lines 1–561 inclusive, covering all six printed pages, statements, outline, examples, figure captions and references. The PDF was hashed, not independently rendered. Font substitutions in the existing extraction are visible. Theorems 1–2 on printed page 1804 are sufficiently readable for the following limited comparison.

They select d eigenfunctions depending on a chosen point and interior scale to give local bi-Lipschitz coordinates; the selected eigenvalues scale with the inverse square of that scale. This is different from a global injective map formed by every basis of a fixed double first-positive eigenspace. Their local statement and the introduction's discussion of an infinite-dimensional heat embedding do not assert the I214 star-shaped image, closure map or common nodal center. This is a comparison of statements, not an audit of their proof. The full 2010 proof/earlier arXiv version cited in the outline was not read.

## Burdzy (2002)

Krzysztof Burdzy, *On nodal lines of Neumann eigenfunctions*, arXiv:math/0203017v1. [Primary record](https://arxiv.org/abs/math/0203017); retained original retrieval [PDF](https://arxiv.org/pdf/math/0203017).

Read `primary/burdzy-nodal-2002.txt`, lines 1–371 inclusive, all ten PDF pages, including Theorem 1, proof, examples, captions and references. The PDF was hashed but figure geometry was not independently inspected.

The text on page 3 states the two-nodal-domain fact for any second Neumann eigenfunction while allowing multiplicity. Theorem 1 uses mirror coupling to exclude certain locations for a nodal domain; the examples locate nodal lines within geometric regions. It does not assert global univalence of a pair of eigenfunctions or a common center. The review's connected-sign-set dependency comes from the stipulated manuscript itself, not an unverified extension of this paper.

## Burdzy (2026)

Krzysztof Burdzy, *Removing Boundary Smoothness from the Hot-Spots Conclusion in the Simple-Eigenvalue Case*, arXiv:2610.12622v1, dated 7 October with arXiv stamp 8 October 2026. [Primary record](https://arxiv.org/abs/2610.12622); retained original retrieval [versioned PDF](https://arxiv.org/pdf/2610.12622v1).

Read `primary/burdzy-2610.12622v1.txt`, lines 1–363 inclusive, all seven PDF pages: human commentary, statements, proofs, remarks and references. The PDF was hashed but not independently rendered.

Theorem 2.1 proves boundary-layer extremal-value conclusions for bounded simply connected domains with compact Neumann resolvent and a simple first positive eigenvalue, conditional on the smooth-domain input. Proposition 5.1 allows multiplicity for subsequential spectral convergence; prescribing a particular limiting eigenfunction uses simplicity. This is not a theorem about global spectral coordinates in the double-eigenvalue case. No rough-boundary extension of I214 follows merely from this note. Its human commentary explicitly limits the author's proof checking; the present review does not use it as a proof dependency.

## Limits

This review independently read the three retained primary texts, but did not repeat the original discovery searches, conduct a citation-tree search, read the full Jones–Maggioni–Schul proof paper, or read other boundary unique-continuation/harmonic-map literature. No worldwide novelty follows from this bounded comparison. The finite-order boundary argument was checked directly through its Fourier multiplier and cutoffs; it does not rest on an unread theorem cited by a search snippet.

See `../../experiments/i218_neumann_eigenmap_proof/input-authentication.json` for file hashes and exact reading metadata. See `../../reviews/i218-neumann-eigenmap-proof.md` for the mathematical verdict and detailed proof checks.
