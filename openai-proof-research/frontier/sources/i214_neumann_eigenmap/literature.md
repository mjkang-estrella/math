# I214 primary literature and comparison

## Bounded conclusion

The proposed result is new relative to the completely read family-369 manuscript and is not a statement of the three primary texts read below. This does **not** establish worldwide novelty. Search misses are not used as evidence of priority. No active project reviews were read.

## Primary texts read

### Jones–Maggioni–Schul, 2008

**Peter W. Jones, Mauro Maggioni, Raanan Schul, “Manifold parametrizations by eigenfunctions of the Laplacian and heat kernels,” PNAS 105(6), 1803–1808 (2008).**

- DOI: [10.1073/pnas.0710175104](https://doi.org/10.1073/pnas.0710175104).
- Retained primary-article PDF: [NOAA-hosted copy](https://www.aoml.noaa.gov/ftp/phod/pub/thacker/SSAmanifoldPapers/JonesMaggioniSchul2007.pdf), `primary/jones-maggioni-schul-2008.pdf`.
- Publisher article archived at [PMC2538843](https://pmc.ncbi.nlm.nih.gov/articles/PMC2538843/).
- Read all six printed pages, 1803–1808, through the entire 561-line extracted text, including theorems, proof outline, examples, captions, and references. Figure geometry was not independently rendered or inspected. The retained article is an announcement/outline; its cited longer proof was not read.

**Comparison (Theorems 1–2, p.1804):** after fixing a point and an interior scale, suitable d eigenfunctions give a bi-Lipschitz map on a smaller ball. Their frequencies scale with the inverse square of that radius. I214 instead fixes the entire first-positive eigenspace in the double planar case and proves injectivity on the whole domain, a star-shaped image, and smooth boundary angular coordinates. I214 gives no uniform distortion estimate; the Neumann boundary degeneracy prevents a global lower Lipschitz bound on closures. The PNAS introduction's discussion of an infinite-dimensional heat-kernel embedding is not a result about two lowest modes. Its cited Bérard–Besson–Gallot paper was not independently read.

### Burdzy, 2002

**Krzysztof Burdzy, “On nodal lines of Neumann eigenfunctions,” arXiv:math/0203017v1 (2 March 2002).**

- Primary record: [arXiv:math/0203017](https://arxiv.org/abs/math/0203017).
- Retrieval URL: `https://arxiv.org/pdf/math/0203017`; the returned PDF identifies itself as v1. Retained as `primary/burdzy-nodal-2002.pdf`.
- Read all ten PDF pages through all 371 extracted text lines, including the theorem/proof, two examples, captions/labels and references. Figure geometry was not independently rendered.

**Comparison (Theorem 1, pp.3–4, examples pp.5–8):** mirror couplings constrain which regions can contain a nodal domain and localize nodal lines in particular planar geometries. The text explicitly recalls two connected nodal domains, including multiplicity. It does not prove global univalence of a pair of first modes, a common nodal center, or an everywhere regular boundary angle. It shows why information about the nodal line is relevant to the hot-spots problem. I214 uses nodal connectedness as input rather than counting that familiar fact as its new result.

### Burdzy, 2026

**Krzysztof Burdzy, “Removing Boundary Smoothness from the Hot-Spots Conclusion in the Simple-Eigenvalue Case,” arXiv:2610.12622v1 (8 October 2026; PDF dated 7 October).**

- Primary record: [arXiv:2610.12622](https://arxiv.org/abs/2610.12622).
- Retained [versioned PDF](https://arxiv.org/pdf/2610.12622v1): `primary/burdzy-2610.12622v1.pdf`.
- Read all seven PDF pages through all 363 extracted text lines: human commentary, Theorem 2.1, Corollary 2.2, Lemmas 3.1 and 4.1, Proposition 5.1 and proofs, remarks, and references.

**Comparison:** Theorem 2.1 transfers a boundary-layer supremum/infimum conclusion to bounded simply connected domains with compact Neumann resolvent and a simple first positive eigenvalue. It explicitly does not establish universal nonvanishing of the interior gradient in the rough setting. Proposition 5.1 permits eigenvalue multiplicity, but a prescribed limiting eigenfunction is selected using simplicity. I214 addresses the double-eigenvalue smooth case and global two-coordinate univalence. The note uses the same smooth-domain theorem as an external input, but is not a proof dependency for I214. Its own human commentary describes the smoothness-removal result as an elementary corollary and does not claim a checked proof audit. I214 makes no claim about rough boundaries.

## Pinned manuscript comparison

All text sources in this family's build were read: sections 01–06, main.tex, references.bib, boundary-signs.tex, and README. Section 01 states the no-critical-point theorem for every member of V. Section 02 already proves the sign-domain connectivity and multiplicity bound. Sections 03–06 establish the vector/kernel route to that theorem. None states or proves global injectivity of F=(u,v), a common nodal center, a star-shaped eigenmap image, or a smooth boundary angular diffeomorphism. The supplied family path listing has one manuscript, so there is no second companion manuscript within that family. Other current lanes were deliberately not examined.

## Search coverage and limits

Ordinary web searches were made for combinations of:

- first Neumann eigenspace/eigenmap with injectivity, univalence, star-shaped domain, and diffeomorphism;
- Neumann second nodal line, smooth boundary, vanishing order, and connectedness;
- hot spots with coordinates and eigenfunction embedding;
- Jones–Maggioni–Schul local eigenfunction parametrization;
- the specifically supplied arXiv identifier 2610.12622.

Search results also pointed to Jiuyi Zhu's Robin/Neumann nodal-set paper, Alessandrini's boundary/nodal papers, the full 2010 Jones–Maggioni–Schul paper, harmonic-map valence literature, and graph “Neumann eigenmaps.” These were discovery leads only, not read proof dependencies and not retained as supposedly read full papers. In particular, an unrelated use of “Neumann” as an author's surname, or the Neumann–Poincaré integral operator, is not a comparison with the Laplacian problem here.

No general boundary unique-continuation theorem is taken on trust from those search snippets. I214 supplies the needed even-reflection/Fourier proof. The actual reviewed comparison set is small; no comprehensive novelty or citation review, citation-tree traversal, later-version comparison, or priority conclusion was attempted.

## Authentication

SHA-256 digests of every retained primary PDF and complete extracted text, together with exact reading bounds, are in `../../experiments/i214_neumann_eigenmap/input-authentication.json`. Text extraction is ordinary `pdftotext -layout`; no OCR, page rendering, numerical experiment, automated theorem test, or source-truth audit was performed.
