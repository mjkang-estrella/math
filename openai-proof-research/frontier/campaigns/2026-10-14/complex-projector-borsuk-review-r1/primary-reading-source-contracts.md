# Primary reading and source contract log

Myeongjin Kang; no affiliation. 2026-10-16. Original prose CC BY 4.0.
All third-party files are private inputs and retain their own rights.

## Immutable identity and mathematical contracts

Upstream truth is stipulated at openai/math
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. It was not audited.
AGENTS.md and sources/upstream.json were read. The family-156 entry
of sources/CONTENTS.md (lines 3715–3729) was read; no semantic reading
of all 719 manuscripts is claimed. The COMPLETE preprints-tree.json was
parsed, truncated=false, 13223 entries; the truncated root tree was not used.
All fourteen retained candidate Git blobs were independently recomputed
as SHA1("blob "+decimal length+NUL+bytes) and matched against that complete
catalogue, with paths, sizes, SHA256 and full blob IDs recorded in
inputs/pinned-catalogue-check.json. Authentication is separate from reading.

The source directory is
preprints/A-nine-dimensional-counterexample-to-Borsuks-covering-assertion-September-23-2026/.
The authenticated original copies remain at
../fresh-structural-discovery-r16/inputs/pinned/borsuk/; they were not
duplicated. The full nonfigure source was read: README, main, preamble,
bibliography, introduction, geometry, extension, topology, six-labels,
ten-labels, conclusion. The three figure TeX files were authenticated,
not read. The source PDF was not read or retained here. Key contracts:

* thm:main concerns REAL 4-by-4 projectors, dimension nine, no ten-set
  strict cover. It does not state B8C or its negation.
* lem:cover-to-map handles arbitrary strict-gap sets via open enlargement;
  its smooth partition is more than needed for the continuous transfer.
* lem:positive-extension includes the singular PSD boundary and support
  identity. lem:signed-extension uses orthogonal spectral supports.
* thm:label-bound supplies the antecedent odd-map count. Its equality
  degree/surjectivity statements are not needed by the Hermitian proof.
* thm:equality-complex and the six/ten-label endgame concern real projective
  space. They are read for operation comparison, not invoked or audited.

The new proof independently checks the projector metric, Bessel,
Hermitian extension, all Hesse algebra, and strict perturbed cover.
Standard mathematical inputs are Borsuk–Ulam, continuity of PSD square
root, elementary compactness/integration and Cauchy–Schwarz/Bessel.
No external primary classification theorem is needed to prove B8C.

## Actual external primary reading

Retained HTML bytes and their readable text extractions are in
inputs/primary/. Exact local hashes/sizes and retrieval URLs appear in
inputs/primary-records.json and manifest.json. Text-extraction line ranges
below refer to those retained .txt files, not browser line numbers.
No primary research code or elimination calculation was executed.

1. Lane Hughston and Simon Salamon, *Surveying points in the complex
   projective plane*, [arXiv:1410.5862v2](https://arxiv.org/html/1410.5862v2).
   Entire article body, Sections 1–10, introduction, acknowledgements,
   and references read (extraction lines 1–1595 including web boilerplate).
   In particular full Theorems 5.3/5.5, Proposition 6.2, Lemmas 7.1/7.2,
   8.1/8.2, symmetric-polynomial construction and final quotient-ideal
   classification argument. The computational primary proof is read as
   an antecedent, not independently re-certified. Its equidistance and
   distance-normalization contracts are distinguished from covering.

2. Hoan Bui Dang, Kate Blanchfield, Ingemar Bengtsson, D. M. Appleby,
   *Linear Dependencies in Weyl-Heisenberg Orbits*,
   [arXiv:1211.0215v2](https://arxiv.org/html/1211.0215v2).
   Full Sections 1–3, extraction lines 1–268, read. This includes phase
   conventions, the displayed SIC family, determinant dependence condition,
   Hesse pencil, twelve normals/MUB discussion and changes within the
   SIC family. Sections 4–9 were retained, not read; no universal statement
   about their non-SIC covering content is attributed to them.

3. Wei Dai, Youjian Liu, Brian Rider, *Quantization Bounds on Grassmann
   Manifolds and Applications to MIMO Communications*,
   [arXiv:cs/0603039v2](https://arxiv.org/html/cs/0603039v2).
   Full introduction, Sections II–IV and their displayed statements and
   proof discussions read (extraction lines 1–488, with III reread
   separately); Appendix B and C in full, lines 763–975, read. The initial
   retrieval used the unversioned HTML endpoint, whose retained body declares
   v2, 16 May 2006. Sections V/VI, the full Appendix A volume proof, and
   references were retained but not read, apart from an incidental tail
   of Appendix A. Do not claim those sections were screened. Exact chordal
   volume versus expected distortion versus worst-case radius matters.

4. Henry Adams, Johnathan Bush, Florian Frick, *The topology of projective
   codes and the distribution of zeros of odd maps*,
   [arXiv:2106.14677v3](https://arxiv.org/html/2106.14677v3).
   Sections 1–3 in full, extraction lines 1–252, and Section 7 and conclusion,
   lines 447–510, read, including full proofs of Theorems 2–4 and 15.
   Lines 265–385 (part of Sections 4–6) and 595–705 (references) were also
   read incidentally. The rest was retained but not read. This is real
   projective/spherical equivariant topology; its cover hypothesis does
   not assert a complex nine-center construction.

Kalai's retained survey was authenticated as part of the author package.
It was not reread here; the source's actual projector methods, rather
than an inherited claim of survey reading, supply the operation comparison.
The CP^2 classification article mentioned only as a search result by the
author was read fully in this review.

## Bounded discovery search and failed access

Thirty focused query strings were issued over nine web-search calls on
2026-10-16. inputs/search-log.json records them. They concern complex
projective nine-ball coverings, covering radius, Hesse/MUB and WH
deformations, complex Grassmann quantization, and projector Borsuk/topology.
Many hits concern finite-field subspace codes, topological branched
coverings or packing, and were discarded as mismatched problems.
Search-result titles, snippets and abstracts are not full-body comparison.

The Mondal–Heath diversity paper, DOI 10.1155/2008/594928, was seen as
a potentially relevant covering-codebook comparison. Its article endpoint
returned “Fetch denied by robots.txt”; its PDF endpoint returned
“(400) Timeout fetching”. No body of that paper was read or retained.
The MDPI endpoint for *SIC-POVMs and Compatibility among Quantum States*
also returned an internal fetch error and was not read. No claims based
on these unread bodies enter the verdicts. No exhaustive covering database,
all citation chains, or all non-SIC WH codebooks were screened.

These limits leave contribution UNRESOLVED. They do not weaken the
independent full-target mathematical PASS and do not justify substantiality.

## History, code and context

The complete original parent discovery brief was hash-checked and read
at its exact supplied original path, all 1750 lines. Its FT2 and LR
appendices were read as historical continuity only; no LR package or
historical program is a mathematical dependency here. No need to inherit
an upstream LR truth claim or to execute its verifier arose.

The full frozen candidate, source contracts, comparison, scope, status,
provenance receipt and verifier were read after independent authentication.
The author's diagnose_b8c.py was read in full before any possible use;
it was not run. No floating-point optimization, random sampling, SAT scan
or other mathematical diagnostic ran in this review. All universal checks
in review.md are symbolic arguments.

Mutable parent/task context is snapshotted under inputs/context/.
The 116882-byte original historical brief, 4.86MB complete catalogue,
and frozen 35-file author package use exact external immutable references
instead of extra copies. The read-only review verifier authenticates them
but never binds future LIVE task or ledger updates. Campaign count remains
4/10, with no shared edits. Unchanged-input receipts distinguish actual
observations from any mathematical conclusion.
