# I224 — reading scope and failure record

## Constraints and early work

Work stayed under `/home/mj-kang/Documents/Dev/math/openai-proof-research`; writes were limited to the assigned I224 files and the assigned source directory. AGENTS.md and sources/upstream.json were read first. Pinned theorems and lower operations were accepted. No agents were spawned; no live other-agent research outputs or acceptance ledgers were read. No research code, numerical work, parameter scan, test, snapshot, seal, stage, commit, or publication was performed. Short Python invocations only retrieved/extracted source text, inspected source-local metadata, or computed provenance hashes.

The early analytic draft wrote the quadratic-cone inequality and the as-yet-unpaid `r/lambda` residual. The first target was actual interior gradient stability, with L² p-approximation considered as the alternate route. After reading the source reduction, the normalized forced-class power bound became the selected bridge.

## Exact contextual reads

* I130: Screen I, lines 119–121 (a wider display included the adjacent end of Screen H; no historical chain was followed).
* I140: nonlinear-elliptic source/overlap and Target I paragraphs, lines 61–69.
* I143: infinity-harmonic/affine subsection, lines 17–29.
* I213: screening paragraph for family 377, line 13. An initial bounded display also exposed the nearby report introduction; none of its other-family mathematics was used.

An overbroad initial `rg --files` returned many historical paths, and one accidental `cat` of I140's read manifest produced truncated provenance records. Neither was used for a historical replay; subsequent reads were restricted to actual family-377 source files and the specified screens. A regex lookup failed once and was replaced by a simpler source-local lookup.

## Pinned manuscript read in place

Reused the existing copy under `frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/`:

* README.md, build/manuscript/main.tex and build/references/bibliography.tex: complete.
* sections/01-introduction.tex: complete, including exact theorem and scope exclusions.
* sections/02-flatness.tex: complete, including lift, cone slopes, fixed-center blow-ups, theorem of sums and three-point penalty.
* sections/03-reduction.tex: complete, including all-center/radius good fits, running maxima, geometry of the anisotropic stretch, exact limit equation and gradient extraction.
* sections/08-rigidity.tex: complete, for the actual Liouville interface and final assembly. Its accepted dependencies in sections 04–07 were not reread or audited.

The matching path entries of sources/preprints-tree.json were inspected for the manuscript/companion check. There is one same-family manuscript. This is a path-catalogue check, not a semantic audit of every unrelated paper. Existing source bytes are authenticated against catalogue Git-blob hashes.

## Primary prior-art reading

* Bungert, arXiv:2302.08462v2: reused `frontier/sources/i140_nonlinear_elliptic_discovery/external/bungert.txt`, introduction/definitions pp. 1–3 and theorem, remarks and radial example pp. 4–6 (displayed text lines 1–160 and 180–310). The rest of the convergence proof was not reread for I224. It is not a gradient-regularity input.
* Crasta–Fragalà, arXiv:1506.05305v1: newly retained PDF-extracted pages 1–3, all read. Also read the complete web-rendered Section 4, lines 340–399, for the semiconcavity condition and Theorem 16. Not claiming a full-paper read.
* Sobral–Teixeira–Urbano, arXiv:2610.13137v1: newly retained PDF-extracted pages 1–4, all read in a separate untruncated display. These contain the main statements, scope, and opening shifted-operator definition. Later proofs were not read or used.
* Lu–Wang, published 2008 author-hosted PDF: retained and fully read PDF pages 8, 9, 11, 12, 13, 24, 25, 29, 30. These contain the main value-stability statement, quadratic comparison and its local proof, and bounded excerpts of the stability proof. The central compactness proof on omitted pages is not claimed read. PDF font encoding is imperfect; exact convention was cross-checked against Crasta–Fragalà's readable Definition 1. The theorem conclusions used for comparison remain legible.

Only actually read page-limited excerpts were retained; complete downloaded PDFs were processed in memory and not kept. No duplicate pinned source copy was made.

## Failed approaches and retrievals

1. The p-energy cutoff identity leaves the explicit factor p times affine value error. Optimizing the local radius against the known value rate does not close. A lower bound on |Dv| is not a lower bound on |Du_p|.
2. Naive isotropic homogeneous replacement does not give an excess estimate after subtraction of an affine function. The limiting large-slope operator is rank one, not uniformly elliptic. Smooth oscillations document the obstruction.
3. Initially `r_i->0` alone did not pay the anisotropic forcing. Strengthening the source running maximum to `b(s_i)/s_i^{gamma_i}>=i`, with gamma_i<=1/2, gives `r_i/lambda_i->0`; this closes the selected route.
4. A trial HTML extraction failed because BeautifulSoup was absent. No package was installed. Retrieval switched to in-memory PDFs plus `pdftotext` page extraction.
5. AMS's Lindgren PDF returned HTTP 403. No copy was retained, and Lindgren's theorem is not a primary-source input to the proof or a claimed direct read. Secondary mentions were search leads only.
6. No independent theorem of p-to-infinity gradient convergence, endpoint regularity, boundary-gradient stability, or all-critical-comparison stability was obtained.

## Final assessment

The mathematical claim is proved relative to the exact pinned lower interfaces, with the forcing terms and limiting quantifiers displayed. It is stronger than interpolation from an assumed common C¹ bound. It nevertheless reuses the source method substantially; contribution significance must be independently judged under the project's prohibition on routine transfers. Search coverage is bounded and cannot certify global novelty. Parent retains both gates and the accepted-finding count.
