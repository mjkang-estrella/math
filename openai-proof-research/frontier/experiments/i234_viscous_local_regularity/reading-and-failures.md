# I234 — reading scope and failures

## Read scope

Read AGENTS.md and sources/upstream.json in full. Read the family-377 entry in sources/CONTENTS.md; queried the complete preprints-tree.json only for the matching manuscript paths. Reused the existing corpus under frontier/sources/i14_spectral_width_novelty_r3/corpus. Read 01-introduction.tex in full; read 03-reduction.tex lines 1–150 (its thm:liouville contract is wholly within the opening passage). No theorem from the remaining reduction or sections 04–08 is used. Catalogue paths show one manuscript in that named family; this is not a search of all unrelated manuscripts for overlap.

The independently retrieved primary excerpts in this task's source directory were read completely:

* Sánchez Morgado, arXiv:1712.10275v1, PDF pages 1–5: introduction, equation (4), Assumption 1, Lemma 1 and proof, Theorem 1 and proof; page 5's start of Section 3 was also read. Rest of the paper not read.
* Porretta, arXiv:2203.04856v2, PDF pages 1–14: introduction, assumptions, Section 3, all the displayed gradient argument and Theorem 3.8. Pages 25–29: end of a convergence argument, Theorem 6.3 and 6.4, their adjacent calculations, Theorem 6.5 and its whole proof, Remark 6.6, and Definition 6.7. Pages 31–34: compact-case paragraph, appendix setup, Proposition 7.1, Proposition 7.2 and its whole proof, Remark 7.3 and footnote. Pages 15–24, 30 and 35 onward not read. No unread classical reference cited by the appendix is imported as an independently checked theorem.
* Muñoz, arXiv:2006.07367v2, PDF pages 1–4: whole introduction and initial elliptic formulation. The later full assumptions and proofs were not read; no theorem is asserted to apply based on this introductory read.

ArXiv HTML was useful for navigation but displayed a generated August 2026 date for Porretta, while the authenticated v2 PDF title page says November 18, 2022 and the arXiv version line November 17, 2022. Formula/hypothesis evidence and retained page ranges use the PDF. No inference about a new version follows from the HTML date.

## Retrieval/search limitations

Initial rg query included the bare number 377 and therefore matched irrelevant SHA substrings; its output was truncated. It was not treated as a complete catalogue read. Later source-local selection used the exact manuscript title. A filename-only search revealed I231 source excerpts. None was opened; the literature was retrieved independently from arXiv. The sole initial `find` searched for a named source file, not history or live notes. It located the old i14 corpus, whose actual manuscript text was then read.

Web searches for the precise PDE/local gradient phrases and Porretta's cited gradient work led to the two supplied papers, Muñoz, and the later manifold transport paper. Search snippets were used as leads only. The manifold paper and irrelevant hits were not read or relied upon. A search miss is not a claim that the desired theorem is absent from the literature. No live I230/I231 output, I233 file, or independent gate was read; the parent reduction was taken solely from the user's supplied text.

The PDF skill was read and used for read-only extraction. PDFs were fetched in memory and page-limited text excerpts extracted with pdftotext; no full unread PDFs were retained. No rendering was needed for a layout claim, and no PDF was authored. This task's mathematical derivations, not numerical computation, supplied all checks.

## Failures and limits

The two principal routes are analyzed explicitly in analytic-attempt.md. The smooth Bernstein identity is valid, but a spatial cutoff has an uncontrolled derivative drift and terms of the same gradient order as the prospective coercive term. The time-only barrier avoids those errors and produces only a weighted estimate. A density lower bound is absent. The two-point periodic calculation also cannot be localized by simply asserting ellipticity; its negative-direction contribution has an inverse-matrix factor.

The all-scale fits provide logarithmic value moduli and bounded dyadic slope increments; they do not supply summability or a common derivative modulus. The one-dimensional hodograph linearization assumes a controlled inverse map which is not supplied. Travelling waves and separated elementary profiles were checked analytically and do not provide a counterexample. No family parameter scan, numerical experiment or research program was executed.

No proof, contribution or acceptance gate was run. The verdict is that this investigation leaves the local bridge unpaid, not that a counterexample exists or that the bridge is impossible. No worldwide priority assertion is made.
