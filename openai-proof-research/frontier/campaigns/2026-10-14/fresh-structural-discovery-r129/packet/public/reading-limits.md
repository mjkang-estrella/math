# Reading limits and access record

## Pinned upstream (commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb)

All 27 non-PDF files of the two family-089 preprints were fetched from pinned raw URLs. Each was matched to its full record in the complete 13223-entry `sources/preprints-tree.json` by size and Git blob SHA1. The records are in `private/canonical.json`.

- Read in full: treewidth `01-introduction.tex` and `07-conclusion.tex`; planar `sections/introduction.tex` and `sections/consequences.tex`.
- The other 23 files were acquired and keyword-searched only (sums, minors, clique, K_{3,3}). Their proofs were not read and are not relied on beyond the main theorem statements above.
- Source175 and its companions were not re-read in r129. Their use is as paid and recorded by r128.

## External primaries

- Indyk–Matoušek–Sidiropoulos, Handbook of Discrete and Computational Geometry, 3rd ed., chapter 8 (csun.edu PDF, HTTP 200). Only the GNRS/k-sum passage and the bibliography entries were read.
- Chekuri–Gupta–Newman–Rabinovich–Sinclair, SIAM J. Discrete Math. 20 (2006) (author PDF, HTTP 200). Keyword search only. No 2-sum closure statement was found, and the paper is not used.
- Lee–Poore, "On the 2-sum embedding conjecture", SoCG 2013. Only the abstract on its ResearchGate listing was read. The ACM PDF returned HTTP 403, and a guessed author-page URL returned 404. The author's publication page links only to the ACM entry. The constrained-embedding characterization was therefore not read.
- Chakrabarti–Jaffe–Lee–Vincent, FOCS 2008. Only the abstract shown on the same ResearchGate listing was read.
- The ResearchGate pages were read through a web fetch and were not retained. Failed requests are recorded in `private/primary/receipts.json`.
- Borcea–Brändén–Liggett, Przybyłowski–Riordan and Park–Vondrák were not re-read. They are cited only through r128's paid operations.

## Project history

Copied and read in full: the r128 outside report, its five public notes and the parent intake; analytic r17 `status.json`, `graph-interface-checkpoint.md`, `interface-obstructions.md` and `operation-comparison.md`; structural r46 `history.md`; and structural r120 `packet/public/screens.md`. Analytic r114 was opened to confirm that it gives 089 navigation only. It was not copied. The accepted findings R027 and R029 and the campaign index were read at the heading and summary level and are bound as inputs.

The two recorded searches (`private/search/`) list paths only. Their hits were opened selectively. For the 2-sum terms, the only operative history hit was r17's `graph-interface-checkpoint.md`. The other eight hits were r17's retained Lee–Sidiropoulos text and copies of the two upstream preprints. For the weighted-rank terms, the operative hits were r128 itself. The remaining hits use "mean field" or "weighted rank" in unrelated senses. A search hit is not a semantic read, and a missing hit is not evidence of absence.

## Computation

`public/cb_checks.py` and its output `public/cb-checks-output.txt` are finite sanity checks. They use exact rationals for containment values and floating point for the mean-field vector. They are not proofs or gates. The only exact claims they confirm are the three rational values of the sandwich example.
