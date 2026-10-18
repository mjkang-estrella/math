# Reading and search limits: T259S proof review r1

Review prose CC BY 4.0.

## Read in full

* `AGENTS.md`, `sources/upstream.json`, and the acceptance section of `frontier/NEW-TEN-2026-10-14.md` (lines 1–24; the ledger beyond was only grepped for acceptance/gate terms).
* Frozen author packet: `candidate-259.md`, `scope-259.md`, `source-and-credit.md` (the terminal printout truncated three long paragraphs in the middle; the visible parts and the credit table were read, and none of it is a premise of the proof verdict), `reading-limits.md`, `formal-interfaces.md`, `reproduce.md`, `verify.py`, `controls.py`, `diagnostics.py` (two short helper sections elided in the terminal printout; the script was only run on a copy, and its output is not proof evidence). The `manifest.json` keys and counts were inspected; `source259-receipts.json` was read only in its first entry, because the reviewer's independent source check does not use author receipts.
* Source259 (`preprints/A-group-without-fixed-price-October-5-2026/`, authenticated copy): `build/introduction.tex` (full, including `intro:main`), `build/conclusion.tex` (full), `build/group-actions.tex` (full: `actions:normal-form` statement and proof, the free-basis proof for J, conull-restriction cost invariance, the Bernoulli space and freeness, `actions:height`, `actions:small-marker` and `actions:low`), `build/compression.tex` lines 255–297 (`compression:cost-one` and its proof via `compression:main`, whose proof body was not read), `INPUTS.md`, `README.md`.

## Not read

* Source259 `deployment.tex`, `finite-models.tex`, `planar.tex`, `rank-surgery.tex`, `surgery-figure.tex`, `paper.tex`, `references.bib`, the remainder of `compression.tex`, and the source PDF. The Bernoulli lower bound and `compression:cost-one` are stipulated source theorems; their proofs were not audited, as instructed.
* The three family262 manuscripts (identity-checked only). They are not T259S premises.
* Private primary comparators (Gaboriau, Abért–Weiss, Hutchcroft–Pete, FGL), `checkpoint.md`, `screen262-checkpoint.md`, `finite-bubble-obstruction.md`, `history-query.txt`, `provenance/*`. These bear on contribution and history, not on proof correctness.
* Anything under `t259s-parent/` and the parallel review packet. These were deliberately not opened, to keep the review independent.

## Standard facts used without a separate primary read

These facts were each re-proved in the review or are textbook-level: the universal property of amalgams and the embedding of factors; Nielsen basis changes; orthonormal tensor bases of L² of a countable product of standard probability spaces; mixing of Bernoulli shifts of infinite groups; equivalence of weak mixing with ergodicity of the diagonal self-product; invariance of cost under conull invariant restriction (also stated in source259 `intro`). No unread literature statement is a premise.

## Search limits

No literature search was performed. This is a proof review, not a contribution review.
