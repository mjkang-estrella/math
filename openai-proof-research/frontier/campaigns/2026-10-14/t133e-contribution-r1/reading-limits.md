# T133E contribution review r1: exact reading and limits

Retrieval and hashing are not reading. Only the ranges below were read semantically. "Navigation" means keyword search used only to locate passages.

## Author packet (`fresh-structural-discovery-r75/`, unchanged)

Read completely: `candidate.md`, `comparison.md`, `reading-limits.md`, `scope-freeze.md`, `checkpoint.md`, `progress.md`, `expander-exploration.md`, `verify.py`, `diagnostics-results.json`. Not read: `diagnostics.py` and `source133-receipts.json` beyond the fields that `verify.py` checks. Parent files read: `t133e-parent/intake.json`, `dispatch-r1.json`, `contribution-r1-brief.txt`. `proof-r1-brief.txt` and any proof-review directory were deliberately not opened.

## Pinned source family (canonical blobs in the author packet's `private/preprints/`, byte-verified against the tree)

Variable-dimension manuscript (`build/sections/`):
- `01-introduction.tex`: 1–229, complete.
- `02-refinement-game.tex`: 36–100 (`lem:dimension-cap`, `prop:membership` statement and first part of its proof). The game lemma `lem:wl-game` was not read.
- `04-blocks-projection.tex`: 137–200 (`lem:block-fibers` with proof, `prop:exact-projection` statement). The exact-projection proof was not read.
- `05-general-realization.tex`: 1–115, complete.
- `06-subcubic-realization.tex`: 1–548, complete (colored Y, sorts, readout walk, colored translations, triangle/private-path uncoloring, lifts, recognition, corollary).
- `07-game-reduction.tex`: 1–135 (`prop:game-reduction` statement, complete forward announced-bijection proof, start of converse). The ring-transfer converse proof was not read.
- `08-uniformity.tex`: 130–190 (`prop:uniform-construction` statement and size bounds).
- `03-computation-images.tex`, the rest of 04/07/08, figures and README: not read. These parts are credited as stipulated source statements.

Identification companion: `01-introduction.tex` 1–80; `03-encoding.tex` 182–215 (uncolored graph by private leaves); `07-identification.tex` 270–300.

Fixed-dimension companion: `main.tex` 30–75 (abstract and start of introduction); `sections/02-compression.tex` 534–575 (uncolored graphs, hub, marks, one-active-block strategy).

Parity-lifts companion: `01-introduction.tex` 75–125 (main theorem and context).

Navigation over all 44 blobs: case-insensitive search for expan, Cheeger, "open problem/question", "remains open", future, bounded degree, maximum degree, private path, and uncolor. There were no expansion or open-question hits relevant to T133E.

Pinned `lean/docs/133.md` (raw URL at the pin, fetched to `/var/tmp`): all 31 lines.

## Primary literature (my own extractions; the PDFs are byte-identical to the author receipts where applicable)

- CSS, arXiv 1401.0758, `lasserre.txt`: lines 400–509 (CFI definitions, Theorem 3.1, Lemmas 3.2–3.4, Claim 3.5, roadmap, start of Lemma 3.2 proof) and 1082–1321 (all of §5: Definition 5.1, Lemmas 5.2–5.3 with proofs, proof of Lemma 3.4 including the odd-twist case). The SDP/vector construction (§4) was not read.
- LRS, LIPIcs CSL 2025.13, `wl-dimension.txt`: lines 186–205, 740–780 and 860–900, plus navigation over Theorems 1–4 and 19, Lemmas 5–23. The full version (arXiv 2402.11531 / ACM 3798282) and the hardness proofs were not read.
- Chen–Flum–Liu, arXiv 2507.01459v1, `uncolored-cfi.txt`: lines 1–120 (abstract, introduction including the gadget-cost remark) and 2252–2345 (all of §9: Propositions 9.1–9.2, Theorem 9.3 with proof, Remark 9.4, Corollaries 9.5–9.6). Sections 2–8 were not read; the lemmas they cite are credited.
- OWWZ, arXiv 1401.2436v1, `owwz.txt`: lines 1–189 (abstract, introduction, footnote 1 on color removal, technique overview). The asymmetry proofs were not read.
- Hoory–Linial–Wigderson (MGG Construction 8.1 / Theorem 8.2): not independently retrieved or read. I rely on the author's reading; the frame is uncontested classical input.

## Bounded additional search (navigation only)

Web queries (2026-10-18): "Weisfeiler-Leman lower bounds uncolored bounded degree expander graphs removing colors rigid gadget"; "\"Weisfeiler-Leman\" equivalence complexity \"bounded degree\" \"expander\" hardness dimension part of input"; "O'Donnell Wright Wu Zhou … remove colors"; "CFI graphs remove colors bounded degree expander uncolored …"; "reduction colored graph isomorphism to uncolored preserving bounded degree and expansion attach to rigid expander identified by color refinement"; "Margulis Gabber Galil expander asymmetric labelled vertices color refinement individualize root …". Snippets were used only to choose OWWZ for reading.

Unread leads, recorded as unread rather than as absence: Grohe–Lichter–Neuen–Schweitzer (CFI compression, JACM 2025); Seppelt 2024 (coNP-hardness); Roberson (oddomorphisms); Neuen–Schweitzer (IR lower bounds, arXiv 1705.03283); Arvind–Köbler–Rattan–Verbitsky (amenability/compactness, arXiv 1502.01255); Dawar–Khan and Berkholz–Nordström on hard WL instances; the general literature on asymmetric or 1-WL-identifiable bounded-degree expanders used as color palettes. The verdict does not depend on these, because it rests on decomposition into paid operations, not on priority.

## Campaign history

I ran case-insensitive searches of `frontier/iterations`, `reviews`, `findings`, `scouts`, `experiments` and campaign Markdown, excluding copied catalogues, `inputs/` and `private/` copies and this target. Terms: weisfeiler, expander, cheeger, uncolou?red, EXPTIME, gadget, -complete, source/family 133. Hits were read in context (i05, i07, i15, r34, r40, r47, the r64 catalogue survey, and T250P and CM275/RCS128 review headers for standards). No exhaustive semantic reread of all 887 iteration files was performed.

## Not done

No proof review. No formal check. No execution of `diagnostics.py`. No visual PDF inspection. No re-audit of the author's 184/185/245 exclusions.
