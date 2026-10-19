# Reading, provenance, and limits

The pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. `private/upstream-receipts.json` lists every acquired source file, its pinned raw URL, Git blob, byte count, SHA256, and authenticated local origin. These are local-corpus reuse receipts, not fresh successful raw-HTTP claims. Every acquired file was checked against the complete 13,223-entry, nontruncated preprint tree. `private/selected-tree-entries.json` carries the selected tree entries; `private/complete-tree-receipt.json` binds the full locally parsed tree. The full tree is not copied into the packet.

`AGENTS.md` and `sources/upstream.json` were read completely. All entries of `sources/preprints-tree.json` were parsed/traversed; parsing is not semantic reading of every manuscript. A whole-catalogue display of `CONTENTS.md` truncated, so the catalogue was subsequently parsed and selected structural blocks read. This is catalogue navigation, not a claim to have semantically read every abstract. The campaign requirements opening and operational-history portions were read, including current 18/20 and stopped publication/browser work; some large outputs truncated. The accepted findings were checked through scope openings in smaller batches. The context receipts identify the local bytes at archive preparation, without copying massive historical bodies.

## Direct upstream semantic reading

| Source | Actual reading | Limits |
|---|---|---|
| 118 | `introduction.tex`; `trees.tex`; `completeness.tex`; `consequences.tex`, complete. `instance.tex` through line 490, including theorem, geometry, inventories, scalar encoding, label control, and start of good-feasibility; inventories/encoding/geometry reread in narrower blocks. | `soundness.tex` acquired but not semantically read. Its theorem contract is stipulated; no claim to independently reconstruct that proof. Preamble/main/bibliography were navigation. |
| 157 positive | Complete introduction, preliminaries, and list-transfer section. | Small-graph, density, routing, separability, recursion files were acquired for bounded navigation but not completely semantically read. No full-paper read claim. |
| Hadwiger negative companion | Complete introduction, including main connected-matching theorem, minor inequality, fractional corollary and construction overview. | Included history file and proof bodies not acquired/read. |
| Colin-de-Verdière companion | Main definition/theorem, rank obstruction, minor implication, explicit linear-list corollary and closing construction overview visible in the introduction output. | Middle of the long combined display truncated. No complete-introduction or proof-body reading claim. |
| 186 graph | Complete `sections/graph.tex` and `sections/threshold.tex`, including restriction, block estimate, capture, variance and threshold proofs. | Other acquired files were navigation; no claim to have reread the entire Fourier proof in the graph version. |
| 186 hypergraph | `introduction.tex` main theorem lines 1–44 separately reread; operative `restriction.tex`, `completion.tex`, `fourier.tex` displayed and read. | Earlier combined output with a web result truncated at its opening; no claim of complete reading of every introductory paragraph. The operative block/capture and main-proof portions were read. |
| 178 | Introduction first 200 lines, including theorem and repair architecture overview. | Setup/algorithm/accounts/reference files acquired but not semantically read. Historical r45/r26 operations were read as historical evidence, not substituted for a complete fresh primary-source proof read. |

Exact labels relied on are recorded in the screens. The 186 graph labels are `lem:restriction`, `prop:block`, `lem:block-capture`, `thm:variance`, `thm:threshold`; the hypergraph main label is `thm:main`. Source 157's main statement and list-transfer are the source interfaces; no new theorem is claimed from an unread subsection. The companion introductions' `thm:main`, Hadwiger `cor:hadwiger`/`cor:fractional-hadwiger`, and Colin-de-Verdière `cor:list-spectral` were inspected as described above.

## Primary versions and proof extents

Successful URLs, retrieval time, PDF SHA256, extraction SHA256, and byte counts are in `private/primary-receipts.json`. Line numbers below refer to the sealed pdftotext-layout files, not journal line numbering.

| Stem | Version and actual extent |
|---|---|
| `dp-random` | Dvořák–Yepremyan, arXiv:2307.15048v1. Lines 140–265 (definitions, Theorem 2.2, Observation 2.4 and its proof), 690–930 (appendix Observation 4.1 through proof of Theorem 2.2, ending the file). Other random-graph theorems not proof-read. |
| `gluing` | Rothvoss, arXiv:1301.4010v1. Lines 475–537, Section 4.2, Lemma 8 proof and Corollary 9. Other approximation machinery not proof-read. |
| `support` | Official ESA 2025 LIPIcs 351, paper 48 PDF. Lines 270–385, Section 3 aggregation setup and statement; that version defers the proof. |
| `support-full` | Jansen–Pirotton–Tutas, arXiv:2512.02758v1. Lines 350–553 cover the aggregation Lemma 5 proof, including dominant radix term, slack bounds and induction; reading continued through line 585, into Section 4 opening. Support-lower-bound construction and full proof not read. |
| `permutations` | arXiv:1007.2170v3 failed HTTP 404. arXiv:1007.2170v2 succeeded. Lines 155–219 (Theorems 1–2 and discussion), 527–610 (Section 6 support-constrained rounding setup). No full lower-bound-proof reading claim. |
| `slice` | Filmus, arXiv:1406.0142v2. Lines 1076–1160, complete Lemmas 5.5–5.6 and proofs. Earlier orthogonal-basis construction not read. |

Web snippets/abstracts served navigation only. No priority clearance is based on them. The successful primary versions are linked at their operative comparisons in the screens. Local primary PDFs/text retain their original rights; they are not part of the original public prose/code.

History reading depths and truncation limits are in `history.md`. Negative history outcomes were used to locate exact interfaces, not adopted as mathematical or contribution verdicts. No statement here asserts exhaustive literature coverage.
