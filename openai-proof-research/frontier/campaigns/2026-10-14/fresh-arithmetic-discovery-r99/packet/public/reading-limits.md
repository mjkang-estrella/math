# r99 reading limits, timing and provenance gaps

Timing (UTC, 2026-10-20): root created 16:55:27; first source fetch 16:58:42;
source-164 bodies fetched 17:14:34; Hunter and Kousek acquired about
17:16–17:17; scope frozen 17:20:23; proof and packet afterwards. A context
compaction occurred during navigation (before 17:10); reading extents for
items read before it are reconstructed from durable notes and logs, and are
stated conservatively below.

## Pinned sources (retained in `private/upstream/`, see `source-register.json`)

- 164 `Monochromatic-finite-sums-and-products-in-the-positive-integers...`:
  `README.md` read; `build/main.tex` fetched, not read; `01_introduction.tex`
  read in full;
  `02_framework.tex` read at lines 230–319 (finite sums form, chain
  selection, start of the deduction) plus keyword search; `references.tex`
  keyword search only. Sections 03–08 were not fetched or read; they are not
  used.
- 200 EGH: `paper.tex` and `01-introduction.tex` read; `02-reduction.tex`
  partly read. Lex-Plus-Powers `01-introduction.tex` and
  `08-characteristic-zero.tex` partly read. Screening only.
- 005 Catalan: `introduction.tex` and `conclusion.tex` read; whether
  `main.tex` was read before the context compaction is not durably recorded;
  the other sections and `references.bib` were fetched but not read
  semantically. Screening only.
- Catalogue `sources/CONTENTS.md` used for navigation only.

## Primaries (in `private/primary/`, see `primary-register.json`)

- Alweiss, arXiv:2307.08901v6: lines 1–825 of 852 of the text extraction
  (all mathematics, §1–§6; not the tail of the bibliography).
- Bowen–Sabok, arXiv:2210.12290v1: introduction and §4.3 (Corollary 1.2
  proof) read; §2–§4.2 and §5 not read.
- Alweiss, arXiv:2211.00766 (served file is v4): introduction read
  (lines 1–90 and the characteristic remark at 250–260); proofs not read.
- Bergelson–Leibman, arXiv:math/9907201v1: lines 1–394 (introduction,
  §0.13–0.18) and §7.9–7.15, §8.7–8.8 read. The proof of PHJ (§1–§6) was not
  read; Corollary 7.11 is used as stated.
- Hunter, arXiv:2308.10749v1 (only version listed): §1–§2.2 read, lines
  690–730 (Lemma 6.1 sketch) read, keyword search elsewhere.
- Kousek, arXiv:2407.03304v1: abstract and §1.1 read; the journal version
  (ETDS 46(2)) was not obtained.

Not obtained: Bergelson–Leibman–McCutcheon (J. Anal. Math. 2005),
Bergelson–Moreira field papers, Green–Sanders, Moreira's Annals paper body,
Cilleruelo, Shkredov; any function-field Ramsey survey.

## Searches

Six web searches (queries recorded in `external-navigation.json`) plus the
arXiv abstract pages for 2308.10749 and 2407.03304. No characteristic-`p`
FS∪FP statement was found. This is not an exhaustive search and supports no
worldwide priority claim.

## History read

Copies in `private/history/` (`context-register.json`): r98 parent
assessment and intake, r98 screens and reading limits, structural r35
`mixed164.md`, arithmetic r94 `other-screens.md`, structural r130
`other-screens.md`. Navigation-only reads, not copied: r95 family-history
counts, r84–r97 parent assessments (headers), r72 screening of 179,
`structural-r35-disposition.json` and r130 `reading-limits.md` (keyword
lines). Active roots r133 analytic and r134 structural were not read.

## Provenance gaps

- At about 16:55:49Z an author command wrote a scratch file `/tmp/x` (catalogue
  titles) outside the root; it was deleted at once
  (`notes/provenance-gaps.txt`).
- The harness saved some command outputs under `/tmp/droid-terminal-*`
  (harness behaviour, not author writes).
- A `pdftotext` extraction of each primary exists in the root `work/`
  directory (not in the packet).
