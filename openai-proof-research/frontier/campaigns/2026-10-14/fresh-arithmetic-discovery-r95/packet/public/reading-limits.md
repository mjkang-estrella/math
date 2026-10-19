# Reading and timing limits

## Timing

- No freeze happened at any point.
- The 041 decision came in two steps.
  1. Matsushita 0903.2098v2 and Greb–Lehn 1303.3919v2 were read, and the Matsushita-route feasibility sketch was worked out.
  2. The degenerate-twistor paragraph of the source introduction (lines 110–160) was read only after that sketch. It confirmed that the operation is paid. This late read is disclosed and is not backdated.
- The final no-size-cutoff alias search (`private/search/final-alias.json`) ran after the PREFREEZE decision. Its hits are file and match counts, not semantic reads or absence certificates.
- Earlier authored-history checks used targeted `rg` searches over campaigns and iterations. The operative hits read were r84 `packet/public/geometry.md` (041 section) and the r72 catalogue-level rejection. Generated or copied mirrors (CONTENTS copies, corpus snapshots) were treated as navigation.

## Pinned source bodies

All 16 bodies are in `source-register.json`. Each was blob-checked against `sources/preprints-tree.json`.

- 017: all fetched files read in full.
- 041 Projective-Space-Bases:
  - `01-introduction.tex` read in full.
  - `07-deformation.tex` lines 1–270 read. The `def:fixed-base` proof (lines 84–202) was read closely. Lines 271–494 (the $b_2\ge5$ argument) were not read.
  - `12-conclusion.tex` read in full.
  - Sections 02–06 and 08–11 were not fetched or read.
- 041 Strong SYZ: introduction lines 1–129 read, and `grep` was used for the remaining lines. Other sections were not fetched.
- 016, 037, 062: the introductions (and the 037 conclusion) were read. Proof bodies were not read.

A local corpus mirror of source041 (`frontier/sources/i14_spectral_width_novelty_r3/corpus/...`) was used only for a `grep` of "twistor" in sections that were not fetched. Nothing from it is relied on.

## Primaries

Three primaries were retained as PDF and `pdftotext` pairs (see `primary-register.json`):

- Matsushita 0903.2098v2: abstract, Section 1 statements (Theorems 1.1, 1.2, Corollary 1.3, Remark 1.5) and the start of Section 2.
- Greb–Lehn 1303.3919v2: read in full (short note).
- Campana 1712.01902v2: read in full (short note).

Not acquired: Verbitsky 2015, Soldatenkov–Verbitsky 2025, Fujiki 1983, Huybrechts' projectivity criterion, Barroero–Dill 1909.01271, and the 017 external preprints and issues. These are listed in `external-navigation.json` as navigation only.

## Scratch

- A temporary slug-count file was created and deleted in the owned directory during catalogue exploration.
- The `work/` scratch directory was emptied by moving its contents into `packet/private`, and then removed.
- `private/acquisition/fetch.py` is kept as a record. Its relative paths refer to the former `work/` location.
- Harness-truncated command outputs were written by the tool harness outside the repository, not by this runner.
