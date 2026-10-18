# T117Q contribution review r1: reading and search limits

All paths below are relative to `openai-proof-research/` unless stated. "Author packet"
means `frontier/campaigns/2026-10-14/fresh-structural-discovery-r59/` (manifest SHA256
053986e5a446cd18251b3e3e8b917bc58cafb0f68d6de87562fe190766e28ae2). Line numbers refer
to the files as read; extracted-text line numbers depend on the pdftotext output kept
under the stated private paths.

## Project rules and scope

- `AGENTS.md`, `sources/upstream.json` (pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).
- `frontier/campaigns/2026-10-14/NEW-TEN-2026-10-14.md`: lines 1–200 (acceptance rules
  and count) and the T117Q entries from line 1368 to the end. The rest was not read.
- `frontier/campaigns/2026-10-14/t117q-parent/`: contribution-r1-dispatch.txt,
  source-precheck.json. The proof-r1 dispatch was not used, and
  `frontier/campaigns/2026-10-14/t117q-proof-r1/` was not opened.

## Author packet (read in full unless stated)

candidate.md, original-scope.txt, checkpoint.md, primary-comparison.md,
reading-limits.md, history-reconciliation.json, matrix-selection-derivation.md,
working-interface.md, provenance.md, LICENSES.md, formal-scope.md, verification.md,
verify.py, checks/integrity_controls.py,
checks/matrix_diagnostics.py, checks/matrix-diagnostics.json. report.md,
checks/extraction-replays.json, checks/integrity-controls.json and checks/seal.py were not
read as evidence. source-receipts.json,
primary-receipts.json and source-tree-selection.json were used only as inputs to the
independent blob comparison, not as evidence.

## Source family 117 (author private copies, blob-verified)

- source117-1: main.tex (full); contraction.tex (full, including the good-chart step at
  lines 231–279); directions.tex and directions-proof.tex (full; sphere-net majority
  lemma at directions-proof.tex lines 196–220); metric.tex, repair.tex, reduction.tex,
  kernel.tex (full). references.bib and figures/construction.tex were not read.
- source117-2: main.tex (full) and sections/00-introduction.tex (Theorem thm:main and
  surrounding text). Sections 01–07 were NOT read; they were keyword-screened only.

## Project history

- `rg --no-ignore` over frontier campaign, iteration and experiment notes for family
  117 markers, source117 paths, and S_1/trace-class and negative-type/average-distortion
  keywords (exact pattern list not retained). Private bodies,
  inputs, snapshots, literature caches, the r59 packet and t117q-* directories were
  excluded from the hit review. Only I14 corpus keyword hits and r54 (family 174) notes
  surfaced; both are unrelated.
- Pinned corpus: 9340 cached tex/bib/md/txt blobs under
  `frontier/sources/i14_spectral_width_novelty_r3/corpus`, each re-hashed against
  `sources/preprints-tree.json`. A keyword intersection of S_1 terms with
  negative-type/distortion terms found three unrelated physics papers. This is a
  keyword screen, not a reading of the corpus.

## Third-party literature

Retrieved by this review into `t117q-contribution-r1/private/primary/` (Git-ignored;
SHA256 in replay-record.json):

| Key | Work | Read |
|---|---|---|
| nps2018 | Naor–Pisier–Schechtman, arXiv 1710.08896 | extracted lines ~280–339 |
| naor-young2018 | Naor–Young, arXiv 1701.00620 | lines 590–634 and 870–889 |
| cee2023 | Cordero-Erausquin–Eskenazis, arXiv 2010.11583 | Theorem 13 at lines 466–555; lines 1940–2014 |
| s1-scale2026 | Jiao–Luo–Wu, arXiv 2610.21445 | lines 1–197 (introduction through Theorem 1.3 statement) |
| naor-icm2010 | Naor, "L1 embeddings of the Heisenberg group and fast estimation of graph isoperimetry" (ICM 2010), arXiv 1003.4261 | keyword grep only |
| naor-ribe2012 | Naor, "An introduction to the Ribe program" (2012) | keyword grep only |
| eskenazis-bourbaki2022 | Eskenazis, arXiv 2201.12620 | keyword grep only |
| cnr-stoc2025 | Chang–Naor–Ren, "Optimal Rounding for Sparsest Cut" (STOC 2025) | keyword grep only |

Author private copies (hash-checked in place, not copied):

| File | Read |
|---|---|
| lww2026 (Luo–Wang–Zhou, arXiv 2610.03407) | lines 1–140 (Theorem 1.1 and introduction) |
| quantum-expansion2024 (Escudero Gutiérrez–Muguruza, arXiv 2405.03517) | Section 3.2, lines 218–257 |
| knt2021-arxiv-v1 (Kush–Nikolov–Tang, arXiv 2105.04712) | Section 5.3, lines 1555–1672 |
| knt2021 (published copy) | not read beyond identity |

Web search covered: noncommutative L1 / Schatten S_1 average distortion and negative
type metrics; S_1 embeddings of the Heisenberg group; Schatten class sparsest cut and
quantum/noncommutative cut metrics; Talagrand type and influences for S_1; metric cotype
of S_1 and grid distortion. Exact query strings were not all retained. The first ten
results per query were scanned by title and snippet only.

## Not read (open leads)

- Mendel–Naor, "Metric cotype" (Annals 2008), and Giladi–Mendel–Naor, sections relevant
  to S_1 grids (see review RQ3).
- Cheng–Wang–Xiang (sharp metric cotype 2 for L_1).
- Haagerup–Pisier, Buchholz and other operator-valued Khintchine/Wick sources (Lemma 1
  is treated as a paid tool, so this does not affect the verdict).
- Tropp matrix concentration texts (cited by the author from a browser only).
- Spherical design / derandomization literature for candidate §2.
- Full bibliographies of KNT, LWW, CEE and Naor–Young; forward citations of any of
  them; MathSciNet/zbMATH searches (no access used).
- Li–Qiao–Wigderson–Wigderson–Zhang quantum expansion paper.

Consequence: literature novelty is NOT demonstrated. The verdict is new-to-project
SUBSTANTIAL with bounded literature coverage.
