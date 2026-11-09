# r133 source, primary and history reading limits

Author: Myeongjin Kang. CC BY 4.0. Runner: Factory Droid / claude-opus-5-5 / high. Times are UTC, 2026-10-20.

## Inputs (read in full, 16:47–16:52Z, before any derivation)
- AGENTS.md; expanded-target-2026-10-17/research-brief-2026-10-20.txt; fresh-analytic-r133-brief.txt.
- r132: REPORT.md, packet/public/report.md, packet/public/reading-limits.md, work/notes.md; discovery-analytic-r132-parent
  intake.json and primary-metadata-check.json. r132 scratch was not run, copied or modified. r132 packaging files
  (FINAL.json, CONTROL-RESULTS.json, packet/public/verify.py) were viewed at 17:36Z only as a format reference.
- SHA-256 hashes of every input file are in work/input-hashes-start.txt; they were rechecked at sealing time.
- Late (after the freeze, about 17:40Z): frontier/NEW-TEN-2026-10-14.md lines 1–60, including the "Acceptance and
  publication" rules, and sources/upstream.json (pin fd4aeeb2…, commit date 2026-10-08). Nothing in them changes the
  frozen scope. The theorem is labelled as a bounded-facet partial advance, not a solution of Brannen's problem.

## Sources and primaries
- **FHLX**, arXiv:2610.13953v1 (Feng, Hu, Liu, Xu, *On the Reverse Projection Inequality*). Read through the
  I43-retained text frontier/sources/i43_convex_isoperimetric_discovery/literature/reverseprojection.txt, lines
  1–1092, in full: Thm 1.1–1.3, §2, §3, §4 Props. 4.1, 4.2, Lemmas 4.3, 4.4, Props. 4.5, 4.6, lifting (4.19), and the
  references. The arXiv abstract page (https://arxiv.org/abs/2610.13953) was fetched at 17:19Z. It shows v1 only,
  submitted 2026-08-16. The arXiv PDF and TeX source were not fetched.
- **Source P** (pinned openai/math fd4aeeb2…, preprints/A-product-counterexample-to-the-simplex-maximum-for-
  projection-body-volume-September-24-2026/): README.md, build/main.tex and build/references.tex, fetched from pinned
  raw URLs. The Git blob SHA-1s match sources/preprints-tree.json (b46aac76…, c3218753…, b5ca002e…). main.tex was read
  in full. paper.pdf was not fetched. Copies are in packet/private/upstream (original rights).
- **Petty companion** (preprints/Pettys-projection-volume-conjecture-in-dimensions-at-least-four-September-24-2026/):
  README.md, build/latex/main.tex, sections/01_introduction.tex, 06_conclusion.tex and 07_consequences.tex were
  fetched at 17:37Z from pinned raw URLs. The blob SHA-1s match the tree (2e447b49…, b9da2920…, 9a16c910…, 0f71c3a9…,
  ce889945…). README, main.tex, the introduction and the first part of the consequences were read. The fetched
  sections contain no mention of Brannen, simplices or upper bounds; the companion concerns the lower bound only.
  Sections 02–05 were not fetched. This read happened AFTER the freeze and is disclosed as late. It found no overlap.
- CONTENTS.md entry 088 (lines 2161–2179) was read.
- **Saroglou**, arXiv:1409.4347v2 (*On the shape of a convex body with respect to its second projection body*): the
  HTML introduction, §2 and the references were read at 17:19Z, before the freeze. Prior sharp upper-bound results
  described there are in dimension 3 only.
- **Saroglou 2011** (Mathematika 57): the PDF at myweb.uoi.gr failed TLS certificate verification. The failure was
  not bypassed, and the body was NOT read. Its content (3-dimensional zonoids, cones, double cones) is known only from
  FHLX and Saroglou 2014.
- **Brannen 1996, 2005; Chen–Feng–Li–Xi–Xu 2026; Henk; Lutwak–Yang–Zhang**: not read. They are known only from
  FHLX's introduction.
- **Classical facts (F1)–(F8)** in proof.md (Minkowski, Cauchy, Shephard/McMullen zonotope volume, Prékopa,
  Brunn, coarea, Gamma–Dirichlet, Jacobi) are cited as standard. Their primary bodies were not reread. The HNBUE step
  (Lemma 6) and the partial-fraction formula (Lemma 7) are proved in full in proof.md instead of being cited
  (Barlow–Proschan / Klefsjö for HNBUE were not read).
- Web searches (17:18–17:21Z, 4 queries) found no result on Brannen's inequality in dimension 4 or for n+2 facets.
  arXiv:2610.18268 (Brauner, Ortega-Moreno, Schuster) was opened and is unrelated. This is search-limited and is not a
  worldwide-priority statement.

## Project history search (16:52–17:05Z)
- `rg -uu` (hidden and ignored files included, no size cutoff) over the whole project.
- Excluded: the active rounds fresh-arithmetic-discovery-r98, discovery-arithmetic-r98-parent and
  fresh-structural-discovery-r134; t106o133-* roots; this root; .git; site-packages; and frozen, corpus, pinned,
  snapshot and inputs copies (copied corpora and catalogue copies).
- The narrowed terms (Brannen, reverse projection, 2610.13953, FHLX, simplex maximum, n+2 facets) hit 155 files.
  Operative hits that were followed: iterations/i43 §1.3 (lines 60–82; RP4 parked after exact simplex-product tests
  n=4..8), the r112 research-report 088 paragraph, r131 notes (numerical vertex search in n=4) and r132 (read in full).
  The other hits were CONTENTS copies and ledgers. No antecedent of the HNBUE comparison, of (S)_n, or of any n=4
  proof was found.
- A broader query that also included B-spline, divided difference, Dirichlet mean, Markov–Krein and projection body
  returned 1692 files, dominated by unrelated uses and copies. It was not followed further (disclosed limit).
- The hit lists were written to /tmp/r133-hits*.txt, outside the assigned root. This violated the write-only-root
  rule. They were deleted at 17:20Z; their contents were path lists only.
