# Reading limits

Line numbers refer to the files whose hashes are recorded in `checks.json`.

## Manuscript (frozen `../t212m-manuscript-v1/`)

Read in full, line by line: `public/main.tex` (61 lines), `public/references.tex`
(8), `public/sections/01-scope.tex` (82), `02-cap.tex` (140), `03-metric.tex`
(109), `04-reference.tex` (194), `05-labels.tex` (173), `06-splice.tex` (128),
`07-finish.tex` (183), `08-use-sites.tex` (109). Also read in full:
`README.md`, `reading-limits.md`, `editorial-crosswalk.md`, `LICENSE.md`,
`build.py`, `verify.py`, `controls.py`, `provenance.json`,
`validation/visual-qa.json`. The `evidence/` copies of the prior gate reports
were checked by hash. I read the originals in their own directories, not the
copies.

PDF: all 19 pages rendered at 70 dpi in /var/tmp (disposable) and inspected
as five 2×2 contact sheets. This is a layout inspection at reduced resolution.
I did not proofread each glyph against the source. Text extraction
(`pdftotext`) was used only to search for "??" and the licence line. The PDF
was not rebuilt; the package's two build receipts were checked against the
PDF hash by the package verifier.

## Stipulated source S (fd4aeeb2, private cache of the r74 candidate)

Read in full: `build/sections/01-introduction.tex` through
`08-conclusion.tex`. Not read: `09-boundary-comparison.tex` (the manuscript
declares it unnecessary; I checked that claim against AH 4.6 instead),
figures, `main.tex` beyond its `\input` list.

## Primary texts (private cache, text extractions)

- AH arXiv:1609.02447v2 (`ahlberg-hoffman-v2.txt`): lines 255–983 (§§2–5,
  including Lemma 4.6 at 649–671, the start of the Prop 4.4 proof at 672–700,
  and Lemmas 5.3–5.6 at 824–948); lines 1555–2712 (§8 in full, including
  Lemma 8.6 and (21); §9 in full, including Prop 9.2, 9.5, 9.7–9.13 and the
  9.10 Case 1 rectangle); §10 (2709–3100) by outline and theorem statements
  only. A keyword search located "tangent" (268–269) and the energy uses
  (Remark 3.2). **Not read:** §§6–7 (983–1555) beyond theorem statements
  found by search; §10 proof bodies.
- DH arXiv:1209.3036v1 (`damron-hanson-v1.txt`): lines 255–335 (A1′, A2′,
  rounding (1.4), Def 1.9, Thm 1.10); 520–650 (Prop 2.4, §3 construction,
  μ*_n averaging, L_α); 1120–1190 (Thm 4.6, Cor 4.7, start of §5); 1330–1609
  (§6: Thm 6.1, Lemmas 6.2–6.6, triple extraction, §6.2.2). **Not read:**
  §§3–5 proof bodies (650–1120 and 1190–1330). These are used under A2′ as
  stated hypotheses, and I verified that the cap meets them.
- DHb arXiv:1512.00804v2, ADH, Cerf–Théret: I did not read their bodies. I
  checked only that the manuscript's citations of them agree with the earlier
  gates' records. No Boivin, Cox–Durrett or Kesten body was read.

## Prior gates

Read: `../t212m-proof-r1/review.md` and `reading-limits.md`;
`../t212m-contribution-r1/review.md` and `reading-limits.md`;
`../t212m-formal-review-r1/review.md` and `reading-limits.md`; the T212M
entries in the shared ledger (read only). The formal supplement was not
rebuilt. Its counts (14 support, 17 controls) were compared with the
manuscript only.

I did not read `../t212m-release-preparation/`, which appeared in a parent
commit during this review. It was not used.

## Trust and independence

No nested agents were used. No frozen author file was edited. Nothing was
staged, committed or uploaded, and no shared ledger was changed. Primary and
source bodies are not copied here. The upstream truth of S, AH and DH is
accepted as stipulated or primary input under their hypotheses, per
AGENTS.md.
