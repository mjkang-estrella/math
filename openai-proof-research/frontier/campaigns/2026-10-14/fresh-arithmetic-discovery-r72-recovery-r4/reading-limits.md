# Reading limits

All upstream files are at pinned commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; blobs and SHA-256 are in
`source-receipts.json` and are checked by `tools/verify.py`.

## Read (source242, `preprints/Single-fold-Diophantine-representations-September-24-2026`)

- `build/main.tex`: statement of Theorem `thm:main` (lines 56–64), the
  introduction, the paragraph on non-displayed constants before Corollary
  `cor:unique-h10`, the proof overview (rank-one curve E: y² = x³ − 25x,
  height window W_k ≤ u + W₁ < W_{k+1}, selection of r = k²), and the
  conventions on sign codes and composition (Lemma `lem:composition`).
- `build/consequences.tex`: whole file, including the closing remark that
  the corollary makes no claim over ℤ or ℚ.
- `build/power.tex`: lines 15–60 and 255–280 only (witness uniqueness,
  "a nonnegative square root is unique").
- `build/elliptic.tex`: lines 50–85 only (rational-code lemma, sign codes).
- `README.md`, `build/height-window-figure.tex`: whole files.
- Keyword scans (grep only, not reading) of `computation.tex`,
  `rank-one-proof.tex`, `witness-ledger.tex`, `references.bib`.

Not read: the remainder of `power.tex` and `elliptic.tex`, and all of
`computation.tex`, `rank-one-proof.tex` and `witness-ledger.tex`. Nothing in
this archive depends on their internal arguments; only Theorem `thm:main`
and Lemma `lem:composition` are used, as stipulated truths.

## Read (source004, `preprints/Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026`)

- `build/sections/01-introduction.tex` and `build/sections/07-consequences.tex`
  (screening only; nothing from source004 is used in any argument).

## Outside sources (navigation only, not relied on for any proof)

- D. Cantone, L. Cuzziol, E. G. Omodeo, "On Diophantine singlefold
  specifications", Le Matematiche 79 (2024) 585–620,
  doi:10.4418/2024.79.2.18. Local private copy, identity in
  `primary-identities.json`. Read: title, abstract and keyword scans for
  integer-unknown statements.
- A. Tyszka, arXiv:1309.3673 (finite-fold representations; uses four
  squares). Abstract and visible text only.
- MathOverflow question 249514 (J. Robinson's definition of ℕ in ℤ via
  Pell). Visible page only.
- Web search results on Z.-W. Sun's work on Hilbert's tenth problem over ℤ
  with few unknowns: result titles and snippets only.

## Novelty and priority

Not cleared. This recovery did not establish whether (N_ℤ), a polynomial
bijection ℤ^k → ℕ, or Lemmas O1–O5 appear in the literature. Lemma O4's
degree-2 case and Lemmas O2/O5 are elementary and are likely known in some
form. No literature status is claimed for T242Z.
