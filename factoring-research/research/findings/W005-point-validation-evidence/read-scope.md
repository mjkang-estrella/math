# W005 point validation — exact read and source scope

2026-10-08. This is a scoped symbolic review, not a repeat of the W004
archival audit. No mathematical execution, numerical tests, examples searched
by software, Lean or experiments were performed. Shell work was restricted to
reading, retrieving/extracting/rendering primary sources, hashes and writing
the exclusive review paths. No package installation, delegation, commits or
publication. The PDF skill was read for source extraction/visual checks; no
PDF was authored or edited. All research writes are inside factoring-research.

## Task and local inputs

The task is the present NEW independent review round, with exclusive ownership
of W005-point-validation.md and its prefix. The exact original brief, parent
response and predecessor reports were supplied in the conversation and read.
No other child draft was read. The task explicitly forbids taking over parent
ideation, shared state or execution; those restrictions govern older general
team instructions.

Read completely from disk:

- AGENTS.md, 26 lines; RESEARCH_LOOP.md, 77; RESEARCH_TEAM.md, 75;
  docs/SPECIFICATION.md, 122; README.md, 73.
- research/hypotheses/W005.md, 192 lines, saved byte-for-byte as
  [W005-assessed.md](W005-assessed.md).
- research/findings/W005-point-development.md, 97 lines, saved byte-for-byte
  as [point-development-assessed.md](point-development-assessed.md).

research/STATE.md was read for context, not audited. The initial concatenated
output was truncated; the explicit follow-up read comprised lines 1–155 and
690–789 (the final 100 lines). No full-read claim is made for the intervening
history. The supplied newer W004 disposition and W005 assignment override its
stale live-review wording. The predecessor reports were consumed as supplied
task text; their historical manifests were not rehashed and their original
files were not reread. Current local input identities are in
[input-identities.sha256](input-identities.sha256).

## Primary sources actually used

1. **Peter L. Montgomery, “Speeding the Pollard and Elliptic Curve Methods
   of Factorization,” Mathematics of Computation 48 (1987), 243–264.**
   DOI 10.1090/S0025-5718-1987-0866113-7.
   [Publisher](https://www.ams.org/journals/mcom/1987-48-177/S0025-5718-1987-0866113-7/S0025-5718-1987-0866113-7.pdf).
   The publisher returned HTTP 403 through both web and curl. Retrieved the
   original article scan from this
   [repository mirror](https://raw.githubusercontent.com/isislovecruft/library--/master/cryptography%20%26%20mathematics/elliptic%20curve%20cryptography/Speeding%20the%20Pollard%20and%20Elliptic%20Curve%20Methods%20of%20Factorization%20%281987%29%20-%20Montgomery.pdf).
   Stored `montgomery1987.pdf` and layout extraction `.txt`.
   Read §§10.3.1 and 10.3.2, printed pp.260–263, including all the
   square-triple, full-two-torsion, B=A+2 and Suyama construction passages;
   extraction lines 920–1075 (displayed read extended to 915–1083).
   Visually checked all of printed p.262, saved as `montgomery-p262.png`,
   including signs, denominators and nondegeneracy conditions. OCR confuses
   N with A in places; the relevant group-order prose was checked in the scan.
   No other section's complexity or success theorem is imported. The
   identification of our cubic/quotient with his construction is this review's
   algebra, not a claim that his paper explicitly mentions this W005 family.

2. **Daniel J. Bernstein, Peter Birkner, Tanja Lange and Christiane Peters,
   “ECM using Edwards curves,” version dated 2009-12-29**, permanent document
   ID cb39208064693232e4751ec8f3494c43.
   [Author-hosted PDF](https://eecm.cr.yp.to/eecm-20091229.pdf), stored as
   `eecm-20091229.pdf` with layout extraction `.txt`.
   Read introductory §§1.1–1.2 (printed pp.2–3) and the entire §7
   (printed pp.27–29), including Theorems 7.2–7.6 and their qualifications.
   The excerpts read were text lines 35–130, 1285–1395 and 1385–1405
   (including the first paragraph of §8). Visually checked
   all of printed p.28, `eecm-p28.png`, particularly the generic-order
   qualification and Theorem 7.5. The final short proof display on p.29
   was checked in the extracted text. No paper's reported timings or
   successful finite examples were run or adopted as evidence here.
   These authors' Edwards construction is primary prior art; Suyama's 1985
   informal report and Atkin–Morain's original article were not obtained.
   Claims about those older constructions are limited to the explicit
   formulations in this source, not an independent audit of their originals.

3. **Sam Lichtenstein, “Néron Models,” Stanford seminar notes**, 23 pages.
   [Author notes](https://virtualmath1.stanford.edu/~conrad/mordellsem/Notes/L11.pdf),
   stored as `lichtenstein-neron-models.pdf` and layout extraction `.txt`.
   Read §§4.1.6–4.3.2, printed pp.18–20, text lines 813–905. The web
   tool also exposed introductory/search context; it was not a full reading
   of the notes. Used only for the smooth minimal-Weierstrass locus as the
   identity component, its reduction homomorphism, and nodal multiplicative
   reduction. The nodal coordinate map, chord check and section-order proof
   are supplied explicitly in the review. No claim to have read the cited
   BLR, Liu or Silverman books is made.

4. **Razvan Barbulescu, Joppe W. Bos, Cyril Bouvier, Thorsten Kleinjung and
   Peter L. Montgomery, “Finding ECM-friendly curves through a study of
   Galois properties,” arXiv:1202.4285v1, 2012-02-20.**
   [Primary HTML](https://arxiv.org/html/1202.4285v1), stored as
   `ecm-friendly-1202.4285v1.html`.
   Read abstract and §1 Introduction only (web lines 39–59). The tool also
   displayed the beginning of §2. No density result, torsion theorem or
   parameter comparison from later sections is used. This source supports
   the established research scope, not a success law for W005.

All stored source-object and extraction identities are in
[source-identities.sha256](source-identities.sha256). Formulae, genus counts,
valuations, finite-field exceptional-j factorization, and generic-order
arguments in the review were derived symbolically without a CAS.

## Retrieval boundary

Focused discovery queries covered Montgomery's 1987 constructions, Edwards
ECM positive-rank/torsion families, nodal reduction, full-two-torsion ECM and
Jacobi quartics. Search snippets and encyclopedia/repository metadata were
discovery aids only, never evidence for mathematical/prior-art assertions.
The web reader failed on author-hosted EECM PDF versions 2009-01-20,
2009-02-23 and 2009-12-29, plus its papers index; curl successfully fetched
the 2009-12-29 primary object. The AMS 403 was resolved by the article-scan
mirror above. No broad novelty survey or current implementation comparison
is claimed. No downloaded source was executed.
