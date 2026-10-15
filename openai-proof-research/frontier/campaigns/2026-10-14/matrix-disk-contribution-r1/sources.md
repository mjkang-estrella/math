# Matrix-disk contribution review: sources and access

2026-10-14. Companion to `review.md`. Hashes of local files are in `input-hashes.json`. Pinned mathematical truth is stipulated at commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and is not audited. Server timestamps on external retrievals fall on 2026-10-15 UTC.

## Candidate and internal record

| Item | What was read | Role |
|---|---|---|
| `matrix-disk-discovery/analysis.md`, SHA `e74dda6b…62b6`, 18601 bytes | complete | statement and the bridge |
| `provenance-and-handoff.md` | complete | author's read map; not a gate |
| `inputs.json`, `outputs.json`, `check.py`, `checks.json` | complete | hash binding and the supporting-check inventory |
| `direct.tex`, SHA `54a429fe…333f` | lines 1–160 and 230–530, including `lem:faber`, `prop:coefficients`, `lem:resolvent`, `thm:domain`, and `lem:approx` | pinned direct operations |
| `structural.tex`, SHA `8a5de532…621c` | lines 1–260 and the statements of `thm:structural`, `thm:representation`, `prop:extremal` | scope of the similar-matrix route |
| `AGENTS.md`, `sources/upstream.json`, `frontier/NEW-TEN-2026-10-14.md` | complete | rules and pin |
| R016 finding | complete | same-witness scalarization through dimension four |
| R019 finding | complete | rank-two disk witness; already counted |
| I287 analysis | Sections 1, 5, and 10, and the closing scope paragraph | scalar-gap distinction |
| I245 `analytic-check.md` | Sections 1, 6, 7, and 8 | where the dimension enters, and the matrix-channel remark |
| I291 review | complete | proof status of R019; not a novelty input for this candidate |
| I292 review and its contribution analysis | the review complete; the analysis through the scalar-gap paragraph and the realization comparison | prior separation of inner realization from the original witness |
| I246 contribution review | complete | what was already credited for dimension four |
| `crouzeix-five/analysis.md` | complete | technical dimension-five extension; not a new bridge |
| `jin-v2-sections1-8.txt` | Lemma 8 and its proof, Lemma 9, Proposition 3, Lemma 10, Propositions 4–6 and their proofs, and the proof of Theorem 1 through Corollary 1 | geometric interface |
| `acv-v3-s11.txt` | complete | scalar classification and dimension-three complete corollaries |

The direct manuscript's collar appendix after line 530 was not used. The structural manuscript after the endpoint-extremal construction was not re-read line by line; I292 remains the record of its rational endpoint at the R019 parameters. I245 Sections 2–5 were not re-audited; R016 states their dimension-independent scope.

## Pinned manuscripts

Both local copies match the hashes and byte counts in the discovery `outputs.json`, and those hashes match `inputs.json`.

- Direct proof, `preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/main.tex`, git blob `5976502d77febf477933f36f6205c6e1aa6370ae`. The complete bound is stipulated. The equality comparison uses the kernel formula, the coefficient proposition, the diagonal test at the displayed finite \(N\), the positive-block comparison, and the outer-approximation statement.
- Structural companion, `preprints/The-complete-Crouzeix-theorem-September-23-2026/build/main.tex`, git blob `2ace452c83a9ceb994a87ae9009441706d90a961`. Used for the optimal-metric and common-density statements. The catalogue entries in `sources/CONTENTS.md` for items 325 and the two preprints were checked for duplicate equality corollaries. The catalogue states the complete bound and the similar-matrix representation. It states no disk-rigidity theorem.

`sources/preprints-tree.json` lists these two Crouzeix preprint directories and no third equality manuscript at the pinned commit.

## Primary literature read in this review

### Jin, version 2

Shanmu Jin, *Rigidity at the Extremal Crouzeix Constant*, Preprints.org `202609.0079`, version 2, posted 15 September 2026. The retained extract `jin-v2-sections1-8.txt` is the text used for Lemma 8, Propositions 3–6, and the proof of Theorem 1. A fresh `curl` of `https://www.preprints.org/manuscript/202609.0079/v2` returned HTTP 403. No fresh whole-page hash is claimed. The live version-2 rendering, retrieved through search, displays Theorem 1 as scalar disk rigidity and Proposition 6 as the circle criterion with the coprime full-level, degree, strict-convexity, nonvanishing-derivative, and Hermitian-determinant hypotheses. That displayed Proposition 6 matches the extract. Sections after Corollary 1, including the domain-constant argument, were not read in this round. They are outside the candidate's hypotheses.

### Åhag–Czyż–Virtanen

Per Åhag, Rafał Czyż, and Jani Virtanen, arXiv:2608.27346.

- Version 3, Section 11, local extract `acv-v3-s11.txt`, read complete, including the proofs of Proposition 11.1, Theorem 11.2, Corollaries 11.3–11.5 and 11.8, Lemma 11.6, Theorem 11.7, and Proposition 11.9.
- Version 4, 21 September 2026, HTML `https://arxiv.org/html/2608.27346v4`, read from the abstract through Theorem 1.7, the equality paragraph that cites Corollary 12.4 and Theorem 12.2, Theorem 5.3, Proposition 5.4, and the statement and proof of Corollary 12.4 together with the opening of Corollary 12.5. The introduction records that Jin and Lorist–Schwenninger do not directly give the completely bounded inequality, and that \(1+\sqrt{2}\) was still the best universal complete bound in that paper.

The full v4 PDF was not opened. Proofs in v4 Sections 6–11 and 13 were not re-read. Theorem 12.2 was compared through the introduction's statement and the unchanged mathematics of v3 Theorem 11.2. No all-dimensional complete disk theorem appears in the sections that were read. The v4 text still limits Corollary 12.4 to dimension at most three.

### Family and classical interfaces

- Crouzeix–Greenbaum, arXiv:2508.12768v1, preprint PDF text: Lemma 1 and Theorem 2 for the weighted-shift family, equating \(\psi\) and \(\psi_{\mathrm{cb}}\) and giving a strict inequality when the weight product is nonzero. The rest of the paper was not read.
- Crouzeix, *Some constants related to numerical ranges*, public PDF text of Section 10 through Lemma 10.1 and the following remark on \(2\times 2\) and \(3\times 3\) disks. The remainder of that paper was not re-read. I292 already used Section 10 as a scalar disk interface.
- Beckermann–Stylianopoulos, arXiv:1606.00553, HTML and PDF text of the Grunsky inequality (1.3) and the \(L^2\) identity (1.6)–(1.7). Read as the calculus cited by the direct manuscript. Equality there is not a numerical-range theorem.
- Leake–Lins–Spitkovsky, Operators and Matrices 8 (2014), Theorem 5.7, only as invoked and scoped by `crouzeix-five/analysis.md`. The publisher PDF was not reopened in this round.
- Lorist–Schwenninger, arXiv:2608.03841, was not opened. The interface is the explicit limitation stated in Åhag–Czyż–Virtanen v4.
- Knese, arXiv:1907.13191, was not reopened. I292's comparison of Theorems 2.1 and 3.1 with the R019 witness is the record used here.

## Searches

Bounded queries on 2026-10-14/15, with the results actually opened:

- complete Crouzeix equality, matrix polynomial, numerical-range disk;
- \(\psi_{\mathrm{cb}}\) equality in all dimensions, arXiv:2608.27346;
- Jin, Proposition 6, matrix-valued polynomial;
- arXiv listings for Crouzeix after the scalar rigidity preprint;
- Grunsky and Faber equality cases in Beckermann–Stylianopoulos;
- MathDB queries for a posted complete-equality disk problem. The hits returned were unrelated problems. No MathDB statement of this package was retrieved, and none is used as a premise.

The OpenAI catalogue and preprint tree were searched locally for a third Crouzeix manuscript. Only the direct proof and the structural companion are present at the pin.

## Access limits

- Jin v2: HTTP 403 on direct retrieval. Theorem statements used from the retained extract, checked against the live rendering of Theorem 1 and Proposition 6.
- Åhag–Czyż–Virtanen v4: HTML through the interfaces named above. Full PDF and the unread section proofs are outside this review.
- Lorist–Schwenninger PDF: not opened.
- Crouzeix 2016: Section 10 interface only in this round.
- Leake–Lins–Spitkovsky PDF: not reopened; the parent note's citation of Theorem 5.7 is the interface.
- Knese: not reopened.
- I245 full limit argument: not re-audited.
- No claim that every paper on numerical-range equality was examined. The negative search was for a theorem that already preserves arbitrary dimension, a specified finite matrix polynomial, the fixed unitary channel, the exterior inverse, and the full lemniscate.

## Hash note

`frontier/NEW-TEN-2026-10-14.md` has SHA-256 `b28ab7f8…9df9`, the same value recorded in the discovery `inputs.json`. The frozen analysis hash matches the prescribed value `e74dda6b…62b6`.
