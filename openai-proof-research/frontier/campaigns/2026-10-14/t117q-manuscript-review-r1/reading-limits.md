# Reading limits: T117Q manuscript review, round 1

## Read completely

- Rules: AGENTS.md, VALIDATION.md, frontier/NEW-TEN-2026-10-14.md (acceptance rules,
  including line 15), and t117q-parent/manuscript-review-r1-brief.txt.
- The frozen manuscript packet t117q-manuscript-v1/:
  - main.tex, all 1035 lines;
  - main.pdf, all 16 pages, rendered and viewed;
  - README.md, editorial-crosswalk.md, reading-limits.md and LICENSES;
  - input-provenance.json, external-read-inputs.json and manifest.json;
  - verify.py, integrity_controls.py and build.py, read before running.
- Prior completed reports:
  - t117q-proof-r1/review.md;
  - t117q-contribution-r1/review.md;
  - t117q-contribution-r2/review.md;
  - t117q-formal-review-r1/review.md;
  - t117q-parent-literature-r1/response.md;
  - fresh-structural-discovery-r59/candidate.md and original-scope.txt;
  - t117q-parent/manuscript-v1-preflight.json.

## Read in part

- Contribution-r1 reading-and-search-limits.md: not read. Its review.md, which
  summarizes those limits, was read in full.
- Release preparation: t117q-release/REPRODUCTION.md only, to locate reproducibility
  instructions. The other release files were not read, and no release verifier was run.
- Formal packet t117q-formal-v1: the toolchain pins were checked, and the Lean files were
  checked to be identical to the manuscript's copies. The Lean development was not
  rebuilt. The formal coverage claims rely on formal-review-r1 and on the manuscript's
  §9 wording matching it.
- Pinned source (copied blobs, Git blob ids verified against preprints-tree.json):
  - directions.tex and directions-proof.tex;
  - kernel.tex, repair.tex, metric.tex and contraction.tex: the operative passages;
  - reduction.tex lines 100–200;
  - main.tex: grep only, to confirm the source exponent 3.
  - Source truth is stipulated and was not audited.

## Primary texts (local extractions, SHA256 in evidence.json)

These are the passages I read myself:

- **JLW 2610.21445v1:** the introduction to the GMN Question 3 discussion, Theorem 1.3,
  (4.5), Proposition 5.2, Steps II–III and Corollary 6.1.
- **MN math/0506201:** the Theorem 1.12 statement (line 422), its proof
  (lines 3005–3062) and Lemma 6.12 with proof (lines 2773–2790).
- **GMN 1003.0279v3:** §1.3 in full (lines 377–505) and the bibliography entries [3],
  [13] and [18].
- **CEE 2010.11583v3:** the Theorem 13 statement, proof (122)–(125), and the Theorem 42
  statement.
- **LWW 2610.03407v1:** Theorem 1.1 only.
- **KNT 2105.04712v1:** Theorem 34 only.
- **Naor–Young:** lines 590–634, including Question 13.
- **NPS:** the header and lines 280–339.
- **EGM:** Section 3.2 and Question 2.

I did NOT read:

- the Bourgain (1987) or Tomczak-Jaegermann (1974) bodies. M1 relies on GMN §1.3's
  explicit statement of their results.
- the full JLW mixing-smoothing proof.
- the full MN or GMN cotype proofs.
- Haagerup–Pisier, Buchholz, Seymour–Zaslavsky or Pisier (1986). These are cited by the
  manuscript as paid standard tools; the manuscript proves the needed forms itself.
- Tropp, and the hardness companion source117-2.

No new literature search, forward-citation search or bibliographic verification of
published versions was performed. Novelty is not assessed beyond checking that the
manuscript's wording stays within the bounded-search qualification. The publication
venues mentioned in O3 were not verified.

## Replays (identity and build only)

- The author verify.py was run with the external anchor (accepted) and with a zero anchor
  (rejected).
- The author integrity_controls.py was run on a /var/tmp copy: 15 cases, with reasons
  checked.
- The exact copied rebuild ran with Tectonic 0.17.0. The PDF and the pdftotext output are
  byte-identical, pdffonts shows all fonts embedded, and the pages were rendered at
  80 dpi.
- The canonical packet was never used as scratch.

None of these is mathematical evidence. The mathematical verdict rests on reading the
proof.

## Scratch

/var/tmp/t117q-msrev-r1/ holds the packet copy, the rebuild, the page renders and the
author-control output. /var/tmp/t117q-msrev-r1-controls/ holds the control copies. These
directories are not package members.
