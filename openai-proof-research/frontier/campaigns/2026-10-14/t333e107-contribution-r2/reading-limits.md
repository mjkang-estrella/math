# T333E107 r2: reading extents, provenance and limits

All reads below were made in this round (Opus 5.5, 2026-10-18). A read means
the full displayed text was read. Truncated displays are noted. Hashes are
SHA256 unless stated otherwise. All writes are confined to
`t333e107-contribution-r2/`.

## Repository context

- Root `AGENTS.md` (11 lines) and `sources/upstream.json` were read in full.
  The pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
- `sources/preprints-tree.json` was parsed completely: 13,223 entries
  (10,373 blobs, 2,850 trees), `truncated=false`, 749 top-level preprint
  directories. `sources/tree.json` was not used.
- A directory-name screen of the complete tree, for isometric, embedding,
  surface, immersion and related terms, found one source333 manuscript and
  the source334 companion. It also found two four-dimensional
  *topological* disk-embedding manuscripts (Freedman–Quinn context), whose
  catalogue abstracts (`CONTENTS.md` l.7535–7547) were read and judged
  irrelevant.
- `CONTENTS.md` entries 333 and 334 (l.8110–8155) were read. The full
  catalogue was not semantically read.

## Author packet (read-only)

All twelve top-level files of `fresh-analytic-discovery-r107/` were read in
full: README, scope-freeze, proof, operation-comparison, hostile-checks,
reading-limits, upstream-provenance, primary-provenance, integrity-controls,
manifest (structure plus payload list via a parser), seal and verify.py.
Detached digests match: manifest e3b99201…, proof 4455d5af…, scope e195f3c7…,
operation-comparison 8317827e…. I read the author's verifier before executing
it with `python3 -I` and the detached digest. Result: verified, 34 payloads,
26 anchors, 13 pinned blobs, 4 PDFs. The author's control receipt is the
author's own and was not adopted as independent evidence.

## Source333 semantic extent (retained author private copies)

Every file below was read in full in this round, and all 13 Git blobs match
the complete tree:

- `introduction.tex` (152 lines)
- `preliminaries.tex` (208)
- `primitive-statement.tex` (147)
- `small-modes.tex` (433)
- `exact-correction.tex` (403)
- `velocity-loop.tex` (373)
- `primitive-realization.tex` (446)
- `geometry-preservation.tex` (289)
- `global-construction.tex` (375)
- `main.tex` (54)
- `figure-geometry.tex` (67; TikZ code and caption only, not rendered)

`refs.bib` was screened by entry keys only (17 keys), not read for content.

Source334: the first ~150 lines of `companion334-main.tex` (228 lines) were
read, covering the title, Theorem A, the context discussion and the start of
the proof-structure discussion, with `\usepackage` lines filtered from the
display. The remaining ~78 lines and all lower-level source334 proof files
were not read. Theorem A is a local R^3 non-immersion result. This
classification uses no source334 operation.

## Primary semantic extent (author-retained private copies; identities from author provenance, re-verified by the author verifier)

Line numbers refer to the retained `pdftotext` text.

- **De Lellis–Inauen–Székelyhidi 2018** (`dlis2018.txt`): l.1–60 (abstract,
  Theorem 1.1, introduction), l.1090–1185 (end of Step 1, complete Remark 8.1,
  start of §8.2) and l.1320–1385 (complete final embedding proof of Theorem
  1.2). Lines 60–135 were only searched by grep in this round. Page images
  were not viewed, and the Hölder iteration was not read.
- **Cao–Székelyhidi 2306.12879v1:** l.1–60 (abstract, introduction) and
  l.470–793 (complete §3.1, including Lemmas 3.1–3.2, Proposition 3.3 with
  full proof, the p.14 embedding sentence and the start of §3.2). Lines
  60–148 and 330–468 were not read in this round.
- **Le Donne 1005.1623v2:** l.227–419 (all of §3, including Theorems 3.1–3.2,
  Lemma 3.5, the construction, the path-isometry proof and the injectivity
  proof). The Federer reference for Lemma 3.5 was not acquired.
- **Gromov, Oct 9 2015 manuscript:** l.2660–2750 and l.3280–3340, as context
  only.
- **Not read:** Nash 1954/1956, Kuiper, Whitney, Hirsch or any textbook
  tubular-neighbourhood or openness proof, Gromov PDR, and the original
  surface-classification proof. None receives operation credit. The tube and
  openness facts used are proved inside author §2 and re-derived in review
  §4. The handlebody embedding of orientable surfaces is identified
  explicitly as a standard topological input.
- No new download or web retrieval was attempted in this round, so there
  were no unsuccessful retrievals. All evidence came from the author's
  retained, integrity-verified copies. No browser UI was used.

## Same-family companion bodies (read in full in this round)

- `fresh-parent-discovery-r5/screen.md` (1aabf5a289d6987587ade7945c4b2dfcda114e3b62105d1c513bc6276e8aceab)
- `fresh-analytic-discovery-r17/source-reading.md` (80691b1af7811661caf99abed4e314fda2f519e512ee8bfb7e42dc825652a243)
- `fresh-structural-discovery-r92/screening.md` (5ccd17502ca58c4315d92a98bfb60cc87386600e59a7a03a309ecf0f6e99b5cc)
- `fresh-analytic-discovery-r17/candidate.md`, l.48–60 only (493a4141…)

In r17 and r92, the unrelated graph-theoretic and degree-theoretic passages
were displayed but not used.

A content search over non-private frontier Markdown for T333, source333,
family 333 and isometric embedding found, besides the above, only:
- the r107 packet;
- the r1 drafts;
- `t333e107-contribution-r3/` and `t333e107-parent/`;
- exclusion or "lesson" mentions in r9, r22, r109, r111, r112, r78 and r116
  (lines inspected via grep context only);
- unrelated geometry and K3 reviews.

None of these develops an embedding argument. Search absence is not
eligibility clearance.

## Deliberately unread

`t333e107-contribution-r3/` (all files) and every file in
`t333e107-parent/` except directory listings were left unread. These include
`contribution-disposition.json` and the r2 brief copy. Leaving them unread
preserves independence. Their contents are unknown to this review.

## r1 drafts (read in full as prior findings)

The four prose drafts were read in full: `review.md` (7200ca89…),
`paid-unpaid-comparison.md` (f35b226e…), `reading-limits.md` (c8585134…) and
`README.md` (2d4551a4…). `author-baseline.json` (f6a01dfe…) and `verify.py`
(be57822c…) were hashed only; they were neither executed nor adopted. The
`checks.json`, `integrity-controls.json` and seal referenced by the r1 drafts
are absent, so the corresponding r1 claims are unauthenticated.

## Integrity and rights

- This bundle contains only original prose and code: no third-party copies
  and no `private/` directory. External files are bound by hash in
  `manifest.json`.
- `checks.py` performs finite exact and float checks (results in
  `checks.json`). These are not proofs.
- Integrity controls ran on a copied bundle and a copied anchor subset in a
  temporary directory under `/tmp`, which was removed afterwards. No
  repository file outside this directory was modified.
- No git operation, staging, commit, PR, upload, contact, browser UI, nested
  agent, manuscript or formalization was used.
