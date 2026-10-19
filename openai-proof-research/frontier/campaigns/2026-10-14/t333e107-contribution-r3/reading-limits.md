# T333E107 r3: reading extents, provenance, and limits

Source truth and proof operations are stipulated at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. No upstream audit was attempted.
This file records what this review actually read in this round. Reading
claims made by the author or by the r1 drafts are not inherited.

## Repository context

- Read `AGENTS.md` (11 lines) and `sources/upstream.json` in full.
- Parsed the complete `sources/preprints-tree.json`: 13,223 entries,
  `truncated=false`. It lists 16 paths under the canonical source333
  directory: the directory itself, `build/`, 12 build files, `README.md`, and
  `paper.pdf`. `sources/tree.json` was not used. `sources/CONTENTS.md` was not
  read in this round. Family identification relied on the complete tree and on
  source333's own text, not on catalogue summaries.
- Read lines 1–30 of `frontier/NEW-TEN-2026-10-14.md`, with each line cut at
  400 characters. This covered the 18/20 status and the model-allocation line
  naming Factory Opus 5.5 as the Claude-limit fallback. The rest of the ledger
  was not read.
- Read `t333e107-parent/contribution-review-status.md` in full and listed the
  parent directory. The parent briefs and dispatch files were not read.

## Author packet (read-only)

- Read in full: `README.md`, `scope-freeze.md`, `proof.md`,
  `operation-comparison.md`, `hostile-checks.md`, `reading-limits.md`,
  `upstream-provenance.json`, and `verify.py`.
- `primary-provenance.json` and `manifest.json`: the displayed portions were
  read, and the middle portions were skipped by the display. I used them for
  integrity only. Both are bound by hash.
- `integrity-controls.json` and `seal.sha256`: hashed. The seal was displayed;
  the controls file was not read. These are author receipts and are not
  adopted.
- Ran the author's read-only `verify.py` with the detached manifest digest. It
  passed with 34 payloads, 26 external anchors, 13 pinned blobs, and 4 primary
  PDFs. The run created no files: the file count stayed at 36 and no
  `__pycache__` appeared (`python3 -B`).

## Source333 (retained private copies in the author packet)

I independently recomputed Git blob SHA-1 values and compared them with the
complete tree. All 12 build files match.

Read in full: `introduction.tex`, `global-construction.tex`,
`primitive-statement.tex`, `velocity-loop.tex`, `primitive-realization.tex`,
`geometry-preservation.tex`, and `preliminaries.tex`.

Read partly:
- `exact-correction.tex`, lines 1–60: the introduction and the complete
  statement of `prop:exact-correction`, plus the start of the smoothing lemma.
  The rest of the proof is unread. Only the statement's C² o(1) conclusion is
  used.
- `small-modes.tex`, lines 20–119: weighted norms, the complete statement of
  `prop:small-increment`, and the start of its proof. The rest is unread and
  not used.
- A label grep was run over `exact-correction.tex`, `small-modes.tex`, and
  `preliminaries.tex`.

Not read in this round: `main.tex`, `refs.bib`, and `figure-geometry.tex`
(hashed only). Upstream `README.md` and `paper.pdf` were not acquired.

## Source334

The retained `companion334-main.tex` matches the pinned blob of
`preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/build/main.tex`.
All 228 lines were read. No line exceeds 200 characters, so the
character-limited display did not truncate anything. Its section files were not
acquired or read.

## Family333 chains

Read in full: `fresh-parent-discovery-r5/screen.md` (33 lines),
`fresh-analytic-discovery-r17/source-reading.md` (113 lines), and
`fresh-structural-discovery-r92/screening.md` (19 lines). Other files in those
directories were listed but not read. No systematic search of all historical
campaign files was made in this round. The comparison rests on these bodies and
on the author's own disclosed search, which I did not re-run.

## r1 drafts

Read in full as prior findings, not as authority: `review.md`,
`paid-unpaid-comparison.md`, `reading-limits.md`, and `README.md`. I did not
read or run `author-baseline.json` or `verify.py`, and I did not inspect r1's
`private/` subtree beyond a directory listing. r1 has no manifest, seal,
`checks.json`, or `integrity-controls.json`, so its claims about those files are
not completed checks. All six public r1 files are anchored by hash in this
review's manifest as context.

## Primary bodies (retained private extracted text in the author packet)

The line numbers refer to the author's retained `pdftotext -layout` text. Its
SHA256 is bound by the author manifest and replayed. I did not re-extract text
from the PDFs or view the rendered PNG pages, and I did not re-download
anything. The text is the author's extraction, verified by hash only.

- De Lellis–Inauen–Székelyhidi 2018 (`dlis2018.txt`): lines 37–138 (Theorems
  1.1 and 1.2 with surrounding introduction), 1060–1194 (Step 1 construction
  (8.1) and the complete Remark 8.1), and 1310–1389 (Corollary 9.1 and the
  complete proof of Theorem 1.2 for embeddings). The rest is unread.
- Cao–Székelyhidi 2306.12879v1 (`cao-szekelyhidi2023v1.txt`): lines 1–150
  (abstract, introduction, Theorem 1.1, strategy) and 470–794 (Lemmas 3.1–3.2,
  Proposition 3.3 and its complete proof, including the p. 14 embedding
  sentence, plus the opening of Section 3.2). The rest is unread.
- Le Donne 1005.1623v2 (`ledonne2016v2.txt`): lines 227–421 (all of Section 3:
  Theorems 3.1 and 3.2, Lemma 3.5, the construction, path-isometry, and the
  embedding proof). Lemma 3.5's referenced proof (Federer) was not read.
- Gromov 2015 (`gromov2015.txt`): not read in this round. It is not used.

Not read, and given no operation credit: Nash 1954 and 1956, Kuiper 1955,
Whitney 1944, Poznyak, Gromov PDR, Federer, the primary for the classification
and handlebody embedding of surfaces, and textbook tubular-neighborhood
theorems. Every elementary step the verdict relies on is proved in `proof.md`
or `review.md`.

## Retrievals and failures

No network retrieval was attempted. There were no unsuccessful retrievals. One
local command failed because `numpy` is not installed; `checks.py` was then
written in pure Python. This is a tool limit, not mathematical evidence.
A first manifest-building shell command was malformed: a stray heredoc
consumed the program, so it executed nothing. `ls` and `git status`
confirmed that it wrote no file. The manifest was then built by a correct
invocation.

Two integrity-control runs were discarded:

- The first sent its receipt to the temporary file `/tmp/null-not-used`, outside
  the owned directory. That run reported all controls as expected. I read the
  file's opening lines and deleted it at once. It contained only the
  verifier-control receipt; no repository file was affected.
- The second run let the receipt file appear inside the bundle while copies
  were being made. The copies then failed membership checks for the wrong
  reason. I fixed the control script so that it copies exactly the sealed
  members, deleted the faulty receipt, resealed, and reran.

The stored receipt comes from that corrected third run. No
browser UI, upload, contact, nested agent, staging, or commit was used.

## Rights and copies

This directory contains no third-party copies. Third-party evidence was read
in place from the author's `private/` subtree and is anchored by hash only.
All prose and code here are original to this review.

## What the integrity material does and does not certify

`manifest.json` and `verify.py` bind this review's bytes, the 36 author files,
context files, and the retained evidence by SHA256. They also re-check the 13
pinned blobs against the complete tree. They do not certify mathematical truth,
priority, semantic completeness, or contribution. Trust requires the detached
manifest digest from the parent-facing handoff, not the neighboring
`seal.sha256`.
