# Reading limits: T117Q manuscript review, round 2

## Read completely

- Rules: AGENTS.md, VALIDATION.md, frontier/NEW-TEN-2026-10-14.md acceptance rules
  (including line 15), t117q-parent/manuscript-review-r2-brief.txt and
  t117q-parent/manuscript-v2-preflight.json.
- Round 1: t117q-manuscript-review-r1/review.md and reading-limits.md. Its verify_review.py
  and review_controls.py were read as format references only; this package's scripts are
  separate files written for round 2.
- The frozen v2 packet t117q-manuscript-v2/:
  - main.tex, all 1068 lines;
  - main.pdf, all 16 pages, rendered at 80 dpi and viewed one by one, plus a 200 dpi render
    of p.14;
  - README.md, reading-limits.md, editorial-crosswalk.md, LICENSES,
    validation/repair-receipt.json and validation/v1-to-v2.patch;
  - packaging and input provenance records;
  - build.py, verify.py and integrity_controls.py, read before running.
- Prior completed reports (byte-identical to the copies under the packet's inputs/):
  - fresh-structural-discovery-r59/original-scope.txt;
  - t117q-proof-r1/review.md;
  - t117q-contribution-r1/review.md;
  - t117q-contribution-r2/review.md;
  - t117q-formal-review-r1/review.md;
  - t117q-parent-literature-r1/response.md.

## Read in part

- t117q-manuscript-v1/main.tex: read through the diff with v2 and by grep (to confirm that
  v1 never mentions GMN Question 3). v1 was read in full in round 1, not again here.
- Formal packet t117q-formal-v1: rebuild.py argparse options only (lines 26–28). The Lean
  development was not rebuilt. Formal coverage relies on formal-review-r1 and on §9 of the
  manuscript matching it.
- Pinned source (copied blobs, Git blob ids rechecked against sources/preprints-tree.json):
  kernel.tex and repair.tex for the formulas reused in §5, and label lookups for the 17
  Appendix A labels. Source truth is stipulated and was not audited.

## Primary texts (local extractions, SHA256 in evidence.json)

These are the passages I read myself:

- **GMN 1003.0279v3:** §1.3 in full (lines 377–505), including Theorem 1.2 and Question 3,
  and bibliography lines 1753–1791 (entries [3] Bourgain and [18] Tomczak-Jaegermann).
- **JLW 2610.21445v1:** lines 1–260 (abstract, introduction, Theorem 1.3 and the GMN
  Question 3 discussion), (4.5), Proposition 5.2, Steps II–III, and Corollary 6.1 with its
  proof (lines 1075–1149).
- **MN math/0506201:** Theorem 1.12 statement (line 422) and proof (lines 3005–3062), and
  Lemma 6.12 with proof (lines 2773–2790).
- **CEE 2010.11583v3:** Theorem 13 statement and proof (122)–(125), Theorem 42 statement,
  and lines 503–512.
- **LWW 2610.03407v1:** Theorem 1.1 (lines 11, 67, 78–88).
- **KNT 2105.04712v1:** Theorem 34 (lines 1642–1646).
- **Naor–Young:** lines 590–634, including Question 13.
- **NPS:** the header and lines 280–339.
- **EGM:** Section 3.2 and Question 2 (lines 221–231).

I did NOT read:

- the Bourgain (1987) or Tomczak-Jaegermann (1974) originals. The M1 closure relies on GMN
  §1.3's explicit statement of their results, and the manuscript discloses the same limit.
- the full JLW mixing-smoothing proof, or the full MN and GMN cotype proofs.
- Haagerup–Pisier, Buchholz, Seymour–Zaslavsky or Pisier (1986). The manuscript proves the
  needed forms itself.
- the published versions of GMN, CEE or NPS (see O3).
- any release preparation (t117q-release, t117q-release-v2). They have no bearing on this
  verdict.

No new literature search, forward-citation search or bibliographic verification of
published versions was performed. Novelty is not assessed beyond checking that the
manuscript's wording stays within the bounded-search qualification.

## Replays (identity and build only)

- The author verify.py was run with the external anchor (accepted, exit 0) and with an
  all-zero anchor (rejected, exit 1).
- The author integrity_controls.py was run on a /var/tmp copy: 15 cases, each reason
  checked.
- The recorded v1-to-v2.patch was applied with `git apply` to a copy of v1 and reproduced
  v2 main.tex exactly. (`patch` is not installed on this host.)
- The copied packet was rebuilt with Tectonic 0.17.0. The PDF and the pdftotext output are
  byte-identical to the packet's, pdffonts shows 24 fonts all embedded, and the log is
  clean.
- The command printed on p.14 was run, as printed, on the /var/tmp packet copy. It failed
  with argparse exit 2 and wrote nothing (R1).
- The canonical packet was never used as scratch.

None of these is mathematical evidence. The mathematical verdict rests on reading the
proof.

## Mutable context

frontier/NEW-TEN-2026-10-14.md is a shared ledger that changed during this review
(new parent commits). Its hash in evidence.json is the value at seal time and is context
only, not a frozen anchor. Line 15 still states the rule used here: an accepted result needs
reproducibility instructions and a precise formalization coverage statement.

## Scratch

/var/tmp/t117q-msrev-r2/ holds the packet copy, the patch check, the rebuild, the page
renders, the p.14 zoom and the author-control output. /var/tmp/t117q-msrev-r2-controls/
holds the review-control copies. These directories are not package members.
