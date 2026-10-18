# Reading, search and check limits (RCS128 contribution review, round 1)

Original prose CC BY 4.0, original code MIT. No third-party bodies are copied into this directory. Source and primary bytes remain private in the author packet, under their own provenance.

## Read directly, in full

- `AGENTS.md` and `sources/upstream.json` (pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`).
- The parent brief, `rcs128-parent/contribution-review-brief.txt`, together with `progress.json` and `contribution-dispatch.json`.
- Author r37 prose:
  - README;
  - `original-scope.txt` and `checkpoint.md`;
  - `candidate.md` (all of §§1–7 and status);
  - `contribution-and-limits.md`;
  - `self-text-rule-and-host.md` and `quotient-cycles.md`;
  - `counts-and-euler.md` and `budget-counterexample.md`;
  - `strengthened-fixed-rule.md`, `folded-threshold.md` and `connection-interface.md`.
- Author r37 code: `verify.py`, `checks.py`, `check-new-interfaces.py`, `explore.py` and `search-budget.py`.
- Author r37 receipts: the source, primary, context and parent-support receipts.
- JSON certificates: not read line by line. The replay checks them, and `independent_checks.py` independently recomputes the W6/OPT7 certificate.
- r36: `superstring128.md` and `reading-limits.md`, in full.
- Pinned source family128: `README.md` and `build/sections/01-introduction.tex` through `07-algorithm.tex`, in full. These are the private copies in the author packet; the author verifier binds them to Git blob IDs in the complete tree. Also read: the bibitem titles in `references.tex`. Not read: figures, beyond their captions in the sections, and `paper.tex`.
- Yamano–Shibuya WABI 2026 extraction, `yamano-shibuya-wabi2026.pdf.txt`, lines 1–739 (the whole extraction). This covers:
  - abstract and §§1–2;
  - §3, Lemmas 6–10;
  - §4: Theorem 11, Algorithm 1, the gadget, Lemma 12 and Theorem 13;
  - §5: Theorems 2 and 3, including the §5.2 encoding;
  - §6 and the references.

  The extraction mangles fraction typography ("38" for 8/3); the meaning is clear from context. PDF identity was checked by SHA256 `757b3e81…`, matching the receipt. I did not fetch the publisher's page afresh, but the arXiv abstract page (v1 2026-03-27, v2 2026-05-29, journal reference WABI 2026) was fetched.

## Not read

- `rcs128-proof-r1/` (the separate proof gate). Only its file names appeared in a grep listing.
- Upstream Lean superstring files and `lean/docs/128.md`.
- The full bodies of the following, which are required before any manuscript (finding R4):
  - Yamano–Shibuya CPM 2026;
  - Jiang–Li–Du 1992;
  - Kececioglu 1991;
  - Medvedev et al. 2007;
  - Kundeti et al. 2010;
  - skew-symmetric graph references;
  - Breslauer–Jiang–Jiang;
  - Mucha;
  - the Collapsing framework.
- The Fici et al. 2015 body. Only its abstract page was fetched.

## Searches

- **Campaign history:** `history-search.json`. This was a bounded regex over proposals, findings, reviews, notes, iterations, campaigns, experiments, output and the frontier reports. Its exclusions are listed in that file. It is not an exhaustive semantic clearance.
- **Catalogue and tree:** the complete nontruncated `preprints-tree.json` (13,223 entries; byte-identical to `sources/`) and `CONTENTS.md` were searched for superstring, reverse-complement, DNA, cycle-cover and hierarchical-graph terms. The only hit is family128.
- **Literature:** `literature-search.json`, five web queries and three page fetches. Bounded. It gives no priority certificate.
- **Upstream (read-only GitHub API):** the commits after the pin are PR-lock commits only. Code search finds nothing for "reverse complement".

## Checks run

- **Author verifier:** positive with replay passes; two wrong anchors fail (`author-identity-replay.json`).
- **`independent_checks.py`:** reviewer-written, using no author imports, about 1.2 s. It writes nothing except to stdout. It recomputes:
  1. the W_naive = 6, OPT_RC = 7 template obstruction, with OPT_RC by exhaustive word search, and W_selftext = 12;
  2. the r36 orientation table restricted to minimum-cost orientations;
  3. a seeded probe of the composite route over 400 instances, finding one instance where an arbitrary minimum constrained cycle-cover orientation has W > OPT_RC. That instance was cross-checked by brute force over all 3¹⁰ words.

  These checks are finite and are not proofs.
- No Lean code was run and no formalization is claimed.
