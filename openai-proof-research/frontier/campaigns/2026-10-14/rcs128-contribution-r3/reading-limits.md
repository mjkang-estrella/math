# Reading, search and check limits (RCS128 contribution review, recovery round 3)

Original prose CC BY 4.0, original code MIT. No third-party bodies are stored in this directory, and none were downloaded this round. Fetched web pages were read in the session only. Their content is summarized in my own words, with at most one short quoted phrase per source, for identification. The third-party bodies I read are private copies in the frozen input packet (`rcs128-contribution-inputs-r2/comparison-r4/private/`) and the author packet (`fresh-structural-discovery-r37/private/`), under their own provenance. Both are excluded from public releases.

## Read directly this round

- `AGENTS.md`.
- The full round-3 brief, including the round-2 brief, the original brief, the round-1 findings and limits, and the exact parent response, as supplied.
- Input packet:
  - `verify.py` (before execution);
  - `provenance.json` and `proof-findings.txt`;
  - `comparison-r4/reading-checkpoint.json` (all fields, untruncated);
  - `open-findings.json`, `access-followup.json` and the `retrieval.json` excerpt.
- Author r37:
  - `candidate.md` (all of §§1–7 and status);
  - `contribution-and-limits.md` and `original-scope.txt`;
  - `folded-threshold.md`;
  - `verify.py` and `checks.py` (including the write guard in `check-new-interfaces.py`).
- Source family128 `05-processing.tex`, in full (the author's private pinned copy).
- Goldberg–Karzanov arXiv extraction, lines 176–215, 470–529 and 710–784. These cover the §2 definitions and the no-self-symmetric-path argument, Theorem 3.1 with its proof, Corollary 3.2, and §5 in full, including the splice at lines 746–749.
- Yamano–Shibuya CPM 2026 extraction, lines 60–119 (introduction, Jiang et al. description, contributions), 232–236 (§2.1), 295–303 (Lemma 11) and 472–480 (Lemma 18 statement and opening).
- Yamano–Shibuya WABI 2026 extraction: keyword hits only (lines 73–77, 144–146 and references 685–705). Round 1 and the parent read it in full; I did not reread it in full.
- Keyword screens (reverse, complement, palindrome, involution, skew, odd, parity) of these extractions:
  - BJJ 1996;
  - Mucha 2013;
  - Collapsing;
  - Medvedev 2007;
  - Kundeti 2010;
  - CPM 2026.

## Relied on through the parent's recorded reading, not reread in full by me

- CPM 2026 (whole);
- Medvedev 2007 (with page limits);
- Kundeti 2010 (whole);
- GK §§3–4, apart from the lines above;
- BJJ 1996 report (whole);
- the MPI 1996 copy (opening only);
- Mucha 2013 (whole);
- Collapsing §7.2.

Source sections 02–04, 06 and 07: as stipulated and as read by round 1 and the parent. This round, I reread §05 only.

## Not read

- `rcs128-proof-r1/` (only its `MANIFEST.json` hash was computed) and the formal reviews.
- Any round-2 artifact. None exists: round 2 failed with a rate-limit error before writing.
- **Jiang–Li–Du 1992 body.** This round I saw only:
  - the publisher abstract page (HTTP 200: abstract and partial reference list; the full text is paywalled);
  - the arXiv 1511.08431 abstract page (Fici et al. 2015).

  No paid access, library request or author contact was attempted. Those are outward actions outside this role.
- **Breslauer–Jiang–Jiang 1997 journal body.** This round I saw only the MPG.PuRe journal record (no file) and search-result abstracts.
- Kececioglu 1991. Upstream Lean superstring files.
- The GK journal 2004 PDF (corrupt download, recorded by the parent).
- GK §§6–10.

## Searches this round

See `search-log.json`: five web searches and three page fetches. They are bounded. Absence of a hit is not evidence of absence. Campaign-history and upstream screens were not repeated; they are inherited from round 1 and the author packet with their recorded limits.

## Checks run

- **Input packet anchor.**
  - Positive: PASS.
  - All-zero and malformed anchors: REJECT.
  - Tamper on a `/tmp` copy: REJECT.
- **Author packet `--replay`.**
  - Positive: PASS.
  - Wrong anchor: FAIL.
  - No side effects (`git status` unchanged).
- **`opt_bruteforce.py`** (reviewer-written, no author imports, about 0.1 s, stdout only). It computes exhaustive OPT_RC: 7 for the identity-involution instance and 10 for the a↔b instance. It does **not** compute any W value.
- **This directory's seal.** See `verify.py`: `--controls` runs positive, wrong-anchor and tamper controls on temporary copies only.
- No Lean code was run. No formal or proof claim is made.
