# Reading, search and check limits (RCS128 contribution review, round 2)

Original prose CC BY 4.0, original code MIT. Third-party bytes retrieved in this round are only under `private/`, with `private/PROVENANCE.json`. They must be excluded from git and from any public release. The comparison bodies supplied by the parent stay in the frozen input packet. They are not copied here.

## Read directly, in full

- `AGENTS.md`.
- The round-2 dispatch text and the ORIGINAL BRIEF, which were supplied in the dispatch.
- The input packet:
  - `verify.py` (read before running it), `provenance.json`, `parent-response.json` and `proof-findings.txt`;
  - `comparison-r4/reading-checkpoint.json`, `open-findings.json`, `access-followup.json` and `retrieval.json`;
  - `prior-contribution-review.md` and `prior-contribution-reading-limits.md`, which are also given verbatim in the dispatch and are byte-identical to the r1 files.
- Author r37:
  - `original-scope.txt` and `candidate.md` (all of it);
  - `contribution-and-limits.md`, `self-text-rule-and-host.md`, `folded-threshold.md` and `budget-counterexample.md`.
- Pinned source family128 (private copies in the author packet):
  - `02-counts.tex` and `05-processing.tex`, in full;
  - the `lem:host` statement and proof in `04-connections.tex`;
  - the lemma label inventory of 03, 04 and 06.

## Read only in part

- **Pinned source family128.** Sections 01, 03, 06 and 07 and the rest of 04 were *not* reread this round. I rely on round 1's full reading and on the stipulation.

## Primary bodies, read directly this round (partial, exact ranges)

All of these are in the input packet's `comparison-r4/private/`.

- **Goldberg–Karzanov, arXiv math/0304290** (PDF `11e46d81…`, text `090a64ed…`):
  - extraction lines 60–330: introduction, §2 definitions, "no self-symmetric paths or cycles", regular paths and barriers;
  - lines 495–520: the end of the Theorem 3.1 decomposition proof and Corollary 3.2 (Tutte parity);
  - lines 690–800: the end of §4 and all of §5, including the two-self-symmetric-cycle splice on pp. 15–16, and the start of §6.

  Not read by me: the rest of §3, §4, and §§6–10. The journal-version PDF (`goldberg-karzanov2004.pdf`) is corrupt and unread.
- **Yamano–Shibuya CPM 2026** (`ys-cpm2026.txt`):
  - lines 70–100: the introduction and the description of Jiang et al. [8];
  - lines 225–262: §2.1, the greedy algorithms;
  - lines 460–530: Lemma 18 and its proof;
  - a keyword grep of the whole file.

  Not read in full by me. The parent reports a whole-file reading.
- **Medvedev et al. 2007:** lines 180–240 (§2.2 bidirected-graph definitions) and a keyword grep. Lemma 1 (balanced connected Euler) is taken from the parent's checkpoint and was not read by me.
- **Collapsing framework (arXiv 1809.08669, v3):** lines 940–975 (§7.2 in full).
- **Breslauer–Jiang–Jiang 1996 BRICS report:** a keyword grep only (the Lemma 3.3 location). The parent reports a full reading.
- **Kundeti 2010 and Mucha 2013:** a keyword grep only. There are no hits for palindrome, self-complement, reverse complement or parity.

Keyword grep is weak evidence, because extraction may break words. For these partially read bodies I rely on the parent's reading checkpoint *only* to place antecedents for components to which I give zero credit. No credited item depends on the content of a body I did not read. The credit judgment depends only on the *absence*, in the read antecedents, of a reflection forced-count surplus, a phase-specific sorted parity and an odd-core threshold. For bodies read only partially, that absence is bounded by the read ranges and the parent's checkpoint, and is not established beyond them.

## New retrieval this round (bounded)

- **Jiang–Li–Du 1992, IPL 44(4):195–199, DOI 10.1016/0020-0190(92)90084-9.**
  - An extended web search (one query) found citations only.
  - `https://www.sciencedirect.com/science/article/pii/0020019092900849` returned HTTP 403.
  - **The body is NOT read.** This is not evidence of absence.
- **Secondary description, Fici–Kociumaka–Radoszewski–Rytter–Waleń, arXiv 1511.08431.** The PDF (SHA `82bc7333…`) was fetched and stored in `private/fici2015/`. Extraction lines 30–110 and the reference list (lines 540–575) were read via grep context. Lines 36–37 and 101–103 describe JLD as a greedy-like 4-approximation with an unproved NP-hardness remark.
- **Breslauer–Jiang–Jiang 1997 journal version.**
  - A web search found only the BRICS and MPI report pages.
  - **The journal body is NOT read.** Its equivalence to the report is not established.

The query log is in `retrieval-r2.json`.

## Not read

- `rcs128-proof-r1/`, the separate proof gate. Its `MANIFEST.json` was *hashed only*, giving `50bf7355…`.
- Formal-review directories, Lean files, and the r37 code and JSON certificates. I did not rerun the author replay. Author bytes were checked by direct sha256 of the four anchored files only.
- Y–S WABI 2026. It was not reread this round; round 1 read the whole extraction.
- Kececioglu 1991 and the skew-symmetric literature beyond GK.

## Searches

There was no new campaign-history search. Round 1's `history-search.json` remains the bounded history screen. The literature search is bounded (see `retrieval-r2.json`). It gives no priority certificate.

## Checks run

- **Input packet verifier:**
  - the correct anchor gives PASS, 37 files and 2 directories;
  - an all-zero anchor gives REJECT;
  - a tampered copy, made outside the repository, gives REJECT.

  See `controls.json`.
- **`w_obstruction.py`:** reviewer-written, using no author or round-1 imports, runtime under 1 s. It gives W_naive=6, W_2k+1=12 and OPT_RC=7, with OPT_RC by exhaustive search. The result is in `w-obstruction.json`. This is diagnostic only.
- **This packet's own `verify.py`:** run with positive, wrong-anchor and tamper controls on copies (`controls.json`).
- No Lean code was run, and no formal claim is made.
