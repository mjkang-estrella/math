# Reading limits: T298P contribution review r2

"Read" means that I saw the text myself in this round. Where a tool display elided lines, the elided lines count as not read and are listed. Hash-only means that the file was authenticated but its content was not read.

## Not opened (independence)

- Any `t298p-proof*` path. The proof review r1 is still running.
- `t298p-parent/proof-r1-brief.txt`, `dispatch-r1.json`, `intake.json`, `reading-and-interface-intake.json` and `contribution-r1-brief.txt`.

Opened from `t298p-parent/`:

- `contribution-r2-brief.txt` (my brief);
- `contribution-r2-dispatch.json`;
- `contribution-r1-failure.json` (round-1 failure record and parent-captured round-1 hashes; it contains no verdict beyond the draft summary already in my brief).

## Author packet `fresh-structural-discovery-r104`

Authenticated by the anchored author verifier (PASS) and by sha256sum against the dispatched anchors.

**Read in full:**

- candidate.md
- comparison.md
- stress-checks.md
- matched-volume-attempt.md (A–G)
- unconditional-score-construction.md (1–5)
- normal-slice-construction.md
- finite-entropy-chart.md
- encoding-attempt.md (1–5)
- scope-freeze.md
- scope-status.json
- MANIFEST.json
- reading-limits.json
- verify.py (read before execution)

**Hash-only, not read:**

- coarse-diagnostics.py and .json
- volume-normalization-diagnostics.py and .json
- primary-receipts.json and source-receipts.json (consumed by the author verifier)
- progress.json
- reproduction.md

The parent reports reproducing the diagnostics. My checks K1–K4 are written independently.

## Round-1 draft `t298p-contribution-r1` (unsealed; prior findings only)

- **Read in full:** review.md, reading-limits.md, checks.json.
- **Hash-only, not read or executed:** contribution-checks.py and .json, verify.py.

All six files match the parent-captured hashes, and I left them unchanged.

## Pinned source bodies (private copies, git blobs verified by the author verifier)

**Source298** (*A finite-entropy separation…*, Sept 25 2026):

- **Read:**
  - `paper.tex` lines 25–40 (abstract);
  - `01-introduction.tex` lines 1–~35 and 46–60 (Theorem `thm:main` and the sentence "does not address equality for every smaller prescribed number of variables");
  - `04-signal.tex` lines 1–44 (construction of C, V_a and the matrix models) and visible parts of lines 95–175 (`eq:freeflow` vicinity, `eq:smallblocks`, `lem:finitechi` proof end);
  - grep hits for labels `eq:chistar`, `eq:gue-norm-tail`, `eq:freeflow`, `lem:flow`.
- **Not read:** the elided introduction lines (~35–45 and the remainder after line 60), 02-conventions (except grep), 03-fisher, 05-flow and 06-blocks bodies.

The source is stipulated, and I used it only as a black box together with its stated limitation.

**Companion287** (*An isomorphism of the free group factors*):

- **Read:** README head; statements of `thm:rank-step` and `thm:main` (main.tex); the statement opening of `cor:entropy-dimensions`; `cor:all-interpolated`.
- **Not read:** all other text, including proofs.

The round-1 draft read entropy-dimensions.tex and amplification.tex in full. I rely only on the statements above.

**Relative generation and the generator problem for finite factors** (Sept 23 2026):

- Scratch copies in `/var/tmp/t298p-c1-gen-src` were fetched by round 1. I independently matched all three git-blob SHA-1 values against `sources/preprints-tree.json` before relying on them:
  - README.md `28a01c27…`
  - introduction.tex `02f9577d…`
  - consequences.tex `1a644264…`
- **Read:** introduction.tex, including `thm:relative-generation`, `thm:main`, the proof outline and the 2×2 encoding citation (DSSW Prop. 1.1, Douglas–Pearcy/Wogen); consequences.tex, including `cor:entropy-generators` and its proof.
- **Not read:** short tool-elided spans (~11, ~16 and ~2 lines); generation.tex, independence.tex, perturbation.tex, main.tex, preamble.tex, references.bib and paper.pdf.

## External primary bodies (private, receipt-matched by the author verifier)

- **Shlyakhtenko math/9812079v1** (`shlyakhtenko-relative.txt`):
  - Read lines 1–370 and 400–764: Definitions 2.1–2.3 and 2.10; Remarks 2.4 and 2.11; Propositions 2.5–2.18 (2.8, 2.12, 2.13, 2.14); Theorems 2.15, 2.17 and 2.19 with proof; Corollary 2.20; Theorem 3.1 (statement); Proposition 3.2; all of §4 (Theorem 4.1 statement, whose proof is omitted in the source; Proposition 4.2 with proof; Theorems 4.3–4.6); all of §5 (Theorem 5.1 with proof).
  - Not read: lines 371–399, the middle of the proof of Theorem 3.1.
- **Nica–Shlyakhtenko–Speicher math/9809081v1** (`nica-shlyakhtenko-speicher.txt`): all 645 lines.
- **Nica–Shlyakhtenko–Speicher math/9809080v1** (`nica-fisher.txt`):
  - Read lines 1180–1379: Proposition 4.1 with proof, (4.4)–(4.5), and the start of the proof of Theorem 1.3.
  - Not read: lines 1–1179 and 1380–1770, including Remark 2.6. Remark 2.6 is used only as quoted at lines 1216–1219.

## Literature screen (bounded; snippets are not theorem evidence)

- **WebSearch, two queries (Oct 2026):**
  - two-variable finite χ<χ* in 2026;
  - matrix amplification and unconditional orbit volume.
- **Abstract page read:** arXiv 2610.06741 (Oct 2026, free entropy and quantum MDL; not relevant).
- **Top-level description only:** jnshi/math-lineage PR #10. It is a third-party precedence review of source298, and its review file was not read. It concerns the source's precedence, not a two-variable reduction.
- **Snippets/titles only:** 1210.6421, 1610.04118, 1306.5372, math/0605633.
- **Not read as bodies:**
  - Jung math/0410594;
  - Shlyakhtenko 2201.09503;
  - Hiai–Miyamoto–Ueda math/0702745;
  - Connes–Shlyakhtenko;
  - NSS R-cyclic matrices;
  - Biane–Capitaine–Guionnet;
  - Jekel–Pi;
  - DSSW.

No two-variable finite gap was found, and no unconditional finite-part matrix-amplification formula for χ or χ*. Absence is not clearance, and no worldwide priority claim is made.

## Campaign history

- **frontier/NEW-TEN-2026-10-14.md:**
  - Read lines 1–60.
  - Grepped for T298P, source/family 298, r104, free entropy, microstates, χ*, Shlyakhtenko, normal slice, gauge orbit and matrix units. The only hit is line 803, the analytic-r20 family-298 screen.
  - Grepped for SUBSTANTIAL/TECHNICAL to check classification usage.
  - All other lines were not read.
- **frontier/RESULTS.md:** does not exist.
- **TWENTY-FINDINGS.md, TEN-FINDINGS.md, OUTCOME.md, README.md:** grepped. The only hit is TWENTY-FINDINGS line 35 (an unrelated "I298" Gaussian-stability iteration).
- **frontier/iterations (887 entries):** grepped for microstates, nonmicrostates, free Fisher, Voiculescu and free entropy. No hits.
- **campaigns/2026-10-14:**
  - Grepped (excluding private/inputs, r104, t298p-*) for free entropy, microstates, nonmicrostates, free Fisher, Voiculescu and Shlyakhtenko, and for matrix unit, normal slice, gauge, two generators and two self-adjoint.
  - Every substantive hit was checked. `fresh-analytic-discovery-r20/entropy-obstruction.md` was read in part (grep context and lines 9–53 summaries). It concerns noise persistence and terminal maximality, with no variable reduction.
  - The remaining hits are catalogue/index listings (r31, r39, r64, r73, source-navigation, cm275) or unrelated uses of "matrix units"/"gauge".

## Author-side attribution packet

`t298p-attribution-r1` is not an independent gate, and I did not rely on it. Its state at the time of observation is recorded in checks.json. I did not read addendum.md, inputs.json, reading-limits.md, verify.py or private/. I read only its README.md and MANIFEST.json to record status. No external anchor was supplied, so it is **not authenticated**. Nothing in it changes this review, whose required items refer to the frozen r104 bytes.
