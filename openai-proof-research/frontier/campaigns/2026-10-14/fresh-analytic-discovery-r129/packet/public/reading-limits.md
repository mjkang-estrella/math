# Reading limits and evidence

## Read in full
- AGENTS.md and the full r129 brief (`expanded-target-2026-10-17/fresh-analytic-r129-brief.txt`). Copies are in private/context.
- The required r128 files: `fresh-analytic-discovery-r128/REPORT.md`, `packet/public/report.md`, `screens.md`, `reading-limits.md`, and `discovery-analytic-r128-parent/intake.json`. Copies are in private/history.

## Pinned upstream
Each file was fetched from its pinned raw URL and authenticated against the complete 13223-entry preprint tree by Git blob SHA. The register is `private/upstream/canonical-register.json`, which records each file's read extent.

Retained (11 files):
- source090 universal optimality:
  - Read in full: `02-cardinal-fourier.tex`, `04-exact-interpolation.tex`, `06-gaussian-energy-transfer.tex`.
  - `01-uniform-gaussian-theorem.tex`: lines 1–170 in full; the remainder was partially displayed.
  - `03-quadrature-finite-data.tex`: lines 250–389 only (q(k), E(k), finite columns, parameter boxes).
  - `05-global-signs.tex`: lines 1–30, plus the line that starts the proof of `thm:normalized-pair`.
  - `main.tex`: a truncated display, used for section order only.
- Atomic companion `main.tex`: lines 120–509 only (history, proof overview, energy section).
- source191 Heilbronn:
  - `01-introduction.tex` in full.
  - Lemma and proposition statements with about 12 lines of context: `aux:cap`, `aux:random-set` and `aux:weights` in `05-auxiliary-cap.tex`; `zero:weighted-zero`, `zero:plane` and `zero:moment` in `07-zero-determinants.tex`.

Acquired, authenticated, then removed unread (retained=false), 11 files:
- source090: `macros.tex`, `07-shifted-mixtures.tex` (label outline only), `08-arithmetic-verification.tex`, `09-conditional-floor-verification.tex` (label outline only).
- source191: `main.tex`, and sections 02, 03, 04, 06, 08 and 09.

Operative statements used in S3 come from fully read text:
- Proposition `prop:exact-interpolation` and its list bound <5, in section 04.
- `eq:uniform-derivative-bounds`, `lem:cardinal-measure` and `lem:kernel-bounds`, in section 02.
- `lem:gaussian-duality` and `prop:density-lp`, in section 06.
- The opening sentence of section 05, which ties the sign proof to the exact lists.

The Section 05 sign certificates, the Section 03 quadrature and finite certificate, and the Section 07 mixture lemma were not reread. They are stipulated.

## History
Copies are in private/history, with extents recorded in `register.json`.
- Read in full: r56 scope-status and singular-strata-attempt, and r57 checkpoint and scope-status.
- Read in part: the r56 checkpoint (first 1200 bytes plus line 5), r57 full-strata-interface (grep lines only), the structural r24 candidate (first 2000 bytes), and I134/I137 (grep lines for source090 only).
- The r56/r57 and r24 reads came after the alias search, which itself came after my own S3 resolution and the source191 cap-count calculation. All of this preceded sealing, and no freeze ever occurred.
- Also seen: navigation-level grep hits in r54 (circle energy; unrelated) and the r115 history-090 file (no hits). These were not copied.

## Primary literature
I fetched no external primary. Cohn–Kumar (Proposition 9.3, Conjecture 9.4), CKMRV, Cohn–Miller, Sardari and Van de Voorde–Voloch appear only as cited by the pinned sources or by the r56 note. Their bodies were not read. Bernstein's theorem and Fubini/Tonelli are classical background. The admissibility class is stated as the companion describes it. I make no novelty or priority claim.

## Searches
`search-receipts.json` records 10 full-content alias searches over frontier, proposals, notes, reviews, experiments and findings, run with `--no-ignore --hidden` and no size cutoff. A post-filter drops this root, the two active rounds, and private, context, input, snapshot, upstream, catalogue and tree copies. Raw and kept counts are both recorded. Receipts are navigation only, not semantic reads or clearance. The `list-bound-exact-interpolation` pattern matched mostly path inventories. The `heilbronn` hits led to r56/r57 and r24, which I read. The other hits were not followed beyond their paths, except the r128 files already read.
