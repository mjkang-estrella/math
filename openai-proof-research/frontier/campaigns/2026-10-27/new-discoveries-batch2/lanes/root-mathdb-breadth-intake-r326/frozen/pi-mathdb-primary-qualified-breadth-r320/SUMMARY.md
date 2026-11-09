# r320 — MathDB primary-qualified breadth screen (50 reserved IDs)

Lane: `lanes/pi-mathdb-primary-qualified-breadth-r320`
Delegate role: solo breadth researcher; root only orchestrates. No child agents, no git,
no shared-ledger/index edits, no MathDB network requests (429 hold respected — zero
requests to mathdb.com from this lane), no browser tabs.

## What was done

1. **Frozen before reading.** `scripts/freeze_inputs.py` copied and SHA-256-bound all
   inputs before any substantive read: r318 `reserved-ids.json`, `queue.json`,
   `BRIEF.md`; r316 `coverage-delta.json`; r304 `accepted-exclusions.json`,
   `historical-dispositions.json`, `README.md`; r319 `intake.json`; and all 20
   `mathdb-normalized-chunk-*.jsonl` corpus files, each verified against r301's own
   manifest hashes (`bindings.json`, 28 entries).
2. **Full cached statements read for all 50 IDs** (no duplicates, none missing;
   `work/reserved-statements.txt`). This is a record-statement screen: it adds zero
   complete primary-body reviews and zero whole-corpus coverage claims.
3. **Prior-art comparisons** against r304/r316/r319 material (no keyword-level topic
   collision with the 133 screened IDs or accepted exclusions; those files are frozen in
   `frozen/` for root inspection) and against public literature via lawful web search.
   Public status was *not* claimed from name greps; refutations/resolutions below are
   tied to exact arXiv records.
4. **Primary bodies retained** for the four decision-relevant IDs (arXiv HTML + abs
   pages, downloaded 2026-10-30T23:46:16Z, hashed in `manifest.json`):
   347483 (Berlow, 2008.01164v2), 338062 (Chang–Ji–Li–Zhang, 1712.10010v2),
   327474 (Cherniavsky–Goldstein–Levit–Shwartz, 1403.3868v2),
   346000 (Potechin–Tsang conjecture, 2003.13166 + refuting 2004.01327), plus
   400943 resolution (1703.05253).
5. **Decisive calculations executed** under the pinned helper guard
   (512 MiB AS/group-RSS, 210 CPU s / 230 wall, single-thread BLAS/OMP):
   - `scripts/decisive.py` → `work/decisive-results.json`
   - `scripts/decisive_trees.py` → `work/decisive-trees.json`
   Details under Achieved coverage.

## Headline dispositions (all 50 in `dispositions.json`)

- **3 rows qualified as single-hypothesis briefs** (`proposals.json`, max 3):
  - **347483** — Berlow Conjecture 5.1: only periodic points of `s_{132,213}`,
    `s_{231,213}` are id and reverse. Verified here for n ≤ 8 by validated exact
    simulation; refutation certificate would be one permutation.
  - **338062** — Chang–Ji–Li–Zhang Conjecture 3.6: D(T) < 2·cfc(T) for every tree.
    Verified here: zero counterexamples among all 94 unlabeled trees n ≤ 9.
  - **327474** — Conjecture 6.3 (arXiv:1403.3868v2): equal Pr^{2n} for all n force
    equal |G/Z|. Pilot scan of 11 groups (orders 8–32, n ≤ 3) found no cheap
    refutation; full scan needs a small-group library (GAP absent here — flagged).
- **Publicly resolved/refuted, labels stale (kill on sight):**
  - 346000 — refuted by arXiv:2004.01327 (infinite family of Cayley graphs with an
    induced subgraph of max degree 1 on > half the vertices) and JCTB 2022
    (10.1016/j.jctb.2022.01.002).
  - 400943 — resolved by arXiv:1703.05253 / JCTA 173 (2020) 105236:
    h_5(n) = Ω(n log^{4/5} n), the exact conjectured bound.
  - 319090 — the cached statement itself records Hastings' disproof.
- **Solved inside their own source (labels stale):** 343278 (muffin 1/3, Cui et al.
  2018), 343374 (Lee proves the stronger exact formula).
- **Infeasible-computation targets:** 316133 (Sierpiński 78557 distributed search),
  399738 (prime-conductor completeness to 1e12).
- **Deep or infeasible programs parked: 30 rows** (see dispositions.json per-ID `why`
  fields), including near-duplicate flag 396644 ≈ 396642.
- **HOLD (12):** 315692, 318431, 320837, 329275, 329579, 331790, 332567, 340687, 349917,
  350216, 390106, plus 329978 (routine-adaptation risk) — plausible but lacking either a
  cheap decisive calculation, source-body access, or a post-2010 status check; not
  padded into the shortlist.

## Achieved coverage (precise)

- 50/50 reserved IDs: full cached statement read and dispositioned (metadata selection
  level; `statement_completeness=full` for all).
- 4 IDs: actual primary-body material read and retained (347483, 338062, 327474 full
  papers; 346000 conjecture body + refutation abstract; 400943 resolution abstract).
- Executed decisive calculations: 347483 periodic-point search S_n, n=3..8, both maps,
  implementation validated against the source's proved cases (exact set matches);
  338062 tree search n ≤ 9 (0 counterexamples; in this range D < 2Δ ≤ 2cfc always, so
  only larger n with small cfc can host counterexamples); 327474 pilot scan
  (11 groups, n ≤ 3; no counterexample; isoclinic pairs behave as the source predicts).
- **Not achieved / open:** no n ≥ 9 search for 347483; no order ≥ 32 full group scan
  for 327474 (no GAP in lane); trees n ≥ 10 for 338062; full-body reads for 331790,
  332567, 320837, 340687, 390106 (Lanneau–Thiffeault), 318431 status check; the
  ScienceDirect published versions were not accessed (denied route). Zero MathDB API
  requests. No numerical inference was used as proof anywhere; finite searches are
  recorded as finite searches.

## Counts

Unchanged: 9 additional / 39 total / next 40. This lane claims 0 accepted results,
0 statement-review coverage beyond its own 50 rows, and 0 novelty clearances.

## Integrity

- `manifest.json` records actual SHA-256 per payload; `verify.py` recomputes and
  **exits nonzero on any mismatch or missing file** (no descriptive-only manifest, no
  vacuous readiness check). Manifest and receipt are excluded by exact filename.
- `verification-receipt.json` is written separately after the payload write and
  records the post-write comparison.
- All references are flat immutable pointers (frozen copies + upstream URLs); no
  recursive historical copies.
