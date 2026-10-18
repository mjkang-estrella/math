# RCS128 proof review r1 — checkpoint and exact reading limits

Reviewer: independent proof-review sub-agent. Date: 2026-10-17. Status: **review complete; verdict PASS_FULL_RCS128 (proof gate only)**. No acceptance, count, contribution, manuscript, Lean or publication claim. Campaign count unchanged (12/20 at assignment); uploads stopped; nothing staged or committed.

## What was read in full
* Author packet: `candidate.md` (complete), `original-scope.txt`, `checkpoint.md`, `README.md`, `self-text-rule-and-host.md`, `quotient-cycles.md`, `folded-threshold.md`, `counts-and-euler.md`, `contribution-and-limits.md`, `connection-interface.md`, `verify.py`, `checks.py`, `search-budget.py`; `check-new-interfaces.py` (all logic lines 1–125); `explore.py` (count/layer code read; historical search loop skimmed).
* Partially: `budget-counterexample.md` (first 40 lines: instance, counts, rule table).
* Pinned source `A-Polynomial-Time-2-Approximation-for-Shortest-Common-Superstring-September-24-2026/build/sections/` 01 (theorem statement and overview), 02, 03, 04, 05, 06, 07 — complete bodies, from the packet's private copies whose Git blob SHA-1 I matched against the repository's own nontruncated `sources/preprints-tree.json` at `fd4aeeb2eeb…`. `paper.tex` only grepped; `references.tex`, figures, README not read.
* Repository: `AGENTS.md`, `sources/upstream.json`, parent brief `rcs128-parent/proof-review-brief.txt`.

## What was NOT read / not done
* Not read: `strengthened-fixed-rule.md` (historical optional fixed2k+2 variant, not in the algorithm), the JSON certificate payloads beyond what `verify.py --replay` checks, `exploration.json`, parent half-Euler outside-packet files (`parent-support-refs.json` targets).
* Primary Yamano–Shibuya PDF/extraction: only lines 1–40 (title/abstract) glanced; no contribution, novelty or priority assessment was performed (separate gate).
* No upstream truth audit (stipulated). No literature search. No Lean.
* The executable model is a reviewer implementation, run on bounded random/exhaustive inputs; it is not a proof and not an author algorithm execution.

## Diagnostic record (all in this directory)
* `rc_counts.py`, `rc_algorithm.py` — independent implementations.
* `exhaustive_w_vs_opt.py` (12,7,4: 297,492 families), `search_w_vs_opt.py` (60,000 + 300) — no W<OPT_RC, no domination failure.
* `diff_counts_vs_author.py` — counts agree with author's frozen code on all instances tried.
* `run_algorithm_search.py`, `host_coverage_search.py` — end-to-end model runs; no assertion failure. `host_cov_11.json` and `host_cov_2[1-4].json` were produced by the model version BEFORE the shadow-reclassification checks were added; `host_cov_11b.json` and the replay use the final version.
* `replay-expected.json` — pinned seeds/outputs for `verify.py --replay`.

## Failures/limits retained
Author history (W6<OPT7 for the old rule; identical-profile multiplicity false; direct-root shortcut; axis/lexmax mismatch) is acknowledged and not used; the review concerns the frozen broad2k+1 candidate only. Multi-child flipped batches were rarely or never reached by the executable model; their correctness rests on the hand re-derivation (review.md S8) plus shadow checks of reflected reclassification on every generated request.
