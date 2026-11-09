# Expanded corpus r95

**20 reserved IDs investigated; zero claimed qualifying solutions; zero credit; no Lean endpoint.** Root acceptance remains separate. No shared counts or ledgers were changed.

The pass recovered all 20 exact raw corpus lines, with original newline, chunk and raw SHA256, one-based line, literal statement and statement hash. Primary HTML was recovered for 19 sources; the grid source's HTML was 404 and its primary PDF was recovered and read. The orbit conjecture required v1/current-version comparison. Source receipts, original bodies, scripts and full computational outputs are retained. `results.json` has exactly 20 ID-keyed entries. `outputs/search-coverage.json` retains the completed rows and output hashes; unfinished searches are explicitly labeled.

## Main dispositions

- **357800:** already proved in its cited source, Theorems 1.1 and 3.1. The actual Section 3 proof was read.
- **382272:** v1 Conjecture 8.45 is addressed by current Theorem 8.3 and its constructive Section 8.5 proof. Older coordinate constants differ; no credit for repairing them.
- **361538:** a literal generation obstruction was detected at k=562 and traced back to k=22. Independent direct checking verifies the 22-term WCS and enumerates a 12-element literal generator closure excluding it. However, the witness is a one-step extension of the source's printed length-21 starting construction, and Table 2 already reports 16 WCSs at length 22. This is a source-internal construction omission/routine bridge, not a claimed significant new solution. See `WCS-SOURCE-INTERNAL-OBSTRUCTION.md`. No surrogate Lean theorem was manufactured.
- **340676:** symmetry and factorial sum are already proved by Donghyun Kim in source Appendix A. Only unimodality remains; the new finite checks do not prove it.
- **365977:** the positive disk center/negative symmetry-axis conflict is in the primary source too. The intended root-location problem was not refuted by exploiting that sign error.
- **372282:** xi_1 is a fourth-order Steklov eigenvalue in the source. Treating it as ordinary Steklov would change the problem.
- All remaining IDs are parked with their exact search coverage and remaining mathematical gaps, not declared solved or novelty-cleared.

## Computational coverage

| ID | Actual covered space | Result/limit |
|---|---|---|
| 361538 | Complete permutation CSP for k=1..24; all one-transposition neighbors of printed seeds for k=501..1000; complete filtered CSP at k=501..570 and 851..870 except capped k=861 | Literal generated-family mismatches at 562 and 862, source-internal analogue already at 22; earlier unfiltered 30000-node attempts incomplete |
| 366336 | All 3355 labeled Laman graphs on six vertices; 240 Henneberg samples each at n=6,7,8,9,10,11,12,14,16 | No counterexample; unique samples classified by one-open 0-extension or no stable cut plus one prism |
| 382189 | Exact univariate polynomial Pfaffians/consecutive division through n=32, with homogeneous degree bridge; 111 integer (k,t) specializations through n=48 except zero pivots | No failure; zero pivots stop those specializations; no all-n proof |
| 354984 | Direct minimax m=2..8,10; component-canonical minimax m=2..6,8,10,12,16; two m=32 attempts | Values agree with source on completed cases; m=32 incomplete at 250000/600000 state caps |
| 351415 | All labeled connected graphs through order six; 2400 structured connected samples each at n=10,11,12,14,16,20 | No candidate beating all trees; sample maxima are not exact global maxima |
| 338455 | Four tree templates at n=4..7, six edge-order samples each, exact regular-representation trace moments through power five | No ordering discrepancy; no all-spectrum result or beyond-10 forest count |
| 346781 | Every strict two-row shape of total size 3..100, exact uniform/chain-weighted down-degree comparison | No unexpected CDE hit; higher-row general scope remains |
| 341633 | Every balanced linear word at n=6,12,18; swap descent at n=36,42,48,60,90,120; source-extremal seeded descent through n=144 | No violation; seeded minima remain n/3+1 |
| 371756 | Same connected graph sweep; 240000 integer-weighted independent-set blowup evaluations on bases of orders 5..10 | No numerical violation; quotient reduction extends graph orders, but floating point is diagnostic |
| 365977 | All binary snake words up to 16 L/R letters modulo complement; exact integer descent polynomials and rational Sturm checks of 33145 distinct polynomials | No failure of h* negative real-rootedness; intended Ehrhart disk part remains untested |
| 375082 | All 3003 six-vertex five-edge hosts for the smallest nonuniform pair; 1500 fixed-edge hosts for each of four further pairs | Each host has an avoiding coloring; no universal Ramsey lower bound proved |
| 347736 | All 24 length-four patterns on S9; all 120 length-five patterns on S8 and on S9 | All functional-graph cycle sets equal literal avoidance classes; 57,093,120 pattern/permutation pairs in these three full sweeps |
| 340676 | Exact diagonal numerators and gamma expansions for j=1..100 | Symmetry, factorial sum, unimodality and nonnegative gamma coefficients hold in this finite range |
| 346886 | Five exact uniform rank-three realizable arrangements at each n=6,9,10,11,12,14,16,20; all common-tope pairs | No failure; arbitrary rank/nonrealizability not covered |

346455 (colorful topological Tverberg), 374838 (cascade consequence), 372282 (Steklov) and 341012 (Nekrasov) received source-backed scope dispositions rather than false finite surrogates. 357800 and 382272 were stopped at primary-source resolution gates.

## Evidence and limits

Live registry refresh used `/commits/HEAD` only: OpenAI/math `4eaee87548250b2682affda7d05d947c05554bae`; Omega `45d162eae7358188735ef9161b64d3c9b2899b3a`. Complete untruncated Omega D5/Problems path screens found no reserved-ID path match. This is not proof-body novelty clearance. The unchanged OpenAI HEAD is distinguished from the older ancestor manuscript pin. Receipts and cached-list bindings are in `outputs/registry-screen.json`.

Historical scanning covered 12616 selected report/ledger files under openai-proof-research. Reserved ledger entries are reservation matches, and numeric-string matches in unrelated computations are false positives. This does not establish global nonreview or novelty.

`ROUTES.md` gives sustained mechanisms, exact algorithms and unresolved proof lemmas. `VALIDATION.md` explains resource caps, reproducibility, numerical limits and initial failed tool attempts. No endpoint survived the source/significance gates, so no Lean packet, axioms audit or full upstream rebuild is claimed. All generated artifacts stay in this lane; the final process check is in `outputs/process-check.json`.
