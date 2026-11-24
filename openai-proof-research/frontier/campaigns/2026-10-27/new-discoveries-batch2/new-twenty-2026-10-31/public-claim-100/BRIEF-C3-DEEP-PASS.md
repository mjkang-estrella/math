# Deep discovery pass (root Claude Fable 5.2, 2026-11-20)

C = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31`

Read `C/public-claim-100/BRIEF-C2-DISCOVERY-ROUND2.md` and the two briefs it names first; this file adds what the round has taught.

## What survives, and what does not
Of about forty claims made in this round, the ones that reached the list were: explicit small counterexamples to "the exact value is X" or "an extremal object of type Y always exists" conjectures (a 30-vertex resolving set, a 20-vertex graph, a length-13 word, a cubic polynomial, a polynomial quotient with one negative coefficient, a count of codes at the first prime the authors had not reached), each with a Lean proof of 300 to 1000 lines. Complete proofs whose statement is finite or reduces to an elementary induction or a finite certificate also go through.

Claims that were correct but did not count:
- a conjecture that says "the table of Theorem N also applies", refuted only where Theorem N's own hypothesis fails. Check inherited hypotheses before claiming.
- a failure at the smallest parameter, or one that disappears for large parameters when the neighbouring conjecture says "for large m".
- a failure inside a family the source says it verified, or a wrong digit in a printed constant.
- a few lines from a classical theorem (for example the chromatic number of a product with a complete graph is a multichromatic number).
- results whose honest Lean statement needs thousands of lines of theory Mathlib lacks: generic rank and Zariski-open sets, measures defined by moments, stochastic processes, representation theory, motivic classes. These were proved on paper and then could not be formalized. Do not spend your time on them unless nothing else is available; say so in one line and move on.

## How to work
1. Triage all 60 rows quickly (one line each). Mark every row whose statement is finitely checkable or reduces to a finite or elementary statement.
2. For each such row open the source, write down what range the authors tested, and search clearly beyond it: exhaustive enumeration where feasible, SAT or ILP, structured families, exact arithmetic. Let searches run for tens of minutes. Keep scripts and record the range covered.
3. Give the two or three most promising rows with a cheap Lean statement a sustained proof attempt.
4. Before writing a proof file: the prior-art checks of the addendum, and the journal version of the source (if the publisher refuses, say so and compare arXiv version dates with the journal's acceptance date).

Expect to work for two to three hours. A pass that ends in under an hour has not searched enough.

Deliverables in your lane folder: TRIAGE.md, PROOF-<id>.md with scripts/ per claim, REPORT.md (every row, the source's tested range, the range you covered, disposition), result.json in the main brief's format with "flags" and "lean_estimate_lines" on each solved entry. Final message: the SOLVED ids with one sentence each, their flags and Lean estimates, and anything root must decide.

Rules: no git commands; nothing submitted, published or sent anywhere; respect publisher and site refusals; do not start subagents; at most 2 cores and 8 GB at a time; run Python as `python3 -I` from inside your own folder.


## Added 2026-11-20: the omega registry posts through GitHub issues
A result was lost because it had been refuted two hours earlier in an issue of the public repository `the-omega-institute/trureturing`. Neither the local clone nor `gh search code` shows issues. For every candidate run `gh search issues --repo the-omega-institute/trureturing "<arXiv id of the source>" --limit 10 --json number,title,createdAt` and the same with two or three distinctive words of the conjecture (authors, the named object), and read any hit with `gh issue view <n> --repo the-omega-institute/trureturing`. These calls are in addition to the `gh search` allowance above; wait three seconds between calls (the search limit is 30 per minute, shared).
