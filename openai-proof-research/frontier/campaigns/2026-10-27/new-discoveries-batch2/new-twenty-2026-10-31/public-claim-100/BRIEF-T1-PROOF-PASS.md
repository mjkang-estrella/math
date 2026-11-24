# Proof pass for tier-1 results (root Claude Fable 5.2, 2026-11-20)

C = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31`

## Goal
The user now wants 100 results of the first tier: a proof of a conjecture listed as open on MathDB, or a refutation of one, that a specialist would not call routine, with a kernel-checked Lean proof. There are 48. Easy counterexamples found by a quick search no longer help: the list has 52 of those and they are a separate tier. What is needed is proofs, and refutations that need a real idea.

## Your input
A pool file of MathDB problems on which an earlier discovery lane made partial progress and stopped (searched, found no counterexample, or reduced the problem and did not finish). Each entry gives the id, the earlier lane's folder and its note. Record text: `python3 -I C/root-intake-r60/corpus_row.py <id>`, run from your own folder. Read the earlier lane's files for the entries you take up (REPORT.md, ATTEMPTS.md, scripts): do not redo its searches.

## What counts and what does not (from 135 audited results)
Counts: a complete proof of the conjecture as the source prints it, in its full stated range, where the proof has at least one step the source's authors did not have (a new invariant, a bijection, an induction on the right quantity, an inequality they missed, a reduction to a finite certified computation they could not do). A refutation counts in this tier only if finding it needed a construction or a structural idea: an infinite family, a witness far outside any plain enumeration, or a counterexample designed from an understanding of why the conjecture fails.

Does not count, however correct:
- public: already proved or refuted in a later version of the source, its journal version, a paper citing it, the Principia archive, the omega registry (including its GitHub issues), ProbXiv, openai/math. About one claim in five died here.
- routine: a few lines from one published theorem or from the source's own lemmas, formulas or tables. A referee who knows the area would say "this follows from Theorem N". About one claim in five died here. Before you invest in a target, write down the shortest route you can see from the source's own results; if it is under ten lines, drop the target and say so.
- trivial: a failure at the smallest parameter, a misprint, a degenerate case, the source's own example or a one-step change of it, the next parameter value after the source's table found by plain enumeration (that is the second tier, not wanted now).
- not the stated problem: a special case, a weakened range, a different reading of the record when the source is clear.
- a proof whose honest Lean statement needs thousands of lines of theory Mathlib lacks (generic rank and Zariski-open sets, measures defined by moments, stochastic processes, representation theory of S_n beyond basics, motivic classes, Jack polynomials, schemes). Nine correct proofs are stranded for this reason. Prefer targets whose statement and proof live in finite combinatorics, graph theory on finite graphs, elementary number theory, polynomial and power-series identities, real inequalities, recurrences, finite linear algebra, words and permutations.

## How to work (about three hours; less means you stopped too early)
1. Read every pool entry and its earlier note (ten minutes). For each, one line: is the conjecture probably true, is there a visible proof mechanism, how heavy would Lean be.
2. Choose the three or four best targets: probably true, statement elementary, a concrete mechanism in sight (the earlier lane's reduction, a pattern in its data, an induction that the small cases suggest). Open the source for each and read the section around the conjecture: what the authors proved, what they tried, why they stopped.
3. Work on them in turn, at least forty minutes each before giving up. Compute to find the structure (exact arithmetic, generate data, guess formulas, test lemmas numerically before proving them). When one opens up, finish it: a complete written proof with every step justified, every lemma tested by an independent computation, and the full range of parameters covered including the small cases.
4. For each proof you complete: the prior-art checks (all arXiv versions and the journal version of the source; papers citing it via OpenAlex or Semantic Scholar; `C/public-claim-100/principia-ids.txt`; `gh search issues --repo the-omega-institute/trureturing "<arXiv id>" --limit 10 --json number,title,createdAt` and the same with two or three distinctive words, three seconds apart; a web search on the conjecture's name). Respect robots.txt and refusals.
5. Write an honest self-assessment for each: the shortest route from published results you could find, what the new step is, and how a specialist would rate it.

A pass with no complete proof is a normal outcome; say what you tried and where each attempt stopped, so the next lane can continue. Do not pad the result list with partial results, special cases or easy counterexamples. If you do meet an easy counterexample, record it in one line under "tier2_side_finds" and move on.

## Deliverables in your lane folder only
- `PROOF-<id>.md` per completed result: the source's statement quoted, the theorem you prove, the full proof, the checks you ran (with `scripts/`), prior-art sources actually read, the self-assessment, and a section "Lean plan" with the literal endpoint in Lean-like notation, the definitions needed, and an estimate of lines.
- `REPORT.md`: every pool entry with its one-line triage; for the targets you worked on, what was tried and where it stands.
- `result.json`: `{"lane", "solved": [{"mathdb_id", "outcome": "PROVED|REFUTED", "statement", "new_step", "shortest_known_route", "flags": [...], "lean_estimate_lines", "proof_file"}], "attempted": [{"mathdb_id", "status", "where_it_stopped"}], "tier2_side_finds": [...]}`.
Final message: each solved id with one sentence, its new step, its Lean estimate, and anything root must decide.

Rules: no git commands; nothing submitted, published or sent anywhere; respect publisher and site refusals; do not start subagents; at most 3 cores and 8 GB at a time; run Python as `python3 -I` from inside your own folder (a file named `inspect.py` in C shadows the standard library otherwise).
