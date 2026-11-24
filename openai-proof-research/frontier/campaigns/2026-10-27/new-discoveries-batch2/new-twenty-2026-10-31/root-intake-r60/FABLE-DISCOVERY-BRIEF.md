# Discovery lane brief (MathDB campaign, root Claude Fable 5.2, from 2026-11-18)

## Goal
Resolve as many of the MathDB open problems in your shard as you can. A resolution is a complete proof of the exact statement, or a complete refutation (exact negation), using the definitions of the source paper the record cites. Each resolution must have a realistic route to a Lean 4 + Mathlib formal proof, because acceptance later requires a kernel-checked literal endpoint.

## What counts and what does not
Counts: the whole stated problem, proved or refuted, new as far as a bounded search can tell.
Does not count: a result already public (paper, later arXiv version, erratum, MathOverflow answer); a few-line corollary of one published theorem; fixing a typo or an obviously misstated record; a special case or partial progress; numerical evidence. Report these honestly with the citation or the gap; they are useful dispositions, they just earn no credit.

Where wins have come from in this campaign: explicit finite counterexamples found by search and then verified by hand; conjectures in recent arXiv papers that rest on computation only; exact formulas, sign tables and inequalities provable by induction, generating functions or a finite reduction; extremal conjectures refuted by a construction; small structural statements about graphs, posets, matroids, partitions, words, polytopes.

## Method
1. Triage every row of the shard (title and statement). Write TRIAGE.md with one line per id and a shortlist of at least ten, ranked by chance of a full resolution and by Lean feasibility.
2. For each shortlisted problem, read the exact definitions and the conjecture in the source (arXiv abstract page and PDF or HTML). Check early whether it is already settled: later versions of the source, papers citing it, a web search on the conjecture's name and key formula. Record what you searched and what you read.
3. Do the mathematics. Computation is allowed and encouraged: Python with sympy and networkx, SageMath or a SAT solver if installed, brute-force search for counterexamples, testing lemmas before proving them. The machine (32 cores, about 125 GB of memory) is shared with other lanes and with Lean builds, so size your runs sensibly, and keep the scripts.
4. For every problem you believe you have resolved, write PROOF-<id>.md: the MathDB statement verbatim, the source definitions, the theorem you prove, a complete rigorous proof (every case, no sketches), the scripts that support it, the prior-art search, the strongest objection that the result is known or routine together with your answer, and a Lean plan (the endpoint statement in Lean-like form, which Mathlib notions exist, estimated lines, the riskiest step).
5. Audit yourself before reporting: reread each proof as a hostile referee, and verify any counterexample with a second independent script.

Give at least three problems a sustained attempt; do not stop at the first failed idea. A lane that returns two solid resolutions is a very good lane. A typical run is two to four hours.

## Rules
- Write only inside your lane directory. No git. Start child agents only if your task says you may.
- No accounts, logins, uploads, posts or messages to anyone. Nothing is published.
- Respect robots.txt, paywalls and refusals: if a site refuses, do not work around it; use arXiv or another open copy. Ordinary transient errors may be retried once.
- Do not read proof bodies in other lanes. You may read the files your task names.
- Already accepted results (do not redo them): `root-intake-r60/sanitized-acceptance-release-114-v13-20261115.json` and `root-intake-r60/accepted-statements-addendum-116-125-20261118-v1.json`. If a shard problem is the same question as an accepted one, mark it DUPLICATE.

## Deliverables (in your lane directory)
- TRIAGE.md
- PROOF-<id>.md for each claimed resolution, with scripts in scripts/
- REPORT.md: a table of every shard id with disposition SOLVED, PUBLIC (with citation), ROUTINE (with the bridge), PARTIAL (with the exact gap), DUPLICATE or SKIPPED, and one line of reason; then a paragraph per SOLVED item with your honest confidence in correctness, novelty and Lean cost
- result.json with the same dispositions in machine-readable form: {"lane": ..., "solved": [{"mathdb_id", "outcome": "PROVED"|"REFUTED", "proof": "PROOF-<id>.md", "confidence": ..., "lean_estimate_lines": ...}], "others": [{"mathdb_id", "disposition", "note"}]}

Your final message: the list of SOLVED ids with one sentence each, and anything root must decide.

## Prior-art sources that have killed candidates (check these first)
- Recent arXiv papers (2025-2026) on the same quantity, and the arXiv version history of the source (withdrawals, revisions). Use arxiv.org, not export.arxiv.org.
- ProbXiv (probxiv.com), a public tracker with posted counterexamples.
- The GitHub repository the-omega-institute/trureturing, a large public collection of formalized conjecture resolutions.
A result is ROUTINE if it follows in a few lines from one published theorem or from the source paper's own tables, recurrences, examples or lemmas; TRIVIAL if the conjecture fails for a degenerate case, a mis-scaled inequality or a standard family.
- Zenodo preprints, the source authors' own web pages and companion notes, and later journal papers by other authors on the same parameter (one candidate was already proved in a 2024 journal paper under a corrected formula; another in the source author's own companion note; another in an October 2026 Zenodo preprint).
Before writing a proof, spend real effort on this search for each shortlisted problem: of 33 claimed resolutions reviewed so far, 13 passed, and 8 of the 20 rejected were already public.
