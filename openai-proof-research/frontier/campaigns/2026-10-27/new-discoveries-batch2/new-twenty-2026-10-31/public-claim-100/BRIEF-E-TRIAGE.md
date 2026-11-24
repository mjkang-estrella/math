# Adversarial triage brief for results never tested for routine or trivial (root Claude Fable 5.2, 2026-11-19)

C = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31`

## Why
The user wants to say in public: "I let AI solve 100 open math problems from MathDB, each with a kernel-checked Lean proof." Of the accepted results that were re-examined by a non-author model so far, about half were removed: the conjecture was false at the first small case anyone would check, or the result followed in a few lines from a published theorem, or it was already public. The results assigned to you passed a statement-fidelity audit and a prior-art sweep but were never put to that adversarial test. You are the adversary. A wrong SOLID is far more costly than a wrong NOT_COUNTED.

## Per assigned id (aim for about 25 minutes each; spend more only where the answer is close)
Inputs: the row in `C/public-claim-100/base-rows.json`; the fidelity entry in `C/row-fidelity-audit-D{1,2,3}-sol62-20261119-r1/fidelity.json`; the prior-art entry in `C/uniform-prior-art-sweep-B*-sol62-20261119-r1/sweep.json` (or `C/public-tracker-prior-art-sweep-sol62-20261119-r1/sweep.json`); `C/mathdb-submissions/<id>-*/` (SUBMISSION.md and the paper); the source paper on arXiv.

1. For a REFUTED result: find the smallest counterexample by your own computation from the source's definitions wherever a search is feasible. What sizes did the source authors check? Is the accepted witness at the first size beyond that, and does a generic search (brute force, random search, annealing) find a counterexample in seconds or minutes? Does a published theorem or the source's own lemma give the counterexample by substitution? Is the witness degenerate (edgeless, disconnected, n = 0 or 1, a padding trick)?
2. For a PROVED result: write down the shortest proof you can from published results and the source's own lemmas, tables and examples. Is it a few lines from one theorem? Did the source authors or later papers say why it is hard? How long was it open and how many papers cite the source?
3. Check the two public archives for the id, neighbouring ids from the same paper and the source arXiv id: `/tmp/claude-1000/-home-mj-kang-Documents-Dev-math/75a48aa2-847d-4c84-96d4-c7a2d5bb5b22/scratchpad/shared/principia` (`site-backup/mathdb-<id>/`, `mathdb/<id>/`; id list in `C/public-claim-100/principia-ids.txt`) and `.../scratchpad/shared/mio-math`. The GitHub API quota is shared and tight: at most two `gh search` calls per result.
4. Verdict, one of four (root decision 2026-11-19: easy computer-found counterexamples are a class of their own, reported separately and not discarded):
   - SOLID: a specialist would accept that a genuinely open problem was solved (modest is fine). For a refutation this needs more than a quick search: a counterexample beyond what generic search reaches in minutes, or one that needed a structural idea, or a problem several papers had left open after computing small cases.
   - SEARCH_EASY: correct, literal, not public and not a consequence of a published theorem, with a non-degenerate witness, but the conjecture fails at the first size beyond what the source checked and a generic search (brute force, random, annealing, SAT) finds a counterexample in seconds or minutes. Record the smallest failing size, the search time and what the source checked.
   - NOT_COUNTED: already public; or a few lines from one published theorem or from the source's own lemmas, tables or examples; or the witness is degenerate (edgeless, n = 0 or 1, padding), a typo or a mis-scaled statement; or the conjecture fails inside the range the source says it tested or on one of the source's own examples; or the result is not the stated problem. Give the route, citation or example.
   - DOUBT: say exactly what must still be checked.

Respect robots.txt, paywalls, bot challenges and 403s; never work around a refusal. Computation is allowed; keep scripts in `scripts/`.

## Deliverables (in your lane folder only; no git; nothing published or sent)
- `triage.json`: list of `{"mathdb_id", "outcome", "verdict":"SOLID|SEARCH_EASY|NOT_COUNTED|DOUBT", "reason", "smallest_counterexample_or_shortest_route", "source_checked_range", "generic_search_time", "archives_checked":true, "confidence", "row_caveats":[...]}`.
- `TRIAGE.md`: a table (id, verdict, one-line reason) and a paragraph for every NOT_COUNTED and DOUBT with the evidence.
Write each result as you finish it. Final message: counts per verdict and one line for every NOT_COUNTED and DOUBT.
