# Tier-1 confirmation brief (root Claude Fable 5.2, 2026-11-19)

C = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31`

## Why
The user wants to say in public: "I let AI solve 100 open math problems from MathDB, each with a kernel-checked Lean proof." The public list has tiers; tier 1 means "a specialist would accept that a genuinely open problem was solved". A triage by GPT-6.2 Sol (the same model family that produced these results) marked the results assigned to you SOLID. Before a row is labelled tier 1 it needs confirmation from a different model: you. You are the adversary; a wrong CONFIRMED is far more costly than a wrong downgrade. Of the results re-examined so far, about two thirds were downgraded.

## Per assigned id (about 20 minutes each; more only where it is close)
Inputs: the Sol triage entry in `C/adversarial-triage-E*-sol62-20261119-r1/triage.json` and TRIAGE.md (find your id; read its reason, shortest route and scripts); the fidelity entry in `C/row-fidelity-audit-D{1,2,3}-sol62-20261119-r1/fidelity.json`; the sweep entry in `C/uniform-prior-art-sweep-B*-sol62-20261119-r1/sweep.json` or `C/public-tracker-prior-art-sweep-sol62-20261119-r1/sweep.json`; the row in `C/public-claim-100/base-rows.json`; `C/mathdb-submissions/<id>-*/`; the source paper.

Test, in this order, and stop at the first failure:
1. Public: `C/public-claim-100/principia-ids.txt` (300 ids, includes Principia's owned-project Lean modules), the Principia clone at `/tmp/claude-1000/-home-mj-kang-Documents-Dev-math/75a48aa2-847d-4c84-96d4-c7a2d5bb5b22/scratchpad/shared/principia` (also sibling ids from the same paper), the journal version of the source and any later version (a journal version that drops or resolves the conjecture has removed two results already), the most obvious later papers.
2. Statement: is the kernel-checked endpoint the MathDB problem under the reading the source fixes? Name any gap.
3. Routine: the shortest proof from one published theorem or from the source's own lemmas, tables and examples. For a refutation: the smallest counterexample and how fast a generic search finds one.
4. Verdict: CONFIRMED_TIER1 (say in one sentence what the real content is, i.e. the step the source authors or later papers could not do), TIER2_SEARCH_EASY (correct and new, but a quick generic search at the first unchecked size), TIER3_SOURCE_SCOPE (the MathDB text is a faulty transcription; the source conjecture is resolved), NOT_COUNTED (public, routine, trivial, the source's own example, or not the stated problem; give the citation or route), or BLOCKED (name the paper and the exact question).

The GitHub API quota is shared and tight: at most one `gh search` call per result. Respect robots.txt, paywalls, bot challenges and 403s; never work around a refusal. Computation is allowed; keep scripts in `scripts/`.

## Deliverables (in your lane folder only; no git; nothing published or sent; do not start subagents)
- `confirm.json`: list of `{"mathdb_id","verdict","real_content_or_reason","shortest_route","statement_gap","sources_read":[{"citation","read":"full text|abstract"}],"row_caveats":[...],"confidence"}`.
- `CONFIRM.md`: a table (id, verdict, one line) and a paragraph for every result that is not CONFIRMED_TIER1.
Write each result as you finish it. Final message: counts per verdict and one line per result that is not CONFIRMED_TIER1.
