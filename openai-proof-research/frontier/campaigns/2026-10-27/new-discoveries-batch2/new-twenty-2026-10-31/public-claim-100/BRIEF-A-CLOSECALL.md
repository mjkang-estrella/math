# Close-call re-adjudication brief (public-claim follow-up, root Claude Fable 5.2, 2026-11-19)

C = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31`

## Why
The user wants to say in public: "I let AI solve 100 open math problems from MathDB, each with a kernel-checked Lean proof." Twelve accepted results were flagged as close calls. Each must now end with no open doubt: either CLEARED with evidence, or NOT COUNTED (it stays in the ledger but out of the public list). You are the adversary: your job is to find the reason a specialist would object, not to defend the result. A wrong CLEARED is far more costly than a wrong NOT COUNTED.

## For each assigned result
Inputs: `C/mathdb-submissions/<id>-*/` (SUBMISSION.md, PAPER.md, Lean source), the acceptance record `C/<name>-<id>-acceptance.json` (lanes, caveats), earlier reviews named there, the MathDB record text via `python3 C/root-intake-r60/corpus_row.py <id>`, and the source paper (arXiv).

1. Settle the specific doubt named in your task (read the unread source, compare the records, decide the scope question). Read primary sources in full text; an abstract is not a reading.
2. Statement fidelity: compare three things word by word: the MathDB record, the conjecture as printed in the source, and the Lean endpoint. Say exactly which statement is proved or refuted and whether it is the MathDB problem.
3. Routine test, adversarially: try to produce the shortest proof from published results and from the source paper's own lemmas, tables, examples and remarks. Would a specialist referee in this area say "this is known", "this is an exercise / a few lines from Theorem X", or "the conjecture was only open because nobody looked"? Give the route you found, its length, and a yes/no. "Modest but real" (a genuine argument that needed an idea, on a conjecture the source authors left open) is acceptable; "routine corollary", "already public" or "not the stated problem" is not.
4. Fresh prior-art pass on the exact statement: later arXiv versions of the source, papers citing it (OpenAlex / Semantic Scholar), arXiv search by API (`http://export.arxiv.org/api/query`, at most one request per 3 seconds), general web search, ProbXiv (probxiv.com), `gh search code`, the omega registry (`OMEGA_REPO=/tmp/claude-1000/-home-mj-kang-Documents-Dev-math/03704234-97d1-47f1-8192-8d8ee0dea55c/scratchpad/omega/repo python3 C/root-intake-r60/omega-screen.py KEY ...`) and the openai/math registry (local clone, grep it: `/tmp/claude-1000/-home-mj-kang-Documents-Dev-math/75a48aa2-847d-4c84-96d4-c7a2d5bb5b22/scratchpad/shared/openai-math`).

## Sources that refuse automated access
Respect robots.txt, paywalls, bot challenges and 403s. Do not work around them (no proxies, no shadow libraries, no spoofed headers). Legitimate open copies are fine: arXiv, author pages, institutional repositories, publisher open archives, OA locations listed by OpenAlex or Unpaywall. mathdb.com refuses automated clients: do not fetch it. If a needed source cannot be obtained, list it in `BLOCKED-SOURCES.json` with full citation, DOI or URL, what you tried, and the exact question it must answer (for example "does Theorem 2 give k distinct characters agreeing on all cycles of bounded support?"). The user will be asked for those PDFs once.

## Verdicts
- CLEARED: the doubt is eliminated by evidence you read, the statement in the row is exact, a specialist would not call it routine or known.
- NOT_COUNTED: known, routine, trivial, not the stated problem, or a doubt that cannot be eliminated.
- BLOCKED_ON_SOURCE: everything else is clean and the only remaining obstacle is a named source you could not obtain.

## Deliverables (in your lane folder only; no git; nothing published or sent anywhere)
- `ADJUDICATION-<id>.md` per result: the doubt, what you read (full text or not), the fidelity comparison, the shortest route found, prior-art queries and hits, verdict and confidence.
- `result.json`: `{"lane":..., "results":[{"mathdb_id":..., "verdict":"CLEARED|NOT_COUNTED|BLOCKED_ON_SOURCE", "specific_doubt":..., "how_settled":..., "would_specialist_call_routine": true|false, "shortest_route":..., "exact_statement_for_public_row":..., "outcome":"PROVED|REFUTED", "lean_endpoint_matches_row": true|false, "caveats_row_must_carry":[...], "closest_prior_read":[{"citation":..., "url":..., "read":"full text|abstract|excerpt", "relation":...}], "queries":[...], "blocked_sources":[...], "confidence":...}]}`
- Computation is allowed (Python, Sage if installed); keep scripts in `scripts/`.
Final message: one line per result with the verdict and the deciding reason, and anything only the user can unblock.

## Added 2026-11-19 (two public archives the sweep found; check both for every result)
- Principia Math (principia-math.com) published write-ups keyed by MathDB id; a public backup is cloned at `/tmp/claude-1000/-home-mj-kang-Documents-Dev-math/75a48aa2-847d-4c84-96d4-c7a2d5bb5b22/scratchpad/shared/principia` (`site-backup/mathdb-<id>/` with 247 ids, commit dated 2026-10-26, and `mathdb/<id>/`). It has already removed six accepted results. Check your id, neighbouring ids from the same source paper, and grep for the source arXiv id.
- `mio-qwq/math` (GitHub, releases up to 2026-10-15), cloned at `/tmp/claude-1000/-home-mj-kang-Documents-Dev-math/75a48aa2-847d-4c84-96d4-c7a2d5bb5b22/scratchpad/shared/mio-math`. Grep for the source arXiv id and key terms.
- GitHub by id: `gh search code 'mathdb-<id>'`, `gh search code '"MathDB <id>"'`, `gh search repos 'mathdb <id>'`.
