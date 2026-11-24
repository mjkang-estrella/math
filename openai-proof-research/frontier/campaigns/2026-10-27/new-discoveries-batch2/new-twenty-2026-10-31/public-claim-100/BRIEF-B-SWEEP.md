# Uniform prior-art sweep brief (public-claim follow-up, root Claude Fable 5.2, 2026-11-19)

C = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31`

## Why
The user wants to say in public that AI solved 100 open MathDB problems. "Open" must be supported by the same search for every result. For each assigned MathDB id, decide whether the result (the exact statement proved or refuted) was already public before our acceptance date. The model to follow and extend is `C/public-tracker-prior-art-sweep-sol62-20261119-r1/SWEEP.md` and `sweep.json`.

## Per result
Read `C/mathdb-submissions/<id>-*/SUBMISSION.md` (statement, source, outcome, summary; PAPER.md or manuscript.pdf if you need the exact theorem). Then run every route below and record each query with its hit count.

1. Source history: the arXiv abs page of the source (all versions, comments, withdrawals, journal reference) and the journal version if it is open.
2. Citing papers: OpenAlex (`https://api.openalex.org/works?filter=cites:<W-id>`) and the Semantic Scholar graph API (`/graph/v1/paper/arXiv:<id>/citations`). Scan every citing title and abstract; open the full text of any that could contain the result.
3. arXiv keyword search through the arXiv API (`http://export.arxiv.org/api/query?search_query=...`, the programmatic interface arXiv provides; at most one request per 3 seconds): conjecture name, key terms, author surnames plus "conjecture".
4. Google Scholar: try the key-term query once. If it refuses automated clients (CAPTCHA, 429, robots), record the refusal, do not work around it, and use OpenAlex full-text search (`search=`), Semantic Scholar search and Crossref as the substitute.
5. General web search: conjecture name with "proof", "counterexample", "disproved", "resolved"; MathOverflow and Math StackExchange.
6. openai/math registry: grep the local clone `/tmp/claude-1000/-home-mj-kang-Documents-Dev-math/75a48aa2-847d-4c84-96d4-c7a2d5bb5b22/scratchpad/shared/openai-math` (head 4eaee875; `grep -rIl` on arXiv id, author surnames, key terms; skip binary files).
7. omega registry: `OMEGA_REPO=/tmp/claude-1000/-home-mj-kang-Documents-Dev-math/03704234-97d1-47f1-8192-8d8ee0dea55c/scratchpad/omega/repo python3 C/root-intake-r60/omega-screen.py <arXiv id> <surname> <key term> ...` (head 40ae81c0, 2026-11-19). Open every file it lists and decide whether it resolves the same statement.
8. ProbXiv (probxiv.com): `/?q=` by MathDB id, title words, arXiv id, surname; open the record; note status, attempts, comments.
9. GitHub code search: `gh search code '<arXiv id>'`, `gh search code '"<conjecture name or key phrase>"'`, `gh search repos '<key phrase>'` (gh is logged in; code search allows about 10 requests a minute, so sleep between calls). Queries must contain only mathematical terms.
10. MathDB itself (mathdb.com) refuses automated clients. Do not fetch it. Record it as not checked.

Respect robots.txt, paywalls, bot challenges and 403s; never work around a refusal. Record each refused route and each paper you could read only as an abstract.

## Verdict per result
- PRIOR_FOUND: the same statement, or one that gives it in a few lines, was public before our acceptance date (see `accepted_utc`/`utc` in `C/ledger.json` or the acceptance file). Quote the theorem, give the URL and date, and explain the implication precisely; this removes the result from the public list, so be exact. If you are unsure, say SUSPECT and explain what must be checked.
- PARTIAL_OVERLAP: known special cases or neighbouring results (say whether the submission already credits them).
- NO_PRIOR_FOUND.
Also report anything public AFTER our acceptance date (later independent work), separately.

## Deliverables (in your lane folder only; no git; nothing published or sent)
- `SWEEP.md`: one section per id in the format of the earlier SWEEP.md (verdict, dated evidence lines with URLs, "Queries and routes searched" with hit counts), plus a line "Closest prior work read: <citation> (<full text|abstract>)" and a line "Routes refused: ...".
- `sweep.json`: list of `{"mathdb_id", "verdict", "evidence":[{"url","date","what it says","how it relates"}], "closest_prior_read":{"citation","url","read"}, "searched":[...], "routes_refused":[...], "later_independent_work":[...], "unread_sources":[{"citation","url","why needed"}]}`.
Work through all assigned ids; do not stop at the first. Final message: counts per verdict, every PRIOR_FOUND or SUSPECT with one sentence, and sources only the user can supply.
