# Prior-art audit of counted results (root Claude Fable 5.2, 2026-11-23)

C = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31`

## RULES FIRST
No git commands at all, not even read-only ones such as `git status` or `git log` (if a helper script calls git, do not run it). Nothing submitted, published or sent anywhere. Read a site's robots.txt (crawl delay and disallowed paths) in a separate step before fetching anything from it; respect paywalls, bot challenges, rate limits and 403s; never work around a refusal. Do not open mathdb.com. Do not start subagents. Do not compile Lean. At most 2 cores. Python as `python3 -I -B` from inside your own folder. Write only in your lane folder. Do not end your turn with a computation still running.

## Why
The user's public sentence is "AI resolved N conjectures listed as open on MathDB, each with a kernel-checked Lean proof, and each cleared by an adversarial review from a second AI model that did not write the proof". The user now asks one question about every counted result: **was this problem already solved by other people?** If it was, the result is dropped. Every row has had a prior-art search before, by the lanes that reviewed it; those searches were bounded and done alongside other work. You do a search that is only about this question, with fresh eyes, on the rows in your batch file. One counted result was lost at its final check to a three-day-old proof in a public repository nobody had searched, and several others to papers that did not cite the source, so assume the earlier searches missed things.

You are not asked whether the result is routine, correct or well formalized. Only: is there a public proof, refutation or resolution by someone else, of this conjecture or of a statement that implies it (or, for a refutation, a public counterexample)?

## Your batch
Your task message names your batch file, `C/public-claim-100/prior-art-audit-20261123/batch-NN.json`. For each row it gives the MathDB id, the record statement, the source, what our result proves (`what_was_proved`), the submission folder under C (with the paper, which has a prior-art paragraph), the note of the earlier prior-art search and the caveats. `python3 -I -B C/root-intake-r60/corpus_row.py <id>` (run from your own folder) prints the record.

## Per row (about 12 to 15 minutes), search in this order
1. **The source itself, all versions.** The arXiv abstract page: every version, the comments field, the journal reference. Read how the latest version states the conjecture: later versions sometimes turn a conjecture into a theorem, add "proved in [X]", "disproved by Y", or drop it. If there is a journal version you can read, the same. Note the dates.
2. **Works citing the source.** OpenAlex (`https://api.openalex.org/works?filter=cites:<work id>`, find the work id by DOI or title), Semantic Scholar (`https://api.semanticscholar.org/graph/v1/paper/arXiv:<id>/citations?fields=title,year,externalIds,abstract&limit=200`), zbMATH Open, INSPIRE where relevant. Go through the whole list, not the first page. For every citing work whose title or abstract touches the conjecture, read the abstract and, if it looks relevant, the full text (arXiv HTML or PDF).
3. **Works that do not cite the source.** Search by the mathematics, not by the citation: web searches with the name of the conjecture, the named objects, the authors' names, with and without the words conjecture, proof, counterexample, disprove, settle, resolve, answer, "question of"; the sequence in the OEIS where there is one; later papers and homepages (publication lists, "open problems" pages) of the source's authors; surveys of the area; MathOverflow and math.stackexchange.
4. **AI and formal-proof registries.** Root is separately running searches by arXiv id of the omega registry (`the-omega-institute/trureturing` issues and pull requests), `mxym/math`, and `openai/math` for every row, so do not repeat those by arXiv id. You may run at most two GitHub keyword searches per row with distinctive words of the conjecture (`gh search issues --repo the-omega-institute/trureturing "<words>" --limit 10 --json number,title,createdAt`; `gh search code --repo mxym/math "<words>" --limit 20 --json path`; or a global `gh search code "<arXiv id>" --limit 20 --json repository,path`), waiting at least 15 seconds between calls; the limits are shared by twelve lanes, so if a call is refused wait a minute, try once more, and if it is still refused list it under `searches_not_run`. Read any hit (`gh issue view <n> --repo ...`, `gh api repos/<owner>/<repo>/contents/<path> -H "Accept: application/vnd.github.raw"`). Also check the local lists: `C/public-claim-100/principia-ids.txt` and the clones under `/tmp/claude-1000/-home-mj-kang-Documents-Dev-math/75a48aa2-847d-4c84-96d4-c7a2d5bb5b22/scratchpad/shared/` (`principia`, `openai-math`, `mio-math`) with grep (not git) if they are still there, for the MathDB id, the arXiv id and sibling ids of the same source.

## What counts, and how to avoid both kinds of mistake
- **A hit must be read.** Do not report a result as solved from a title, an abstract or a search snippet. Open the text, find the theorem, and check that it is the same statement or implies it: same objects, same range, same definitions. Quote the theorem with its number and the date of the version you read (first arXiv version date matters: say whether it is before or after our acceptance, which was between 2026-10-26 and 2026-11-23 for all rows; if the date is not in the batch file, give the hit's date and root will compare).
- **Partial overlap is its own verdict.** A paper that proves a special case, a weaker bound, the other direction, or the same statement under an extra hypothesis is not "solved", but say exactly which part is public and which part our result adds.
- **The source's own later version counts.** If the authors' later version or journal version proves or withdraws the conjecture, that is a hit.
- **AI-generated public proofs count.** A proof in a public repository, registry issue or site by another group counts exactly like a paper, with its date.
- **Independent rediscovery after our date** still matters: report it with dates.
- **An unreadable text** (paywall, 403, challenge) that could plausibly settle the question: name it, say what you could see (abstract, MathSciNet-style summary, table of contents), and give your probability that it contains a resolution.

## Verdict per row
- `SOLVED_BY_OTHERS`: a public resolution by someone else exists. Give the citation, link, date, the quoted theorem, and one or two sentences on why it is the same statement or implies it. Say `before_our_acceptance: true|false|unknown`.
- `PARTLY_PUBLIC`: say exactly what is public and what remains.
- `NOT_FOUND`: nothing found; list what you searched.
- `UNREADABLE_RISK`: nothing found in what you could read, but a named unreadable text has a real chance (say 0.10 or more) of containing a resolution.
Give your confidence that the row is unsolved by others (0 to 1).

## Deliverables (in your lane folder only)
- `audit.json`: `{"batch": NN, "auditor_model": "...", "rows": [{"mathdb_id", "verdict", "confidence_unsolved", "hits": [{"citation", "link", "date", "quoted_statement", "relation", "before_our_acceptance"}], "source_versions": "...", "citing_works_examined": <number>, "citing_lists": ["OpenAlex", ...], "searches_run": [...], "searches_not_run": [...], "unreadable": [{"citation", "what_was_seen", "probability_it_settles"}], "note": "..."}]}`.
- `AUDIT.md`: a table (id, verdict, confidence, the hit or "none"), then a short paragraph per row.
Write each row as you finish it, so that nothing is lost if your run is cut off. Do not stop early: finish every row of the batch.

Final message: one line per row (id, verdict, confidence, the hit with date if any), then the rows you want root to look at first, and the searches that did not run.
