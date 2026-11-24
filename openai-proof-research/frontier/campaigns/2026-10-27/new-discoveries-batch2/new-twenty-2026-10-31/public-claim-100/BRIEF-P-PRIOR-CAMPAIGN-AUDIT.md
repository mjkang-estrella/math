# Audit of results from the first campaign (root Claude Fable 5.2, 2026-11-20)

C = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31`
F = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries` (the first campaign: `candidates/<name>/` holds PROOF.md, main.tex, NOVELTY.md, formal/*.lean, reviews/; `ledger.json` and `RESULTS.md` list the accepted results)

## Why
The user wants a public list of 100 conjectures listed as open on MathDB that AI resolved, each with a kernel-checked Lean proof, where every entry is a proof or refutation a specialist would not call routine and nothing public had it before us. The first campaign (accepted 2026-10-26, proofs by GPT lanes, published afterwards by the user at mathdb.com/abs/2610.007xx with Zenodo DOIs) was never put through this audit. Fifteen of its thirty results turned out to have Principia write-ups dated September 2026, a month earlier, and are dropped. You audit the others assigned to you. You are a different model from the authors. A wrong PASS costs far more than a wrong rejection.

## Per assigned result (about 30 minutes each)
Record text: `python3 -I C/root-intake-r60/corpus_row.py <id>` run from your own folder (if it prints nothing, say so). Read the candidate's PROOF.md, NOVELTY.md, the Lean files in formal/ and the reviews. Test in this order and stop at the first failure:
1. **Public before 2026-10-26.** `C/public-claim-100/principia-ids.txt` and the Principia clone at `/tmp/claude-1000/-home-mj-kang-Documents-Dev-math/75a48aa2-847d-4c84-96d4-c7a2d5bb5b22/scratchpad/shared/principia` (`site-backup/mathdb-<id>/`, also sibling ids from the same source paper; the write-ups carry dates); later versions and the journal version of the source; papers citing the source; `gh search issues --repo the-omega-institute/trureturing "<arXiv id>" --limit 10 --json number,title,createdAt` and the same with two or three distinctive words (three seconds apart; compare issue dates with 2026-10-26); a web search. The user's own publication of this result (mathdb.com/abs/2610.*, Zenodo, anything by MJ Kang or citing those) is not prior art; anything else dated before 2026-10-26 is.
2. **Statement.** Is the MathDB record the conjecture as the source prints it, and is the Lean endpoint that record (or its exact negation) with the source's definitions: no simplified object, no missing hypothesis, no vacuity, no default values doing the work? If the result resolves a narrower, later or reworded question than the record, say exactly which.
3. **Routine or trivial.** The shortest route from one published theorem or from the source's own lemmas; for a refutation, the smallest counterexample and how a plain search finds it, and whether the conjecture as printed was obviously too general (for example a statement about all C*-algebras refuted by 2 x 2 matrices: say whether the source's authors would answer "that is not what we meant").
4. **Correctness spot check.** The key step of the proof, or the witness recomputed exactly.

Verdict per result: TIER1 (survives all four), TIER2 (a correct literal refutation by an explicit counterexample that a quick search finds, not degenerate, outside any range the source tested, not the source's own example or a one-step change of it, nothing public), NOT_COUNTED (public, routine, trivial, or not the stated record: give the citation or the route), BLOCKED (name the paper and the exact question).

At most one `gh search code` call per result. Respect robots.txt (read it, including any crawl delay, before fetching from a site), paywalls, bot challenges and 403s; never work around a refusal. Do not open mathdb.com (it refuses automated clients).

## Deliverables (in your lane folder only; no git commands at all; nothing published or sent; do not start subagents; do not compile Lean; at most 3 cores; Python as `python3 -I` from inside your own folder)
- `audit.json`: list of `{"number","mathdb_ids","verdict","reason","shortest_route","statement_gap","lean_endpoint","lean_files","sources_read":[{"citation","read":"full text|abstract"}],"row_caveats":[...],"confidence"}`.
- `AUDIT.md`: a table and a paragraph per result.
Write each result as you finish it. Final message: one line per result with the verdict, the reason and your confidence.
