# Cross-model confirmation brief, round 2 (root Claude Fable 5.2, 2026-11-19)

C = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31`

## Why
The user wants to say in public that AI resolved 100 conjectures listed as open on MathDB, each with a kernel-checked Lean proof. The list has two counted tiers. Tier 1: a proof or refutation a specialist would not call routine. Tier 2: a correct, literal refutation by an explicit counterexample that a computer search finds quickly, where the MathDB record states the conjecture as the source prints it, the witness is not degenerate or a boundary case, it is not inside a range the source says it tested, it is not one of the source's own examples or a small change to one, and nothing public already has it.

In round 2 every lane (discovery, review, Lean, final check) is GPT-6.1 Sol. You are the other model. For each result assigned to you the Lean packet is complete and root has rebuilt it; a Sol review and a Sol final check have passed it. Your job is the view a different model brings: is this really countable, and does the Lean statement say what the source says. A wrong CONFIRMED costs far more than a wrong downgrade. In this round two of the first four results that reached this stage were downgraded.

## Per assigned id (about 25 minutes each; more only where it is close)
Inputs are named in your task: the packet (PAPER, LEAN-SOURCE-APPENDIX.md, REPORT.md), the Sol review and the Sol final check with its revised paper. Record text: `python3 -I C/root-intake-r60/corpus_row.py <id>` run from your own folder. Do not compile Lean.

Test in this order and stop at the first failure:
1. **Public.** `C/public-claim-100/principia-ids.txt`; the Principia clone at `/tmp/claude-1000/-home-mj-kang-Documents-Dev-math/75a48aa2-847d-4c84-96d4-c7a2d5bb5b22/scratchpad/shared/principia` (also sibling ids from the same paper); the journal version and later versions of the source; the most obvious later papers and anything citing the source. Do your own search; do not rely on the Sol lanes' lists.
2. **Statement.** Read the final endpoint and every definition it uses in LEAN-SOURCE-APPENDIX.md against the source's definitions. Name any gap: a simplified object, a missing hypothesis, vacuity, default values doing the work.
3. **Routine or trivial.** The shortest route from one published theorem or from the source's own lemmas, tables and examples; the smallest counterexample and how a generic search finds it; whether the source's authors would say "that is not what we meant".
4. **Verdict:** CONFIRMED_TIER1, CONFIRMED_TIER2 (meets every tier-2 condition above), NOT_COUNTED (public, routine, trivial, degenerate, the source's own example, or not the stated problem; give the citation or the route), or BLOCKED (name the paper and the exact question).

At most one `gh search` call per result. Respect robots.txt, paywalls, bot challenges and 403s; never work around a refusal. Computation is allowed; keep scripts in `scripts/`; run Python as `python3 -I` from inside your own folder.

## Deliverables (in your lane folder only; no git; nothing published or sent; do not start subagents)
- `confirm.json`: list of `{"mathdb_id","verdict","real_content_or_reason","shortest_route","statement_gap","sources_read":[{"citation","read":"full text|abstract"}],"row_caveats":[...],"confidence"}`.
- `CONFIRM.md`: a table (id, verdict, one line) and a paragraph per result.
Write each result as you finish it. Final message: one line per result with the verdict, the reason and your confidence.


## Added 2026-11-20: the omega registry posts through GitHub issues
A result was lost because it had been refuted two hours earlier in an issue of the public repository `the-omega-institute/trureturing`. Neither the local clone nor `gh search code` shows issues. For every candidate run `gh search issues --repo the-omega-institute/trureturing "<arXiv id of the source>" --limit 10 --json number,title,createdAt` and the same with two or three distinctive words of the conjecture (authors, the named object), and read any hit with `gh issue view <n> --repo the-omega-institute/trureturing`. These calls are in addition to the `gh search` allowance above; wait three seconds between calls (the search limit is 30 per minute, shared).
