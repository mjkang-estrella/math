# Candidate review brief, round 2 (root Claude Fable 5.2, 2026-11-19 evening)

C = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31`

Read `C/root-intake-r60/FABLE-PIPELINE.md` (step 1 is your job), `C/root-intake-r60/FABLE-DISCOVERY-BRIEF.md` and `C/public-claim-100/BRIEF-C-DISCOVERY-ADDENDUM.md` (prior-art sources, including the sections added at its end).

Each assigned candidate was claimed by another lane; your task names the proof file (scripts and REPORT.md are beside it). It is wanted for a public list of "open MathDB problems solved by AI, each with a kernel-checked Lean proof". You did not write it and you are the adversary: your job is to find the reason it should not be on that list. Root (a different model) reads your review and re-checks the cheap parts. Also read `C/public-claim-100/BRIEF-C2-DISCOVERY-ROUND2.md` for what counts: PASS and SEARCH_EASY both count; everything else does not. Record text: `python3 C/root-intake-r60/corpus_row.py <id>`.

For each candidate, in this order, and stop early when a test fails:
1. Archives and prior art: `C/public-claim-100/principia-ids.txt` and the two clones (Principia, mio-qwq), neighbouring ids from the same source paper, later arXiv versions of the source and its journal version, citing papers, ProbXiv, the omega and openai/math registries. The GitHub API quota is shared and tight: at most two `gh search` calls per candidate.
2. Fidelity: MathDB record versus the conjecture as printed in the source versus the theorem claimed. A record that mis-transcribes the source is RECORD_DEFECT.
3. Smallest case and shortest route, by your own computation from the source definitions:
   - refutation: find the smallest counterexample; what did the source authors check; does a generic search find one in seconds or minutes at the first unchecked size (then SEARCH_EASY); is the witness degenerate, or inside the source's tested range, or one of the source's own examples (then TRIVIAL)?
   - proof: the shortest proof from published theorems and the source's own lemmas; a few lines from one of them is ROUTINE.
4. Correctness of every step, with independent computation.
5. The exact literal Lean endpoint you would require (all definitions included), the cheapest kernel-checkable route without native_decide, estimated lines and the riskiest step.

Verdict per candidate: PASS (no flag), SEARCH_EASY (correct, literal, new, non-degenerate, but an easy computer search at the first unchecked size), FAIL (first gap), PUBLIC, ROUTINE, TRIVIAL, RECORD_DEFECT or BLOCKED (name the source and the question).

Deliverables in your lane folder only (no git; nothing published or sent; respect site refusals; do not start subagents): `REVIEW-<id>.md` written as soon as that candidate is done, each with the verdict and a line `FLAGS: none | list`; `result.json` with a list of `{"mathdb_id","verdict","flags","correctness","novelty","smallest_case_or_shortest_route","would_specialist_call_routine","lean_endpoint_required","lean_estimate_lines"}`. Final message: one line per candidate with verdict, flags and the required Lean endpoint.


For SEARCH_EASY be strict on the conditions, because that verdict now counts: say exactly what range the source tested (quote it), why the witness is not degenerate and not a boundary case, and why it is not one of the source's own examples. When in doubt between SEARCH_EASY and TRIVIAL, say TRIVIAL and give the reason.


## Added 2026-11-20: the omega registry posts through GitHub issues
A result was lost because it had been refuted two hours earlier in an issue of the public repository `the-omega-institute/trureturing`. Neither the local clone nor `gh search code` shows issues. For every candidate run `gh search issues --repo the-omega-institute/trureturing "<arXiv id of the source>" --limit 10 --json number,title,createdAt` and the same with two or three distinctive words of the conjecture (authors, the named object), and read any hit with `gh issue view <n> --repo the-omega-institute/trureturing`. These calls are in addition to the `gh search` allowance above; wait three seconds between calls (the search limit is 30 per minute, shared).


## Added 2026-11-20: journal texts a publisher refuses
If the only open point is a journal text that a publisher refuses, do not stop at BLOCKED. Give the verdict the mathematics deserves, add the flag JOURNAL_TEXT_UNREAD, and report the open evidence on which arXiv version is the accepted text (arXiv version dates against the journal's received, accepted and published dates; whether the latest arXiv version thanks referees or notes acceptance; whether the journal abstract matches). Root decides on that evidence.
