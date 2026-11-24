# Candidate review brief (replacements for the public list; root Claude Fable 5.2, 2026-11-19)

C = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31`

Read `C/root-intake-r60/FABLE-PIPELINE.md` (step 1 is your job), `C/root-intake-r60/FABLE-DISCOVERY-BRIEF.md` and `C/public-claim-100/BRIEF-C-DISCOVERY-ADDENDUM.md` (prior-art sources, including the sections added at its end).

Each assigned candidate was claimed by GPT-6.2 Sol in `C/fresh-shard<NNN>-discovery-sol62-20261119-r1/PROOF-<id>.md` (scripts and REPORT.md beside it). It is wanted for a public list of "open MathDB problems solved by AI, each with a kernel-checked Lean proof". You are the adversary. Record text: `python3 C/root-intake-r60/corpus_row.py <id>`.

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
