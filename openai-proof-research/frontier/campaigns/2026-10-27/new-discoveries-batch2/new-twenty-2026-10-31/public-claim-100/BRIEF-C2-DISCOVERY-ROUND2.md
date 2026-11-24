# Discovery round 2 for the public list (root Claude Fable 5.2, 2026-11-19 evening)

C = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31`

Read `C/root-intake-r60/FABLE-DISCOVERY-BRIEF.md` first (goal, method, rules, deliverables), then `C/public-claim-100/BRIEF-C-DISCOVERY-ADDENDUM.md` for the prior-art sources and local clones. This file changes what counts.

## What counts in this round

The list needs 18 more results. Two kinds count:

- **Tier 1**: a proof or refutation of the literal statement that a specialist would not call routine.
- **Tier 2**: a correct refutation of the literal statement by an explicit counterexample that a computer search finds quickly, provided all of these hold: the MathDB record states the conjecture as the source prints it; the witness is not degenerate (not an empty or one-element case, not a boundary index, not a disconnected or zero-weight case the authors plainly did not mean); it lies outside the range the source says it checked; it is not one of the source's own examples or a small change to one; nothing public already has it. Report these as SOLVED with `FLAGS: SEARCH_EASY`. Do not mark them TRIVIAL.

Still worth nothing here, so do not spend time on them beyond one line in the report: PUBLIC; ROUTINE (a few lines from a published theorem or from the source's own lemmas, tables or recurrences); TRIVIAL (degenerate case, misprint, mis-scaled statement, failure inside the source's tested range or at a case its own data contradicts); RECORD_DEFECT (the record does not say what the source says); partial results.

## How to spend the time

1. Triage all 60 rows quickly. Mark every row whose statement is finitely checkable: a universal claim over graphs, posets, words, permutations, partitions, matrices, codes, sequences or integers with a formula, bound or classification.
2. For every such row, read the source's definitions and what range it tested, then run a real counterexample search past that range (exhaustive where possible, otherwise random and structured families, SAT or ILP if useful). Most tier-2 results come from this step. Keep the scripts and record the range you covered when nothing is found.
3. Give the two or three most promising remaining rows a sustained proof attempt.
4. Before you write a proof file, do the prior-art checks in the addendum (Principia archive by id and by source arXiv id, mio-qwq clone, omega and openai/math registries, later versions and the journal version of the source, citing papers, ProbXiv). At most two `gh search` calls per candidate; the quota is shared.

Lean cost matters. For a refutation, state in PROOF-<id>.md the exact finite certificate a Lean kernel could check without `native_decide` (the witness, the quantities to evaluate, their sizes). A counterexample whose check needs an enormous enumeration should say so.

In REPORT.md give each SOLVED item a line `FLAGS: none`, `FLAGS: SEARCH_EASY` or the list of other flags, and one line on what range the source tested.
