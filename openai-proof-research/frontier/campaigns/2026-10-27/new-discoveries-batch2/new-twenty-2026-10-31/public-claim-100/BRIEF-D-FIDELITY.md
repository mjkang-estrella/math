# Row fidelity audit brief (public-claim follow-up, root Claude Fable 5.2, 2026-11-19)

C = `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31`

## Why
The user wants to say in public: "I let AI solve 100 open math problems from MathDB, each with a kernel-checked Lean proof." Every row of the public list must state exactly what was proved or refuted and how that relates to the MathDB record. This lane does that for results that were not flagged as close calls. It works from local files only (no web search needed; a source paper on arXiv may be opened when the local files leave the conjecture's wording unclear).

## Per assigned id
Inputs: the row in `C/public-claim-100/base-rows.json` (MathDB record statement from the corpus, endpoints, acceptance file, submission folder); the acceptance record; `C/mathdb-submissions/<id>-*/SUBMISSION.md` and the paper (PAPER.md or manuscript); the Lean source (the endpoint theorem statement and the definitions it uses; in LEAN-SOURCE-APPENDIX.md, the `lean/` directory or proof-packet.zip, which you may unzip into your lane folder); fidelity and significance reviews named in the acceptance record.

Decide and record:
1. `row_statement`: one or two exact sentences of what the kernel-checked endpoint says (quantifiers, ranges, objects), in plain mathematical English.
2. `relation` of the Lean endpoint to the MathDB record text, one of:
   - LITERAL: the record's statement, or its exact negation, with the record's quantifiers and scope;
   - LITERAL_STRONGER: implies the record's statement or its negation;
   - SOURCE_NOT_RECORD: matches the conjecture as printed in the source, but the MathDB record text differs from the source in a way that matters (say how);
   - PART_ONLY: resolves only part of a multi-part record (say which part, and whether refuting that part refutes the record's conjunction);
   - READING: depends on choosing one reading of an ambiguous statement (say which, and whether other readings were also handled).
3. `lean_vs_paper`: what is kernel-checked and what is proved only in the written paper.
4. `recorded_caveats`: every caveat, limit or doubt the acceptance record and reviews already state (significance called modest or close, routine risk, intended versus literal scope, degenerate cases, unread sources), quoted briefly with the file it is in.
5. `degenerate_check`: is the refutation or proof carried by a degenerate object (empty or edgeless graph, n = 0 or 1, a typo in the printed conjecture, a hypothesis the source obviously intended)? yes/no with reason.
6. `recommendation`: CLEAN (a careful reader would accept "this MathDB problem was solved" with at most a wording note) or NEEDS_ADJUDICATION (name the doubt in one sentence). Be strict: when unsure, NEEDS_ADJUDICATION.

Do not re-prove the mathematics and do not redo prior-art search; other lanes do that. Do read the actual Lean endpoint statement rather than trusting summaries.

## Deliverables (in your lane folder only; no git; nothing published or sent)
- `fidelity.json`: list of `{"mathdb_id", "row_statement", "outcome", "relation", "relation_note", "lean_endpoints", "lean_vs_paper", "recorded_caveats":[...], "degenerate_check", "recommendation", "doubt"}`.
- `FIDELITY.md`: a table (id, outcome, relation, recommendation, one-line note) followed by a short paragraph for every NEEDS_ADJUDICATION item.
Write results as you go. Final message: counts per relation and the list of NEEDS_ADJUDICATION ids with the doubt in one sentence each.
