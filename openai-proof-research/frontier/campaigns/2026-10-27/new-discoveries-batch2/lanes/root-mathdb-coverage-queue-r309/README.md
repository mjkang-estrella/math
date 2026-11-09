# MathDB coverage and scheduling queue

This is an offline orchestration index of the immutable r307 snapshot. It creates
disjoint batches of at most 250 IDs, retaining every record regardless of its
inherited solved/open label. Missing statements, incomplete statements, and
statements labelled full have separate queues. The labels are not independently
validated source scope, difficulty estimates, or evidence of novelty.

`coverage.jsonl` gives each ID's exact frozen file and line. Every technical and
primary-body review is marked **not reconciled**: pending workers may have read
some records, but their completed evidence must be merged before crediting any
coverage. No batch is assigned here, and this index supersedes no active task.
Before assigning a batch, subtract completed record-level coverage and current
assignments. Never dispatch a proof attempt from metadata alone.

`source-url-groups.json` lets later workers share a primary-body retrieval across
records with the same source URL after removing only its page fragment. Different
versions, DOI aliases, or mirrors are not asserted equivalent. Accepted-family
IDs are flags for exact scope comparison, never blanket exclusions.

Run `build.py build`, then `build.py verify` as separate commands under the
existing helper guard. Inputs are hash-bound references to the already-frozen
r307 records, not another recursive evidence copy. The separate verifier checks
every source location, routing class, and the exact duplicate-free ID partition.
It does not perform mathematical review. No network access, child assignment,
shared ledger edit, or acceptance/count change occurs.
