# Merged record coverage

This sparse overlay updates the immutable r309 corpus partition with completed
r302/r303 record-review reports and the r312/r313/r314 dispatch reservations.
Assignments are recorded allocations, not a live worker-status monitor. Old
snapshots and worker artifacts remain unchanged. Later completed handbacks must
be reconciled before extending this overlay.

The 83 record-review IDs are delegate-reported activity, including flagged
garbling and uncertain source scope. They are not 83 primary-body reviews.
`reported_complete` means that record-review activity was handed back, not that
the statement is authoritative or complete. Only 371202 has a reported partial
primary read; none has a complete source/prior clearance in these handbacks.

Every snapshot ID belongs to one disjoint shard. Unreviewed assigned records are
separated from unreviewed unassigned records. `shard-state.json` supplies exact
remaining IDs for future breadth allocations. Scores, prior dispositions, and
accepted-family associations remain subject to literal-scope adjudication.

Run `merge.py build` and then `merge.py verify` in separate helper-guarded
processes. Reuse hash-checked immutable inputs by reference; no recursive copies,
network retrieval, mathematical solving, or acceptance/count edits occur.
