# H013 collision-search comparison baseline

2026-10-08. Root primary-source check during live independent ideation, no
experiment or implementation. Verified improvement remains NONE. This prevents
known implementation improvements being compared against an artificially weak
rho implementation. It is a starting baseline, not an exhaustive current survey.

## Independently checked source

[Bernstein--Lange--Schwabe, 2011](https://cryptojedi.org/papers/negation-20110102.pdf),
§§2–3, already describes eliminating live scalar coefficients, storing endpoint
hashes plus starting seeds, and replaying colliding walks to recover coefficients.
It treats fruitless cycles in negating walks and rotates cycle checks among
batched walks. These are established baseline capabilities.

The paper batches m inversions using one inversion and3(m-1) multiplications.
Its ordinary affine-addition batch ledger is5m-3 multiplications,m squarings,
6m subtractions and one inversion, before special/cycle work. Costs for a
particular field representation and hardware are separate. The walk/table size
trades reduced nonrandomness/cycle overhead against memory behavior; distinguished
point frequency trades server work against collision detection delay.

Root read these passages directly; native Sol independently identified the
same source. This historical paper is neither a 2026 hardware calibration nor
a proof of random-walk behavior for an arbitrary new transition rule.

## Root acceptance conditions for H013 implementation hypotheses

A pure permutation of a batch must preserve logical walker identity, state,
cycle-check phase/history, seed reconstruction and successor rules. Otherwise
unchanged collision merging/replay and success statistics cannot be assumed.
If exact trajectories ARE preserved, the possible benefit is implementation
work, not an exponent change; do not run new collision-statistics claims without
need. All reorder/scatter, scratch space, synchronization and lost walker
capacity count. One global inversion per batch is different from paying one per
jump bucket; freeze the actual schedule before evaluating it.

Restart randomness is part of that coupling: a global random stream consumed in
physical bucket order generally changes the walks. Preserve baseline logical
draw order or the baseline's independently indexed walker streams, and charge
the assignment. Restore endpoint/report/stop side effects in their original
logical order. Merely retaining a walker ID does not establish this equivalence.

Server optimizations need the fraction of total work they can affect, plus
collision detection/replay latency and exact-key verification. A filter false
negative loses a valid collision; a false positive creates paid work. Hash/key
or disk/memory claims must specify complete storage and lookup semantics.
Saving a primitive operation or CPU branch does not automatically lower total
solver work. No published AI FLOPS are converted into curve throughput.

Potential proposals remain unaccepted until exact steps, full-cost gate, primary
prior-art distinction and an inexpensive matched synthetic test are supplied.
We will not claim database batching, Montgomery inversion, lazy labels, or known
negation handling as new discoveries.
