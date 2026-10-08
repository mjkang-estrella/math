# H013 scheduling hypotheses: no measured gain

Native Sol /root/h010_early_dependencies initial report,2026-10-08. Root owns
integration. No experiments or edits by proposer. Novelty unverified. Baseline
must include known automorphisms, tuned adding walks, shared inversion, effective
cycle handling, coefficient-free walks and replay; see H013-collision-baseline.md.
Same hardware, total memory, workers and full-range targets. Adopt a prospective
10% COMPLETE-work reduction as a materiality gate for these implementation cards;
it is a research priority threshold, not a mathematical definition of improvement.

## A: full-record jump bucketing with one global inversion

Freeze baseline jump points S_j=u_jG+v_jQ and logical scheduling. Each round:
compute operation descriptors (jump, cycle action, exceptional flags); counting-
sort complete walker records into jump buckets; generate denominators and use
ONE inversion across ALL buckets; finish with resident jump coordinates; scatter
complete updated records back; report endpoints in original(round,walker-ID) order.
Handle identity, zero denominators and scheduled doublings, never discard them.

Record includes immutable walker/seed ID, point, logical counter, cycle phase,
saved comparison points/minimum, cap/restart state and any retained labels.
RNG draw assignment must preserve the baseline's logical order/streams, not
consume a shared stream in bucket order. Replay follows logical walks, not buckets.
Affine invariant P=AG+BQ transforms by adding(u_j,v_j), doubling both, or applying
the scalar eigenvalue of the actual canonicalizing automorphism to both labels.
Labels may remain virtual until replay as in the known baseline.

If the exact coupling above holds, ordered endpoints/stopping behavior are
unchanged for fixed parameters. Potential saving is memory/scheduling work only.
Reducing live-walker count to fit scratch changes those fixed parameters and
does NOT inherit the same-stopping argument; see independent cost preflight.
A larger jump table might reduce cycle losses, but that changes the walk and
needs an additional whole-search comparison; do not bundle it into equivalence.

Pay table construction, descriptor/count/prefix work, complete record movement,
scatter, scratch space, reduced walker capacity under fixed total memory,
exceptions, RNG assignment, reports, replay and verification. Require

    N*(c_baseline-c_bucket) > extra_setup + extra_stopping/recovery_work,

and at least10% complete saving. Primitive latency is not enough. Sorting is known
technology, not a discovery. Missing assumption: saved random jump loads outweigh
record traffic, synchronization and loss of inversion batching. Root asked
independent Astra for static traffic/capacity crossover and Sol for an exact
pass/fusion schedule BEFORE any prototype. Equal-cost cell events and physical
cache misses are distinct ledgers. No measured CPU/GPU costs are available.

Cheapest potential test: identical declared operation trace in both schedules,
all state/history movements charged, ordered outputs equal. A losing trace ends
that implementation; a winning primitive trace alone does not establish full-
solver10% gain. Actual matched complete searches would then be needed.

## B: compact only actual cycle escapes

Retain baseline check schedule and comparisons/minima. Copy-only outcomes do no
group operation; actual escapes enqueue doubling of the baseline-selected point.
Batch real additions/doublings with one shared inversion, then restore all state,
counter, RNG and endpoint order. No new walk or mixing claim.

Saving is only discarded masked arithmetic. Charge compaction/indexes, extra
traffic, mixed slope/exception paths and lost batching. Necessary gate:

    discarded_doubling_work > compaction + lost_batching + extra_traffic.

If eliminable work is less than10% of total, it cannot pass the materiality gate.
This is ordinary conditional execution where branches are cheap; relevant only
when the competent hardware baseline actually benefits from masking. Sol is
checking a scoped arithmetic ceiling, not assuming memory cost or a bottleneck.
No new implementation without a favorable complete ceiling.

## C: buffered sorted-run endpoint dictionary

Keep distinguished-point predicate and exact canonical endpoint keys. Buffer a
fixed number of records, sort/check duplicates, query old sorted runs using
Bloom probes followed by exact lookup, and merge under a fixed size schedule.
Retain same seed/length data; keep equal-key records until replay determines
useful target-coefficient difference. A fruitless collision must not erase useful
history. Final [d]G=Q verification remains required.

Charge sorting, filter construction/probes, false positives, exact lookups,
merges, seed storage, framing/backpressure, replay and delayed detection. All
memory shares the same finite budget. Paid partial flush/timeout must release
a final collision even if buffer never fills. A changed distinguished density
requires separate full restart/communication/detection accounting.

This is established database machinery, not algorithmic novelty. Proposer's
primary leads: https://www.cs.umb.edu/~poneil/lsmtree.pdf and
https://people.scs.carleton.ca/~paulv/papers/acmccs94.pdf . Specific comparisons
are unverified here. If baseline dictionary work is below10% of total, even
removing it cannot pass the gate. No measured bottleneck, so card parked.

## Current decision

A received an independent paper preflight: literal full-copy traffic loses the
equal-cost-cell ledger; hardware hierarchy advantage has no calibration. See
findings/H013-scheduling-preflight.md. No engine now. B has a necessary
savings-ceiling screen; C remains parked. None changes credible ECDLP complexity,
and no hardware multiplier, measured throughput or novelty is claimed.
