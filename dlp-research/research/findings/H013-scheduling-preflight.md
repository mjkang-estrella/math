# H013 literal bucketing cost preflight

2026-10-08. Native Sol proposer; independent Astra
/root/h007_additive_relations reviewed costs; root checked equations and scope.
No implementation, numerical run, hardware calibration or verified improvement.

Let b walkers, complete record R bytes, additional descriptor d bytes, original
inversion scratch s per walker, histogram H, available capacity C, U occupied
jump buckets and J bytes of baseline jump coordinates loaded per step.
For LITERAL separate materialized passes, counting-sort copies read/write2bR
bytes; scattering finished records reads/writes another2bR. This is nominal
extra4R bytes/step beyond the common arithmetic accesses, before histogram,
descriptor, offsets and bucket work. Perfect bucket residency saves at most
J*(1-U/b) jump-coordinate bytes/step. R already includes two point coordinates
plus history and control. In the equal-width, equal-cost cell model, added
record traffic exceeds saved coordinate accesses. Thus this literal schedule
loses that ledger before counting sorting overhead.

This is NOT a measured timing lower bound. Cache-line misses, write allocation,
broadcast and memory levels have different costs. Fused finish/scatter can
replace some baseline writes and needs a new exact delta ledger. Lightweight
descriptor-only bucketing also differs from literal full-record copying. No
alternative is silently credited with the old card's invariance or saving.

Ignoring floors, fixed memory gives

    b0=C/(R+s),   b1=(C-H)/(2R+s+d).

IDs already included in R are not counted twice. From the independently checked
BLS ordinary affine batch ledger, the batch-dependent per-step arithmetic delta
is (I-3M)*(1/b1-1/b0), with I inversion and M multiplication cost. It is a
penalty only when I>3M; no uncalibrated hardware ratio is assumed. Exceptional
paths, masks, squarings, subtractions and control still belong in the full ledger.

For complete baseline cost C0 and W walk steps, measured removable scheduling
work S per step, replacement penalty P and setup/end difference A, a10% gain
requires W*(S-P)-A>=0.1*C0. An optimistic first screen removes ALL jump-selection/
load overhead with zero replacement cost. If even that cannot reach10%, no
prototype is warranted. There is currently no competent-kernel bottleneck
measurement or derived bound making this screen pass.

Under exact equal logical walks, permutation preserves point/label transitions
and ordered endpoint side effects ONLY if phase/history, RNG assignments,
restart decisions and stop order are also preserved. Reducing the number of
live walkers under fixed memory changes endpoint timing and possibly stopping
work; the same-individual-trajectory argument does not settle that. A fixed
transcript processed in smaller microbatches isolates kernel work and exposes
extra inversions, but does not by itself compare complete solvers. Storing all
original logical walkers elsewhere consumes paid memory and cannot bypass C.

Candidate B (actual-escape compaction) and C (buffered endpoint runs) similarly
require their removable baseline fractions to exceed10%, before replacement
overhead. This is a necessary saving ceiling, not a new attack.

Root decision: no full-record bucketing engine or large baseline build now.
Retain the card for a concrete existing-kernel bottleneck ledger or independently
justified hardware case. Do not invent memory multipliers, measured throughput,
or new finite curves merely to manufacture a positive primitive benchmark.
Broader H013 coordinate/algebra/information roles remain separate and live.

## Proposer's completed fusion audit and B ceiling

Sol returned an exact matched layout. If baseline preparation reads R and its
finish reads/writes R, baseline traffic is3R. Let classification read aR per
walker (a=1 for full-record classification; projected reads need explicit fields).
The separate candidate passes cost(7+a)R. Fusing denominator preparation into
copy-sort removes one R read: (6+a)R. Finishing arithmetic directly into original
slots removes a sorted-output write and later scatter read: (4+a)R. Therefore
this specific fully fused variant still adds(1+a)R relative to baseline.
With equal field widths R>=J and a>=0, this exceeds J*(1-U/b), even before
histogram/descriptor costs. This extends the raw-cell-traffic rejection to the
specified fusion, NOT every descriptor-only or in-place permutation algorithm.
Hierarchy-dependent runtime remains uncalibrated. Fusion does not automatically
remove the second record buffer or its batch-capacity penalty. Root checked the
pass arithmetic; common baseline layouts must not be changed mid-comparison.

For B, use only the named BLS-style schedule with one check replacing an
addition each48 positions, and batched arithmetic D=A+S<=2A. Even if every
scheduled doubling were discarded, removed arithmetic fraction is at most
D/(47A+D)<=2/49. Including checks each49152 positions bounds their fraction by
f=1/48+1/49152, hence arithmetic saving <=2f/(1+f)=2050/50177<4.1%.
Actual required escapes reduce this ceiling. Other configured checks need to
be added. This is an ARITHMETIC ceiling under the specified ledger, not an
independent10% complete-work impossibility: memory/scheduling weights remain
separate and compaction itself costs work. No hardware measurements invented.

All native scheduling proposal/preflight roles are now completed. No further
implementation or engine round authorized for these cards absent new evidence.
