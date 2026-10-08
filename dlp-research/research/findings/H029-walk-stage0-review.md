# H029 clocked walk repair: Stage0 not passed

2026-10-08. Grok's completed task/report retained in H029-walk-repair-grok-raw.md.
Native Astra independently reviewed mathematics/detection; root checked H023
formulas and finite-batch accounting. Separate native Sol cost/protocol review
confirmed the finite-batch and experiment objections, and found the structured
target bias below. No experiment, import, instance or Lean theorem. Verified
improvement NONE.

## Valid algebra, unsupported detection

R1 applies translation then reflection to UPDATED labels when sorting swaps:
(a,b)->(a+1,b)->(1-(a+1),-b). Doubling plus a fixed representative convention
is also defined. It is not intrinsic doubling on a reflection class without
that convention. At clock boundaries the regular map is D_can composed F^31.
This is a well-defined object to analyze, not a proved mixing law. Once F reaches
its accepted regular two-cycle, repeated fill pairs reuse both state and labels.
Clocking eventually changes the operation; it does not make wasted fills fresh.

The global-clock argument is false for cross-time intersections. Simultaneous
equal states coalesce, but an arrival at a previously visited point may have a
different clock phase from its earlier visit. Their subsequent schedules then
differ. Stored equalities may still immediately recover a verified scalar; an
unreported equality need not propagate to a common distinguished point. Hence
no automatic additive distinguished-point delay has been established.
Phase-tagged or boundary-only detection would change the contract and need its
own useful-collision/cost argument. Our iid landing model does NOT apply here.

Shared null-hit restart conflicts with R1's fill-cycle exemption unless the
report specifies whether the latter covers DP hits or only the ring. Same-walker
table hits also need a defined retirement rule. Capping and refusing new records
changes detection coverage; fallback charges loss but does not prove a success law.

## Finite-batch correction

R1's two doubling denominators are available together, so the H023 batch of2n
denominators is valid:11M+3S+(I-3M)/n, outside additions/dispatch.
R2's second addition depends on the first result, requiring two successive
inversion batches for the literal implementation:

    mixer =13M+2S+2(I-3M)/n.

For fixed n across a32-step block the remainder is(33/32)(I-3M)/n, not one
remainder. If active batch sizes change, charge each actual batch separately.
An explicitly DIFFERENT regular kernel can omit the second output ordinate:
its needed state is only(x(P+J),x(P+J-G)). This saves1M, yielding

    x-terminal mixer =12M+2S+2(I-3M)/n.

It repairs kernel arithmetic only. No complete-work headroom follows without
the operation/query/label/memory and useful-collision ledger.

## Proposed experiments not admitted

Six-word DP records do not count32 active states,64-entry rings per walker,
jump table, scratch, labels and other metadata. All must enter matched memory.
The cited leading BLS heuristic is not a complete implementation of baseline
or fallback; starts, jump tables, cycle policy and actual work need specification.
The comparator need not build unused fixed-difference pairs. Nor is pricing
each scalar-verification doubling as one comparator addition automatically a
conservative bound: use the actual formulas. Field additions, comparisons,
label arithmetic, table accesses, stalls and failed/fallback work remain paid.
The32 rings of64 two-field keys alone occupy4096 field words, before labels or
indices for meaningful repeated-state tests. Endpoint capacity is not total RAM.
A full-state dictionary with no DP wait changes both detector and memory regime.
It could diagnose algebra/dynamics but cannot validate this low-memory claim.
One Q=floor(q/3)G per curve does not sample full-range expected work; fixed public
parameters do not cure that selection problem. More specifically, for prime
q>3 write q=3k+r with k=floor(q/3) and r in{1,2}. Then3Q=-rG. The proposed
starts P_i=(i+1)Q satisfy P_(i+3)=P_i-rG. Consequently R2's +G fill trajectories
from these starts meet across times after only one/two translations. A full-state
dictionary can detect those meetings before any clocked jump. This target
choice structurally favors exactly the tested fill direction; it cannot support
a full-range performance premise even when scalar verification succeeds.

There is another scale problem: at m=L=32, the31 all-active fill rounds before
the first mixer alone cost31*32*5=4960 leading M. Near q=2^15 the proposed
global heuristic cap is around930M at s=.8, before setup. Under unchanged active
population it stops long before the mixer. Early detections/retirements change
the schedule but do not turn this into a test of the stated long-run mechanism.
Q=O also needs explicit trivial-target dispatch. Discovery/setup/caps remain paid.

No exact universal impossibility is claimed for clocked maps. However Stage0
has failed to establish the report's claimed complete contracts. Before any
numerical admission: freeze phase-aware detection, resolve null-hit policy,
specify baseline/fallback, correct finite batches and count total memory. Only
then choose a bounded test that could change the complete-work conclusion.
