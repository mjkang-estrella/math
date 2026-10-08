# H031 coverage/detection proposals: scoped paper screens

2026-10-08. Initial proposer native Astra `/root/h007_additive_relations`;
root mathematical check and narrower followup completed. Independent native
Sol `/root/h010_early_dependencies` algebra and scope review received; final
review summary pending. No experiment or Lean claim.
Verified complete-work improvement NONE. Three distinct initial mechanisms:
cross-start relation aggregation, cubic scalar-label schedules, compressed trail
certificates. None currently has a positive complete-work rationale.

## Cross-start relation aggregation

Fix Q=kG in a group of prime order q. Independently choose starts aG+bQ with
a uniform in Fq and b uniform in Fq (alternatively Fq*). Writing z=a+bk,
for each z,b there is exactly one a. Thus initial geometry z is independent
of b and the marginal b distribution is retained conditional on geometry.
Fix public jump data, and let geometric trajectories and selection of a
cross-start signed equality depend on geometry only. For each selected start,
assume its terminal b-label is u*b+v, where u!=0 and u,v are determined by
that geometric information. Conditional on this information, different starts'
b-labels remain independent. In the full-Fq case, their signed difference is
zero with probability1/q. Ordinary cross-start collisions are already useful
with probability1-1/q. Aggregating more relations cannot yield a material gain
merely by repairing this already small null-denominator probability.

For b uniform Fq*, u*b+v is uniform on Fq minus{v}. The two compared labels
have excluded values v1 and sigma*v2. Their support intersection has q-1
points if those agree, otherwise q-2. The null probabilities are therefore
1/(q-1) and(q-2)/(q-1)^2, respectively. C2's G-only jumps have v=0, so its
corresponding random-start model would use1/(q-1), not1/q. Its fixed LCG seeds
instantiate neither probability theorem. These are exact counting statements
under the explicit conditional independence assumptions, not walk-mixing laws.

This screen excludes same-start cycles, dependent starts, singular u=0 updates,
label-dependent selection, and choices conditioned on observed scalar recovery
or failures that reveal labels. Sharing/merging starts must preserve or reprove
the independence premise. The statement does not exclude cheaper arithmetic
batching or a new detector finding more geometric collisions. No new detector
was supplied, so no numerical test is justified by usefulness alone.

## Literal cubic schedule

P_i=iQ+i^3G, D_i=Q+(3i^2+3i+1)G, E_i=(6i+6)G, F=6G.
Using old values: P'=P+D, D'=D+E, E'=E+F. Initialize P_0=O,
D_0=Q+G and E_0=F=6G. Generic setup is two doublings and two additions.
The first P update starts at infinity and the first E update is a doubling
(E=F), so the regular formula is not a finite first-emission cost. Each later
regular emitted point requires three full affine additions. Their
three denominators all use old registers and can join one batch across n
streams, giving15M+3S+(I-3M)/n per emitted point. Identically initialized
streams duplicate outputs: useful n-way batching needs separately specified,
paid distinct starting indices/states and its own coverage reconciliation. Add storage, labels,
initialization, exceptions and verification. This is a literal recurrence
ledger; neither all cubic implementations nor finite totals are characterized.

The prior [H025 schedule screen](H025-addition-chain-screen.md) bounds a fixed
target-independent scalar-label schedule's recoverable targets by t^2+O(t)
after t inspected points, including signed collisions and direct infinity.
For a uniform full-range target, mean inspected outputs are at least
(2/3)sqrt(q)-O(1). Even one regular full addition per output has leading
arithmetic coefficient(2/3)(5+s), exceeding the high-memory paired comparator
(2sqrt(2)/3)(2.5+s) from [H019](H019-xonly-baseline-screen.md), for0<=s=S/M<=1.
After cancelling and squaring the difference is12.5-s^2>0.

Scope: the comparison uses the regular-affine arithmetic regime and the H019
square-root-memory comparator, bounded inversion ratio and controlled setup/
exceptions. No candidate exception count or exact finite total was established.
It is an unfavorable regular-operation premise, not an unconditional cost
lower bound, low-memory dismissal or wall-time theorem. A cheap multi-output
construction or different memory regime would require a new named comparison.
No new cubic experiment or formal infrastructure follows from this card.

## Compressed trail certificates

Proposal: keep compact certificates of walk segments, detect intersections
without retaining every point, then recover labels. Missing primitive: a paid
query detecting an interior intersection between certificates more cheaply
than scanning/rebuilding the segments. Endpoint equality reduces to the known
distinguished-point/replay comparator. The proposal has no supplied gain,
not an impossibility proof. Cheapest decisive step is specifying that interior
query and its complete storage/construction/recovery cost; no pilot admitted.

## Evidence and process

All new equations are paper derivations, not current-literature novelty claims.
H019 contains the previously read primary-source comparator and its limitations.
No new source fetched, program run, seed searched or hidden table constructed.
Root required the cubic recurrence ledger before retaining the proposed rejection,
and corrected the full-Fq probability to the separate Fq* case relevant to C2.
Sol independently confirmed the label-support count and recurrence/batching
algebra, while requiring geometry-only conditioning before denominator outcomes,
paid distinct stream initialization, and exceptional first emissions. These
corrections are incorporated above. No audit-count progress claim.
