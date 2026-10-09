# H035 exact stopped-chain expectation

Status: independently reviewed PAPER theorem under the stated table contract.
No new execution, Lean claim, hardware price or complete ECDLP improvement.
Native Astra /root/h007_additive_relations derived/reviewed the formula at root's
request; root checked the terminal indexing and conditioning scope. This sharpens
the earlier leading-only false-probe calculation without a new experiment.

## Hash-independent trace contract

Condition on a complete trace T containing targets, labels, exact geometric
keys, insertion order, recovery decisions and independent fallback shifts, but
NOT bucket locations or probe histories. Require that this trace is independent
of the sampled square multiplier u² and shift -2r. Tables prepend new records
and scan newest first, stopping on the FIRST exact match or chain exhaustion.
No occupancy-dependent reordering, resizing, cap, rehashing or selection occurs.
Exact comparison uses an injective field key. Record duplicates are allowed.

For each query j, define A_j from its destination table's insertion history:
if no exact match exists, include all stored records; otherwise include only
records newer than the NEWEST exact match. All records in A_j have unequal
geometric keys. Pathwise, false probes are exactly

    sum_j sum_{i in A_j} 1[bucket(key_i)=bucket(query_j)].

The true-match probe, if present, is deterministic from the trace. This is true
also for the terminal partial chain: older bucket-colliding records are never
visited after the newest match. No independence among comparisons is required.

For p=3 mod4 and L=u²*x-2r, the earlier reversal argument gives, for ANY fixed
distinct pair, collision probability

    beta(p,H)=[H*a*(a-1)+2*v*a]/[p*(p-1)],  p=a*H+v.

Therefore linearity of expectation yields the EXACT finite identity

    E[false probes | T] = sum_j beta(p,H_j)*|A_j|.

Reuse of hash parameters across tables, phases or head counts does not break
this identity. It only requires the stated trace independence and pair law.

## Terminal candidate and split-role examples

For a single archive with no earlier equal key, T inspected keys ending at its
first equality, and matching predecessor insertion position j* in1..T-1,

    E[false probes | trace] = beta(p,H)*(choose(T,2)-j*).

Indeed queries before the last contribute choose(T-1,2) eligible records; the
last contributes T-1-j*. A collision-free capped prefix instead contributes
beta(p,H)*choose(T,2). The true-match count is respectively1 and0.

For H019, A_j contains only the opposite-role records. Duplicates are counted
with multiplicity and the latest exact match still determines the cutoff.
Seed scans, geometry-first null recovery and fresh blinded fallback can be
included by summing phase/table queries. Recovery must not skip a matching
record according to its coefficient and then search for another relation.

## What this does not establish

The H034 experiment's event cap depends on actual probe work. Conditioning on
successful completion beneath that cap destroys the independent-trace premise.
The identity does NOT apply to the observed censored trace or completed cases
selected by that resource guard. A pure prefix cut off by resources is only
pathwise bounded by the full uncensored trace. No reinterpretation or rerun of
the retained diagnostic follows from this theorem.

Fixed-price node reads, comparisons, next-pointer reads and loop operations can
be priced from this identity plus deterministic insertion/query/exhaustion
counts. Variable-limb comparisons, cache behavior, allocator policies, races,
hash-driven walks or occupancy-dependent branches need additional analysis.
The identity does not couple physical cache trajectories between hash families.
Complete coordinate setup, field arithmetic, full-point updates and capacities
remain separate costs. Fixed PRNG streams are not independent uniform randomness.
No universal dominance over a word hash or raw coordinate-bit table follows.
