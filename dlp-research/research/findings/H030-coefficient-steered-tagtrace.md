# H030 C2: coefficient-steered tracing, scoped algebra accepted

2026-10-08. Factory Opus proposed amendment after reviewing C1. Root derived
the ledger; native Sol independently confirmed logical transition, exceptions
and operation counts. No implementation/experiment/Lean claim or verified gain.
C1 signed table and Miller bootstrap requirements remain fully applicable.

Use canonical h for BOTH partition and reporting predicate. Keep exact point
keys for reports/recovery. With S=epsilon(P0+K), choose J from canonical h(S),
update K'=K+epsilon*J, and compute only

    lambda=(y(K')-y(P0))/(x(K')-x(P0)),
    H=h(P0)+h(K')-lambda.

Sign selection gives S'=can_h(S+J), as in C1. Different refresh boundaries do
not change this logical successor if dispatch preserves it. Noninjectivity of h
is harmless for the partition, not for claiming point equality.

## Exact regular ledger, before mandatory control

Partial slope/H costs I+M+4A. Full refresh additionally computes x and y,
costing I+2M+S+8A in total. Against tau ordinary affine additions, ideal credit is

    (tau-1)(M+S)+(2tau-4)A.

For n simultaneous regular slopes, average arithmetic is

    (4+1/tau)M + S/tau + (I-3M)/n + (4+4/tau)A.

This is a larger concrete arithmetic ceiling than C1, not a solver speedup.
Canonical nonzero h must now actually feed the selector/predicate, so C1's
deferred negation cannot be carried over as free. Specify field reduction,
comparison, selection and index operations.

At a report, recover x=lambda²-x(P0)-x(K') for S+2A; retain its canonical
integer representation for exact negation-class lookup. Canonicalized point
labels and actual verification are still required. At zero H, computing y adds
M+2A after x; identity and exceptions have separate dispatch. If reporting and
refresh coincide, share already-performed arithmetic rather than double charging.

An h-repeat in cycle history is only a filter. Exact x comparison requires old
coordinates or retained origin/slope descriptors. False screens, reconstruction,
history capacity, cycle escapes and retries all count. No global fibre bound
has been converted to an actual visited exception/repeat rate.

Origin/table identity, tangent and vertical pairs need complete formulas and
costs. Signed table construction, indexes/pointers, Miller bootstrap, starts,
lookup/storage, scalar recovery and failed attempts remain paid. Existing BLS
representative/partition statistics are not this map's stopping law.

## Applicability and next gate

H030-miller-automorphism-covariance.md extends orientation to rational order-six
curves with extra unit operations and a larger formal table. Point labels use
the subgroup eigenvalue and cumulative K updates use the inverse unit. Ordinary
negation and six-unit cases must each compare against the corresponding competent
baseline; no repeated credit for known automorphism gains.

C2 is the current highest-priority incomplete arithmetic hypothesis. Next: one
explicit paid layout and cycle/detection contract, with symbolic break-even
conditions or a justified implementation cost model. Then a bounded synthetic
falsifier can test correctness and actual useful-hit work. It must not exploit
structured scalars, free precomputation or an easier detector in the candidate.
No broad Lean machine infrastructure and no numerical run admitted yet.
