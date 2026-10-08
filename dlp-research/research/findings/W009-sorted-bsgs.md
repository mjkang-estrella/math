# W009: sorted BSGS correctness and accumulated query bounds

Date: 2026-10-07. Status: implementation independently accepted; integrated
validation recorded below and in STATE.md. No total-work or faster-algorithm claim.
Predecessor commits: 9667d72 generic linear BSGS, 97ebd5c coordinate keys/design.

## Question and result

Can the reviewed array lookup replace linear lookup while preserving actual
forward scalar payloads through sorting, including duplicate babies at m>q,
and can executed query counters be accumulated in the actual solver?

Yes: SortedBabies.lean prepares a fresh table, and SortedBSGS.lean proves
correct recovery for every orbit scalar at every positive width. The input is
only an arithmetic/key refinement, public width and target point. Neither
solver receives a secret scalar or precomputed inverse table. This is the
conventional method; no novel attack or exponent improvement is claimed.

## Implementation

Coordinator-owned SortedBabies.lean uses the reviewed IndexedLookup.Entry.
`prepare` computes buildBabies once, maps coordinate keys to cached entries,
converts to Array and calls library mergeSort ordered by key alone. It retains
the same construction's final mG. Twelve public theorems establish size,
final point, membership/permutation consequences, genuine baby indices, every
baby's presence, pairwise/indexed sortedness, query completeness and modular
recovery from a matching payload. Payload and sorted array location differ.
Equal keys may retain different payloads; any matching one recovers modulo q.

SortedBSGS.lean contains the actual giant loop. It negates prepared.final,
starts at the target, queries the cached array, and uses A.add after absence.
Lookup's exhausted outcome is handled defensively but proved unreachable by
its wrapper theorem. The loop can compute one unused final giant on failure;
no excluded work is silently counted. It returns answer plus sums of queries,
probes and comparisonCalls from the actual lookup results.

For B=(q-1)/m+1 and F(m)=0 when m=0, otherwise log2(m)+1, the four generic
public theorems prove search correctness, solve correctness and:

- queries <= B;
- probes <= B*F(m);
- equality-plus-ordering calls <= B*(2*F(m)).

The counter bounds hold for arbitrary targets/widths. Correctness requires
positive width and an orbit target. This distinction does not authorize a
width-zero solver or off-orbit validation claim. No q-primality or gcd premise.

## Cost scope

Every invocation performs fresh baby construction, key generation, conversion
and sorting, but their costs are NOT in the query counters. Generator evaluation,
all group/field arithmetic, key generation for giants, scalar/control/bit work,
allocation/copying, reference counting, physical array access and peak memory
also remain unpriced. Array.mergeSort carries no proved two-buffer bound here.
The logarithmic query bound is not a complete efficient-baseline result, a
RAM/tape bound, calibrated speed or exponent claim. W010 considers a separate
full-cost interpreter; its proposal is not yet adopted.

## Validation and failed attempts

Initial SortedBabies generic proofs compiled on the first attempt. Two attempts
to add reduction-based `decide +kernel` array-sort edge checks got stuck in
Decidable reduction, including after the proved array/list merge-sort rewrite.
The retained `smallCurve_edges` is explicitly derived from generic theorems,
not advertised as execution. This does not weaken the generic obligations.
Actual compiled execution is checked separately below.

Initial SortedBSGS correctness proofs compiled. Aggregate counter arithmetic
initially failed because normalization produced fuel*(F+F) in one expression
and fuel*(2*F) in another; normalizing both hypotheses and goal fixed it. No
algorithm counterexample or timeout occurred. Final standalone commands passed:

```
timeout 60 ./scripts/lake.sh env lean Research/SortedBabies.lean
timeout 60 ./scripts/lake.sh env lean Research/SortedBSGS.lean
./scripts/lake.sh build Research.SortedBSGS
timeout 60 ./scripts/lake.sh env lean scripts/sorted_bsgs_checks.lean > research/findings/W009-sorted-results.txt
```

The durable script executes the actual compiled solver, tests every scalar
0..6 for each width 1,3,7,8, verifies answers and query bounds, and fails with
an IO error on mismatch. All 28 cases passed. Maxima (queries, probes, comparison
calls) were (7,7,13), (3,6,11), (1,3,5), (1,3,5), respectively. These are per-field
maxima, not a sum measuring worst-case total work. They make no claim about the
other four Python curves or cryptographic-sized instances. Native evaluation
is experimental evidence, never a proof-producing escape hatch.

## Independent reviews

Native Astra separately reviewed the frozen adapter and frozen full solver.
Adapter PASS: clean compile and all 12 public axiom checks, preservation of
actual baby payloads, correct total-preorder sortedness, matching-key recovery,
no hidden input/table or cost assumptions. Its edge-specialization description
was accepted; compiled execution requested separately and supplied.

Full solver PASS: clean compile and all four public axiom checks; all positive
widths including m>q and order one handled. Counters follow actual lookup calls
and retain stated exclusions. Reviewer reproduced the exact 28-case maxima.
One reviewer command mistakenly supplied --run to the #eval-only script,
executed its checks and then failed for missing main; the corrected command
above exited zero. This was an invocation error, not a failed algorithm test.
All audits used only propext, Classical.choice and Quot.sound.

All 31 IndexedLookup, 12 SortedBabies and four SortedBSGS public declarations
were added to Audit.lean, with module imports. Full integrated `./scripts/check.sh` passed: 20 screened files, 43 build jobs,
159 theorem audits and smoke output. STATE.md records the active continuation.
