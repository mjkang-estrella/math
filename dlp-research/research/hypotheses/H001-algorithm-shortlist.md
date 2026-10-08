# H001: algorithm-first shortlist (provisional, not discoveries)

User refocus acknowledged,2026-10-08 UTC. Current verified improvement: **NONE**.
Working classical baseline for ordinary prime-field prime-order groups remains
square-root work, with known negation/automorphism constants and explicit memory/
parallelization tradeoffs. No calibrated full-size GPU throughput is available.
This shortlist is for quick rejection/refinement, not an assertion of novelty.

## 1. Coordinate-aware relation generation for prime-field index calculus

Mechanism to investigate: exploit the algebraic structure of Semaev summation
polynomials using structured elimination or coordinate buckets, rather than
exhaustively enumerating factor-base tuples. A concrete proposed filter must
preserve enough valid relations while reducing candidate combinations; a free
bounded-root oracle is forbidden. Initial task must identify that actual filter
or report that no candidate beyond known exhaustive joins was found.

Barrier: obtaining enough bounded-coordinate relations cheaply enough, including
failed searches and linear algebra. Prior art: Semaev2004/031 and Diem2011; the
retrieved historical papers leave the relevant prime-field solver gap open.
Fresh primary-source search is required before any novelty statement.

Target hypothesis, not evidence: with n=5 and factor-base scale B≈q^(1/5+δ),
Semaev's conditional estimate t*B+B² beats q^(1/2) only if δ<1/20 and
relation cost t=o(q^(3/10-δ)), including preprocessing amortization. These
necessary thresholds are the first falsifier. Little-o here only means a
sub-square-root ratio; a fixed exponent improvement additionally needs an
explicit fixed positive exponent gap in the relation-generator bound. Ordinary pair/triple joins or
unjustified Wagner-style coordinate bucketing may fail this threshold outright.
Memory includes all factor-base points, join tables, stored relations and sparse
linear algebra; no table is free. Baseline is matched full-domain BSGS/rho work.

Cheap test: derive the relation-generation cost from the actual proposed steps
first; reject exponent arithmetic that already loses. For a surviving explicit
filter, compare relation retention versus candidate pruning and complete cost on
increasing ordinary synthetic prime-order curves, with multiple seeded targets.
Include a no-filter control and source-point signs. Small n=3 diagnostics alone
cannot validate the n=5 exponent, and finite fits cannot prove an asymptotic.

## 2. Reduce total work in an already automorphism-aware rho baseline

Mechanism to investigate: batched/cycle-aware scheduling of quotient-walk work,
including a concrete evaluation of delayed canonicalization blocks. Known order-
2/order-6 automorphisms are baseline features, not a new attack. The candidate
must preserve correct coefficient tracking and collision recovery and compare
against the best applicable known quotient walk, not only plain rho.

Barrier: per-step coordinate normalization, fruitless cycles, field inversion/
batching and collision-table overhead can consume the theoretical constant.
Prediction sought: a material complete-work saving (e.g. >10%, with uncertainty)
at increasing sizes/seeds; no exponent improvement is predicted. This threshold
is an experimental objective, not a per-input theorem or claimed speedup.

Memory/preprocessing: r-adding tables, distinguished points, batch storage,
restarts and collision verification all count. Prior art includes Bernstein–
Lange–Schwabe PKC2011 and earlier automorphism walks; exact candidate novelty must
be checked. Hardware timings cannot be inferred from AI FLOPS.

Cheap falsifier: for delayed blocks t=1,2,4,8, first derive collision opportunity
loss versus saved normalization and check quotient-walk/coalescence validity.
Reject analytically if extra additions dominate the maximum possible saving.
Only a surviving schedule merits matched seeded synthetic complete-run tests.
A favorable scalar-multiplication kernel alone is insufficient.

## 3. GLV decomposition as an alleged exponent reduction — reject unless new information

Mechanism often proposed: split a scalar into two ≈sqrt(q) coefficients using a
known endomorphism and treat either coordinate as a smaller DLP. Barrier: the
joint domain still has ≈q possibilities and the two coefficients are not given.
Known GLV speeds scalar multiplication; it does not supply a discrete-log oracle.
Baseline square-root collision work still applies to the unstructured search.

Predicted credible improvement from decomposition alone: **none in the exponent**;
possible known per-operation constants belong in baseline2. Memory/preprocessing
must include any coefficient lattice or lookup tables. Cheap falsifier: enumerate
joint-domain size/linear relation rank and identify the exact new information or
non-generic operation that would eliminate it. No expanded proof infrastructure
or broad experiment is authorized for this already-known obstruction.

## Decision gate

First disposition: item2 fails the present analytic/headroom gate; see
H001-delayed-canonicalization-gate.md. This is not a universal lower bound.
Item3 supplies no new information and is rejected as an exponent claim. Item1
remains open only for an explicit relation generator; PKM/APS are known prior
art. Broad H002 independent ideation proceeds in parallel under the latest user
policy; this shortlist is not the entire research pipeline.

The shortlist may be reordered or entirely rejected by the independent critic.
A proposal must produce a concrete algorithm and a conclusion-changing test;
missing root solvers, unproved bias or favorable toy curves are not results.
The next wave reports supported complexity/work, improvement (currently NONE),
hypothesis, evidence against/for, and the next decisive test. Parked word-machine
work is not a prerequisite and cannot consume new effort without a named need.
