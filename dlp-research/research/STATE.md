# Research checkpoint

Status: dedicated multi-agent research task authorized and being launched;
no time-based recurring schedule configured.

## Task authorization

The user authorized an ongoing research task, parallel delegates across the
model families in `RESEARCH_TEAM.md`, in-depth independent verification, and
local commits of significant findings with their process/evidence. Preparation-
only instructions from the original setup have been superseded.

The task coordinator must record its active goal and delegated task IDs here
before beginning parallel work. Only it integrates and commits shared changes.

## Objective

Develop a precise, verified research framework for improved elliptic-curve
discrete-log algorithms. No faster algorithm has been discovered here.

## Established artifacts

- `Research/Machine.lean`: explicit finite-program binary-tape cost semantics.
- `Research/Problem.lean`: injective cyclic-orbit public-key problem interface.
- `Research/Goals.lean`: concrete feasibility and uniform exponent objectives;
  conditional arithmetic capacity checks.
- `Research/Secp256k1.lean`: standard constants and generator equation check.
- `Research/Checks.lean`: interpreter checks and trivial order-two example.

## Unresolved prerequisites

1. Concrete EC arithmetic and exact-order proof connected to the interface.
2. Review/freeze a nontrivial curve family and public encodings.
3. Verified baseline, randomized semantics where needed, memory accounting,
   and a justified relation between abstract cost and measured performance.

## Next distinct step

Choose a small actual elliptic curve, implement its arithmetic, and prove that
its chosen generator and coordinate encoding instantiate `CyclicProblem`.
Treat that as specification validation, not an attack or asymptotic result.

## Validation

2026-10-07, initial setup, Lean 4.34.1:

- `./scripts/check.sh`: passed; 17 build jobs, source screen for 7 files,
  axiom audit for all 12 listed declarations, executable smoke check.
- Allowed dependencies found: `propext`, `Classical.choice`, `Quot.sound`.
  The curve-coordinate and arithmetic checks depend on no axioms.
- `git diff --check`: passed (new files are untracked; no commit was requested).
- No GPU computation, model API calls, recurring tasks, or attack attempts.

Scope: the abstract framework and listed checks compile. The concrete elliptic-
curve solver/refinement and all faster-algorithm claims remain unproved.
