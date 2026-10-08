# Research checkpoint

Status: active, wave 4 sorted-solver correctness/query milestone accepted
(2026-10-07). Persistent goal in coordinator thread
`01a118a2-f8f0-7751-90bd-ddeb86a90ada`; no token budget or recurring schedule.
Starting commit `815d920`, clean at intake. Local milestones `c99e349` and
`05ed8be`; W005/W006/W007 committed locally as `9667d72`; clean after that commit.
W008 coordinate-key layer committed locally as `97ebd5c`. IndexedLookup,
SortedBabies and SortedBSGS are frozen, independently reviewed, integrated and
committed locally as `f95d27e`. Full-cost semantics remain under design review.
No faster ECDLP algorithm or cryptographic break has been discovered.

## Authorization and operating constraints

User authorized the ongoing research loop, parallel native/T3 delegates,
independent verification, and local commits of significant findings/process.
Preparation-only restrictions are superseded. No push, publication, wallet
recovery or scheduler. Coordinator alone integrates/stages/commits; writers
have disjoint ownership, reviewers are read-only. No grandchildren. Respect
four active slots including coordinator; availability is not execution evidence.
Core Machine/Problem/Goals definitions remain frozen. Their encoding/advice
limitations are documented by negative tests, not silently repaired.

## Current live work

- Native Sol `/root/small_curve`: completed adversarial W010 review: original
  proposal rejected. Now owns ONLY research/proposals/W011-fixed-word-contract.md
  as design writer: exact finite-PC/fixedheap semantics, no Lean implementation.
  Draft must be independently reviewed before implementation; no children.
- T3 Grok `grok-4.7`: original primary-literature/falsifiable-directions task
  remains running at last status read. Do not duplicate because it is slow.
  Request `ecdloop-w1-literature-grok-20261007-r1`; task ID
  `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w1-literature-grok-20261007-r1`.
- Native Astra `/root/encoding_review`: independently passed W008 key/search,
  W009 adapter and full sorted solver, including all 28 compiled test cases.
  W010 arithmetic reproduction passed. W012 source/data independently passed:
  all2085 scalar/width cases,128691 events, every dominance/proxy result and
  first-hit addition totals checked. Currently complete; available for W011.
- Factory Fable 5.1: whole-solver cost-design review completed; original report
  retained verbatim in W010-cost-proposal-review.md, explicitly NOT ACCEPTED.
  Request `ecdloop-w4-cost-ledger-fable-20261007-r1`; task ID
  `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w4-cost-ledger-fable-20261007-r1`.
  Original proposal rejected after independent Sol challenge. Full corrections
  and Astra-reviewed arithmetic counterexamples retained in W010. A smaller
  fixed-capacity instruction machine is only a qualified direction; no exact
  semantics or alternative cost goal has been adopted.
  Current active slots: coordinator, Sol W011 design writer, Grok literature.
  Native Astra completed W012 review; no duplicate tasks.

Live catalog discovered Codex Astra/Sol, Claude Opus 5.5, Grok 4.7, and Factory
Fable/Opus with delegation supported and no reported constraints. Actual runs
are identified here; no claim every listed model ran.

## Completed delegated rounds

Native Sol authored SmallCurve, Framing, OrbitArithmetic and BSGS in separate
owned-file rounds, and proposed W005 algebra/cost design. Native Astra separately
reviewed W002 negative tests, W003 framing, W004 experiment, W005 design and
implementation, W006 source/arithmetic/disagreements, W007 modular arithmetic
and frozen BSGS implementation. All qualified passes have explicit limits in
findings; standard proof compilation is not independent cost-model acceptance.

T3 completed rounds (retain exact task IDs; new reviews require new delegates):

- Claude Opus 5.5 specification/lower-bound audit, request
  `ecdloop-w1-spec-opus-20261007-r1`; task ID
  `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w1-spec-opus-20261007-r1`.
  Secret-revealing encoding counterexamples integrated/reviewed; informal
  prime-gap/advice claims challenged and qualified in W002.
- Factory Fable 5.1 finite curve/baseline review, request
  `ecdloop-w1-finite-review-fable-20261007-r1`; task ID
  `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w1-finite-review-fable-20261007-r1`.
  PASS with scope qualifications recorded in W001.
- Claude Opus 5.5 signed-BSGS design/literature review, request
  `ecdloop-w3-negation-design-opus-20261007-r1`; task ID
  `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w3-negation-design-opus-20261007-r1`.
  No design blocker. Native Astra challenged rounding, necessity of strict
  span, stored-sign representation and tuning claims; resolutions in W006.
  This early design review did not inspect the later Python implementation.

## Established milestones

- Initial scaffold: explicit binary-tape semantics, cyclic-orbit interface,
  deterministic finite/uniform goals, order-two solver, secp256k1 constants and
  generator equation, conditional capacity arithmetic. 12 original audits.
- `c99e349`, W001/W002: seven-point coordinate curve over F5, proved group laws
  and exact orbit, exhaustive solver with d+1 equality tests; independently
  reviewed encoding leakage and indistinguishable-tape counterexamples.
- `05ed8be`, W003/W004: fixed-width observable input distinction; all 365 scalars
  of five synthetic coordinate curves tested with ordinary BSGS variants.
  Linear lookup retains d+1 equality checks despite fewer additions; sorting
  comparisons charged in ordered variant. 70 audits; 119327 instrumented events.
- W005: generic orbit period/residue laws, executable add/neg refinement proved
  for SmallCurve, baby construction invariants. Its exact m count is ONLY direct
  countedAdd wrapper calls; generator evaluation/P.next and internals excluded.
- W006: signed coverage/alias arithmetic; reviewed signed-BSGS finite experiment
  with fresh per-target sorting on all 365 scalars, three variants, 100988
  instrumented events. Known constant-factor addition saving accompanied by
  sign/key costs; no calibrated speed, exponent or complete Lean signed solver.
- W007: actual generic linear BSGS correctness for every orbit scalar and
  positive width, including duplicates m>q and order one. No cost bound.
- W008/W009: coordinate keys, actual indexed binary search, sorted preparation
  and full sorted BSGS correctness. Queries/probes/comparisons accumulated from
  executed lookups; generic bounds exclude all preprocessing, key/group/scalar
  arithmetic and memory. Runtime checks passed all 28 scalar/width cases on
  the order-seven curve. These are conventional algorithms, not improvements.

## Current validation and remaining assumptions

Current `./scripts/check.sh` passed: 20 screened files, 43 build jobs, 159
named theorem audits and executable smoke output. IndexedLookup (31 claims),
SortedBabies (12) and SortedBSGS (4) each independently recompiled/audited;
only permitted propext, Classical.choice and Quot.sound dependencies.
`scripts/sorted_bsgs_checks.lean` runs with lake env lean (no --run; uses #eval)
and all 28 cases passed, output archived in W009-sorted-results.txt. W006 JSON
was independently reproduced previously. Failed proof/command attempts and
reviewer-only unarchived sweeps are retained in findings; no failed algorithm
case is hidden.
These scripts detect honest mistakes, not adversarial proof validation.

Open prerequisites: cryptographic/general EC refinement; reviewed hard family
and conventional public encoding; complete preprocessing, key/arithmetic,
primitive/access/allocation/storage/scalar-width accounting; tape
refinement; randomized semantics; calibration and any genuinely improved
candidate. Orbit laws alone give no off-orbit target validation or efficiency.
Do not equate wrapper calls, field operations, RAM units, tape transitions or
hardware timing. Deferred W005 RAM ledger is not an accepted model.

## Next distinct step

W008/W009 committed after staged-path inspection. Coordinator archived W010
arithmetic counterexamples for word widths, bump addresses, primality and
exact-order validation; these are not VM or accepted-solver failures. W010
original design is rejected; draft and independently review the exact W011
contract before implementing any alternative cost interpreter. Retain frozen
Machine/Problem/Goals.
Collect Grok's existing task when its notification arrives; do not duplicate.
Continue bounded waves with durable evidence and reviewer disagreements.
Previous turn: progress (a92d640 negative cost-model findings). This turn
adds W012 finite all-width tuning evidence while W011 is drafted. None of the
three signed defaultwidths is dominated in the partial eventvector; minimizers
of declared hypotheticalweights vary. These are not wholecost/speed results.
Grok remains authoritatively live; no duplicate task or scheduler.
Research goal stays active; no completion or repeated-blocked threshold is met.
