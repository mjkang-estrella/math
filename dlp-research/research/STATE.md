# Research checkpoint

Status: active, waves 1–3 correctness/finite-experiment milestone accepted
(2026-10-07). Persistent goal in coordinator thread
`01a118a2-f8f0-7751-90bd-ddeb86a90ada`; no token budget or recurring schedule.
Starting commit `815d920`, clean at intake. Local milestones `c99e349` and
`05ed8be`; current W005/W006/W007 milestone ready for local commit.
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

- Native Sol `/root/small_curve`: READ-ONLY next-step proposal for lawful
  conventional coordinate keys and actual indexed lookup with correctness and
  explicit comparison counts. Inspect Std APIs; no implementation or RAM
  adoption until independent design review. Its BSGS source is frozen/accepted.
- T3 Grok `grok-4.7`: original primary-literature/falsifiable-directions task
  remains running at last status read. Do not duplicate because it is slow.
  Request `ecdloop-w1-literature-grok-20261007-r1`; task ID
  `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w1-literature-grok-20261007-r1`.
- Native Astra `/root/encoding_review`: completed independent generic BSGS
  implementation review, PASS. Available for next distinct review.

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
- W007: actual generic BSGS solver and correctness for every orbit scalar and
  every positive width, including duplicates m>q and order one. Coordinate
  instance checked at widths 1,3,7,8. Actual lookup is linear; no cost bound.

## Current validation and remaining assumptions

Integrated `./scripts/check.sh` passed: 16 screened source files, 35 build jobs,
106 audited declarations, executable smoke output. Dependencies limited to
propext, Classical.choice and Quot.sound. W007 frozen source also independently
compiled/audited all nine new claims. W006 archived JSON was independently
regenerated exactly. Earlier failed elaboration attempts and reviewer-only
unarchived supplementary sweeps are identified in findings; none are hidden.
These scripts detect honest mistakes, not adversarial proof validation.

Open prerequisites: cryptographic/general EC refinement; reviewed hard family
and conventional public encoding; lawful efficient keys and sorted lookup;
complete primitive/access/allocation/storage/scalar-width accounting; tape
refinement; randomized semantics; calibration and any genuinely improved
candidate. Orbit laws alone give no off-orbit target validation or efficiency.
Do not equate wrapper calls, field operations, RAM units, tape transitions or
hardware timing. Deferred W005 RAM ledger is not an accepted model.

## Next distinct step

Commit the accepted W005/W006/W007 milestone locally after staged-path/diff
inspection. Review Sol's indexed-lookup proposal independently before assigning
implementation. Collect Grok's existing task when its notification arrives.
Continue bounded waves with durable evidence and reviewer disagreements.
Research goal stays active; no completion or repeated-blocked threshold is met.
