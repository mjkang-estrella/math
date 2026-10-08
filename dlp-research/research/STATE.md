# Research checkpoint

Status: active, word-machine component verification after sorted-solver milestone
(2026-10-07). Persistent goal in coordinator thread
`01a118a2-f8f0-7751-90bd-ddeb86a90ada`; no token budget or recurring schedule.
Starting commit `815d920`, clean at intake. Local milestones `c99e349` and
`05ed8be`; W005/W006/W007 committed locally as `9667d72`; clean after that commit.
W008 coordinate-key layer committed locally as `97ebd5c`. IndexedLookup,
SortedBabies and SortedBSGS are frozen, independently reviewed, integrated and
committed locally as `f95d27e`. W010 negative findings committed as `a92d640`;
W012 signed tuning committed as `f3d451a`. W011 abstract core contract accepted;
WordCore and WordCodec with review records committed locally as `d830782`.
Tight signed coverage and independent enumeration committed as `03d4bdb`.
Raw-run interpreter independently verified and committed as `4120ffc` (W014).
W017 accounting and amended W016 policy committed as `7a2f5df`.
W020 exact table encoding/numerical layout committed locally as `a367812` (303 audits).
Complete solver costs remain unproved.
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

- Native Sol `/root/small_curve`: WordQueryCode frozen, independently reviewed
  and integrated (347 audits), W022. Now owns only Research/WordQueryDecoder.lean
  for actual operational field-loop contents/termination/trace refinement.
  First bounded milestone may be genuine per-iteration/exit semantics if the
  complete generic 9+6w theorem needs further waves; no assumed macro contract.
- Native Astra `/root/encoding_review`: W019 adversarial and WordPacking/code
  reviews complete. Now owns only Research/WordQueryInputFacts.lean: actual raw
  header/key/payload/query bit association, paired numeric-value lemmas, generic
  valid indices. No guest-execution claim. Planned API supplied to Sol.
- Coordinator: independent fresh-run query tests and integration are next.
  WordPacking and W019 negative finding committed as `b92f092`; typed query
  code accepted only for fixed graph/admission/serialization, with operational
  correctness, common F and actual cost comparisons still outstanding.
- Factory Fable5.1 focused audit completed, no children. Its report is retained
  with independently reviewed corrections in W019-disposition.md. Request
  `ecdloop-w8-literature-audit-fable-20261008-r1`; task ID
  `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w8-literature-audit-fable-20261008-r1`.
  The original general ring-addition routine is falsified by a valid-point
  noncommutativity counterexample; sampled Smart outputs are not thereby refuted.
- Original Grok literature task: complete report recovered read-only from backing
  timeline position144, updated2026-10-07T23:33:48.137Z, while task status still
  said running with null summary. Retained verbatim; coordinator then cancelled
  the unfinalized owned run with request
  `ecdloop-w1-literature-close-recovered-20261008-r1`. Authoritative final state
  interrupted/result_available, no children; task_status now publishes the report.
  This was an orchestration finalization discrepancy, not evidence Grok never ran.
  Task ID
  `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w1-literature-grok-20261007-r1`.
- Opus W016 review completed and its binding conditions were incorporated,
  independently reviewed, and committed in 7a2f5df with W017 accounting.
  Request `ecdloop-w7-query-contract-opus-20261007-r1`; task ID
  `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w7-query-contract-opus-20261007-r1`.
  Earlier W010 Factory and W011 Opus reports/IDs remain in their findings.

Active: coordinator, Sol operational decoder, Astra input-bit association (three).
Factory completed; original Grok closed. No duplicate delegated tasks.

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

Current `./scripts/check.sh` passed: 347 named theorem audits and executable
smoke output. WordCore (23), WordCodec (29), SignedTight (16) and WordRun (38)
plus WordRunFacts (10) and WordQueryData (28), WordPacking (7) and WordQueryCode (37) are included; independent component reviews PASS. IndexedLookup (31),
SortedBabies (12), SortedBSGS (4) and all earlier claims remain included.
Only permitted propext, Classical.choice and Quot.sound dependencies.
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

W014 runner committed as 4120ffc. W017 exact fresh-run accounting/guest split
independently passed and integrated (275 audits). W016 amended contract accepted
ONLY for data encoding/numerical profile support and numbered graph design:
3aa67dbd8e98de67878d978cb895f3d3763474546ff4ed5dc39c54ec517b92b5.
Original reviewed draft bd22c845... retained in proposals/archive. W018 graph and W022 typed code reviews now PASS; actual shared code admission
is proved nonvacuously. Full result still needs generic correctness, common-F
sufficiency, segment refinement and actual fresh-run ledgers. See binding W016 section 9 for all conditions.

Previous goal turn: progress (a367812 exact data proofs and retained reports).
Current turn: progress (W018 graph review accepted/reproduced; W019 focused report
collected/corrected/committed; arithmetic and fixed code independently verified;
new operational decoder/input-bit proof tasks active). No speedup, whole BSGS cost or
cryptographic/tape/hardware result is established. Machine/Problem/Goals and
existing experiment engines remain unchanged.

Grok's recovered report is unaccepted evidence pending the new focused audit.
No scheduler or publication is authorized/configured. Goal stays active;
no completion or repeated-blocked threshold is met. An unrelated untracked
`research-monitor/` directory at repository root is excluded from this task.
