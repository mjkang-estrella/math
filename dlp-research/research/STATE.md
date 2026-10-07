# Research checkpoint

Status: active, wave 1 complete; wave 2 in progress (2026-10-07). Persistent goal established in coordinator
thread `01a118a2-f8f0-7751-90bd-ddeb86a90ada`; no token budget or recurring schedule.
Starting commit: `815d920`; working tree clean at intake.

## Active wave and ownership

Integration milestone: inspect specification gaps and prove arithmetic and
exact-order facts for a small actual elliptic curve, without changing the frozen
core interface or claiming a faster ECDLP algorithm.

Live catalog refreshed: Codex Astra/Sol, Claude Opus 5.5, Grok 4.7, and Factory
Fable/Opus all report child delegation support and no constraints. Actual runs
and failures are recorded below; availability alone is not execution evidence.

Active wave-1 delegates:
- Native Codex `gpt-6.1-sol`, `/root/small_curve`: completed and stable;
  `Research/SmallCurve.lean` implements the seven-point F5 curve. All 22
  public theorem audits passed; coordinator independently cross-checked it.
- T3 Claude `claude-opus-5-5`, completed; request
  `ecdloop-w1-spec-opus-20261007-r1`; task ID
  `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w1-spec-opus-20261007-r1`.
  Read-only specification and lower-bound audit.
  Produced Lean-checked secret-revealing encoding counterexamples. Coordinator
  reproduced and namespaced them in EncodingAudit.lean as negative tests;
  broader informal assertions remain under review, not accepted facts.
- T3 Grok `grok-4.7`, running; request
  `ecdloop-w1-literature-grok-20261007-r1`; task ID
  `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w1-literature-grok-20261007-r1`.
  Read-only primary literature and falsifiable candidate directions.

Coordinator alone owns integration, findings, audit list, checkpoint, and commits.
Delegates must not spawn grandchildren in this wave. Three children maximum.

After Opus completed, native Astra `/root/encoding_review` completed a read-only
independent review of encoding counterexamples and InputCollision.lean: qualified
pass. W002 records its disagreements with Opus's informal prime-gap and advice
claims. All three negative examples independently reproduced.

Wave-2 overlap while cross-provider reviews finish: native Sol `/root/small_curve`
now owns ONLY new `Research/Framing.lean`, proving fixed-width observable tape
read adequacy. Existing SmallCurve source remains stable. No grandchildren.

Replacement delegate after Sol completed: Factory `claude-fable-5.1`, read-only
independent curve/baseline proof and cost review; completed, PASS with
qualifications resolved in W001 (no blocking proof findings).
Request `ecdloop-w1-finite-review-fable-20261007-r1`; task ID
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w1-finite-review-fable-20261007-r1`.

Integration accepted for local commit: W001 finite coordinate curve and exact
exhaustive equality counts reviewed by Factory Fable; W002 negative encoding
tests reviewed by native Astra. Full suite passed 53 dependency audits and
25 build jobs. Latest source screen sees 12 files because uncommitted Framing
is present; Framing is NOT included in this milestone's accepted claims or
commit. All core definitions unchanged; Goals comments clarified only.

Commit file scope: Audit.lean, Main.lean, README.md, Research.lean,
Research/{Baseline,Checks,EncodingAudit,Goals,InputCollision,SmallCurve}.lean,
scripts/small_curve_reference.py, research/findings/W001-initial-audit.md,
research/findings/W002-encoding-audit.md, and this checkpoint. No toolchains,
build products or Framing source are staged for this milestone. The commit
records both results with their separate reviewers; see git log for its hash.

Framing implementation is complete, with 17 standalone theorem audits passed.
Native Astra `/root/encoding_review` is now independently reviewing it read-only.
Grok literature remains live. Research objective is active, not achieved.

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
- `Research/SmallCurve.lean`: finite coordinate curve with seven points, group
  laws, complete order-seven orbit and fixed-width encoding (independent review passed).
- `Research/Baseline.lean`: generic executable exhaustive scan with exact d+1
  equality tests; instantiated on the small curve (independent review passed).

## Unresolved prerequisites

1. General/cryptographic EC refinement beyond the finite seven-point example.
2. Review/freeze a nontrivial curve family and public encodings.
3. Tape refinement of the exhaustive baseline, verified square-root baseline,
   randomized semantics, memory accounting, and cost/performance calibration.

## Next distinct step

Finish the enumerated W001/W002 local commit. Await Grok literature and native
Astra framing review; do not duplicate either task. Then integrate/audit framing
and test a square-root reference baseline with explicit lookup/memory costs.
Coordinator is preparing a bounded synthetic comparison of linear versus
ordered BSGS lookup; no algorithmic improvement has been accepted.

Previous goal turn: progress (negative encoding examples, independent review,
53 audits). Current continuation: progress (Factory pass resolved, framing
implemented, final milestone review/commit). No blocker threshold or objective
completion criterion has been met.

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
