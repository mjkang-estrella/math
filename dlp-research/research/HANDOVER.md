# ECDLP research handover

2026-10-09 UTC / 2026-10-08 America/Los_Angeles. **User requested shutdown
after currently running work. Collection is complete; research is stopped.
No new research is authorized.** Final live-task
and goal-pause confirmation is recorded at the end of this document.

Repository: `/home/mj-kang/Documents/Dev/math`, branch `main`.
Project: `dlp-research`. Existing goal: `01a118a2-f8f0-7751-90bd-ddeb86a90ada`.
This handover concerns ECDLP only. The factoring coordinator handles factoring;
the separate **Find New Low-Hanging Mathematical Proofs** thread is untouched.

## Purpose, assumptions and present conclusion

Investigate a correct executable algorithm for recovering the full scalar
k in[0,q) from public E,G,Q=[k]G, on appropriately hard elliptic-curve families,
with honest explicit complete costs and independent verification. Synthetic
instances only; no wallet targeting, hidden inverse tables, secret-dependent
advice, narrowed scalar ranges or toy-to-real extrapolation.

**Verified exponent improvement: NONE. Verified matched complete-work
improvement over the accepted baseline: NONE.** The working classical exponent
is1/2 in subgroup order q, with known negation/automorphism constants and
resource-dependent rho/BSGS comparisons. This is neither a proof of ECDLP
hardness nor a generic-group impossibility claim for coordinate-aware methods.
No calibrated cryptographic-size whole solver or validated GPU throughput was
produced. B200/H200 AI FLOPS are not curve-work measurements.

The Lean deterministic all-input worst-case goal is stronger than expected
randomized rho claims. `Research/Goals.lean` defines ConcreteGoal and
ExponentBreakthrough; it does not prove an improved algorithm exists. The
family interface does not itself enforce hardness or efficiently generated,
advice-free encodings. Full cryptographic EC refinement, a frozen hard family,
randomized semantics and realistic complete resource calibration remain open.

## Evidence classes — keep these separate

| Evidence | What exists | What it does not establish |
|---|---|---|
| Lean kernel-checked artifacts | Existing 366 named dependency audits; small coordinate curve, baseline correctness, lookup/encoding/word components, secp generator equation, conditional capacity arithmetic | A new attack, cryptographic-size EC group proof, complete baseline tape cost, randomized stopping law or physical throughput |
| Paper mathematical results | Scoped identities, counting arguments and literal-algorithm screens in findings; many independently rederived by root/native reviewers | Lean certification or a universal algorithmic lower bound |
| AI/provider reviews | Raw proposals, disagreements, corrections, source access limitations and task handles retained | Correctness merely because several models agree; failed providers supplied no result |
| Executed finite diagnostics | Archived source, frozen protocols and result artifacts under research/experiments and findings | Asymptotic proof, full-size speedup, or unexecuted/censored branch coverage |
| H048 partial ideation | One existing native task returned two related divisor/bilinear ideas at shutdown | Independent mathematical review, new primary-source verification, executable algorithm or admission to test |

## Adopted results and exact scope

Formal entry points are [README](../README.md), [Audit.lean](../Audit.lean),
[Research.lean](../Research.lean), and [Research/](../Research/). The seven-point
curve over F5 is genuinely verified finite EC refinement. Exhaustive search and
ordinary/sorted BSGS recover every orbit scalar under their interfaces; their
comparison bounds do not price all preprocessing, field arithmetic and memory.
Encoding counterexamples show why bare cyclic interfaces are inadequate security
challenges. Word/query work was parked after user correction of infrastructure
drift; [parked infrastructure](parked/20261008-query-infrastructure/README.md)
must not be revived without a concrete surviving candidate-specific need.

Latest reviewed paper results:

- [H047 mixed-radix success](findings/H047-mixed-radix-success.md): dependent
  short pairs generate independent randomized long progressions; exact moments
  and output-cap qualifications give a compatible success premise. A paid fast
  selective reporter is missing. Common-step constructions can fail.
- [Rectangle screen](findings/H047-rectangle-reporter-screen.md): a lower cost
  bound for a specified complete fresh-perimeter reporting schedule, not cached,
  shared, early-stop or arbitrary circuits.
- [Compact-filter reporter](findings/H047-compact-filter-reporter.md): explicit
  division-free polynomial circuit and paid exceptions/extraction; its supplied
  softO(M) upper invoice does not improve direct enumeration's exponent. It is
  not a proof every possible reporter needs that work.
- [Residual projection](findings/H047-residual-projection-screen.md): nonsplit
  quadratic residual trace/anti-trace equations do not yield the claimed new
  scalar relation through the immediate collision bridge. Further nonlinear
  constraints are not excluded.
- [Storage/recovery screens](findings/H047-storage-recovery-screens.md): exact
  residue intervals/sign recovery and conditional filter-tree accounting, with
  query-seed scope and preprocessing retained. No universal memory lower bound.
- [Eigenline residue disposition](findings/H047-eigenline-residue-disposition.md):
  corrected order-four eigenline; exact higher-residue product conditional on
  finite nonzero observable values; a quartic nonvanishing condition; a sextic
  observable that can vanish identically. Finite-order integer matrices with
  tame reduction satisfy a restricted dimension screen. Its ideal g-additions
  quotient comparison does not constrain fused arithmetic or prove stopping.
- [Sibling-min correction](findings/H047-sibling-min-correction.md): regular
  delayed-ordinate kernel4M+S outside inversion, batch7M+S+(I-3M)/K; zero-jump
  absorbing states and limited repeated-index dynamics. No useful stopping law
  or complete solver gain. Native algebra and cost reviews completed. The final
  Fable review supplies an alternative6M+2S+(I-3M)/K regular batch schedule,
  checked by root on paper. Its probabilistic gain ceilings remain unverified.

These latest paper findings add no Lean theorem. Historical W001--W024 formal
and experiment records and H001--H046 algorithmic records remain searchable in
[findings/](findings/) and the chronological sections of [STATE](STATE.md).

## Rejected and parked directions

Do not erase failed hypotheses or adopt raw reviewers' overstatements. Recurring
rejection reasons were missing public operators, special-curve applicability,
paid relation generation overwhelming sparse relation counts, dense polynomial
or selector costs, hidden preprocessing/advice, insufficient useful collision
laws, detector/coalescence errors, memory mismatch and finite-only evidence.
Known signed BSGS, automorphism rho and arithmetic batching are prior art.

- Half-orbit/character signals can have exact identities while evaluation and
  recovery remain too expensive in the supplied implementations. Named decoder
  upper bounds are NOT lower bounds excluding better joint recovery.
- Borrowed E² automorphisms lose in the literal g-addition ideal model supplied;
  that does not prove every representation or fused circuit loses.
- Coordinate walk gates remain parked without complete label/detector/restart
  contracts and a credible useful hitting-time improvement. Image concentration
  alone does not prove such improvement.
- H034 sparse paired sums have conditional mathematical premises, but the
  finite run was censored and never reached candidate leaf search. No observed
  solver gain can be claimed. See its result and review qualifications below.
- Safety-stopped H006 role and H038 Farey/height-lattice route were not retried
  through another provider. Their stops remain recorded, not mathematical
  impossibility theorems.
- [H048 partial result](findings/H048-stop-boundary-result.md) is independently
  UNVERIFIED. It supplies no cheaper structured bilinear-zero reporter; user
  shutdown prevents additional review or tests.

## Latest work, task handles and process ownership

Native handles: `/root/h007_additive_relations` (Astra: H047 final algebra),
`/root/h034_c4_implementation` (Sol: cost review, then already-running H048
partial ideation). Both returned final results after/before receiving the stop
boundary; no followup is authorized. `/root/h006_structured_relation_ideas` is
historically errored, not live and not retried.

T3 task IDs use the exact prefix:

`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3A`

Append these retained suffixes:

| Suffix | Provider/model | Final evidence |
|---|---|---|
| ecdloop-h047-shared-information-factory-opus-20261009-r1 | Factory / claude-opus-5-5 | Completed; raw report in H047-information-factory-raw.md; corrected disposition supersedes it |
| ecdloop-h047-coordinate-constructions-opus-20261009-r1 | Claude / claude-opus-5-5 | Failed after repeated API errors; no mathematical result; explicit native fallback is separately attributed |
| ecdloop-h047-autonomous-search-grok-20261009-r1 | Grok / grok-4.7 | Completed; H047-walk-grok-raw.md is unaccepted raw output |
| ecdloop-h047-walk-algebra-review-fable-20261009-r1 | Factory / claude-fable-5.1 | Completed, no pending runs; H047-walk-fable-review-raw.md retains corrections and unverified heuristics |

Factory Opus task_status returned only a plan footer; the actual untruncated
research message was recovered from backing-thread position35, exact item ID
in the raw record. Shutdown steering to the existing Fable run was confirmed
`delivery=steered`, not a new delegated review or queued followup. No failed
task was restarted. Root alone edits/stages/commits shared files.
Fable's actual final message was recovered from backing-thread position21;
its exact item ID is in [the raw review](findings/H047-walk-fable-review-raw.md).
It used repository sources only. No followup was started to resolve its
unproved cycle rates, occupation estimates or IID-based claimed gain ceilings.

Relevant local commits: `815d920` initial scaffold/policy; `79ac5d0` H046
reviewed progression/cost gates; `c1de988` rectangle screen; `386c5b7` mixed-radix,
residual and storage; `8678feb` compact reporter; `d2b4115` returned raw reports;
`5758104` corrected eigenline transfer. Final handover commit is discoverable
with `git log -1 -- dlp-research/research/HANDOVER.md`. No push or publication.

## Validation, reproduction and consumed budgets

Lean4.34.1, bundled Std only; ignored local `.tools/` via scripts/lake.sh.
Artifact validation from the project directory:

```bash
cd /home/mj-kang/Documents/Dev/math/dlp-research
./scripts/check.sh
./scripts/lake.sh build
./scripts/lake.sh env lean Audit.lean
```

check.sh runs source screening, build, printed dependency audit and the finite
research_demo checks. Its366 audits are honest-mistake checks, not hardened
adversarial proof validation. Earlier current validation passed at
`/tmp/ecdlp-h047-eigenline-check.log`; temporary logs are not portable evidence.
Final handover validation passed as recorded below. Validation is not
a new ECDLP experiment. No performance or arithmetic calibration is inferred.

The latest executed candidate diagnostic is [H034 result](findings/H034-initial-diagnostic-result.md),
with [source](experiments/H034/c4_probe.py), [protocol](experiments/H034/protocol.md)
and [raw JSON](experiments/H034/initial_results.json). It ended
`censored_inconclusive` at the aggregate1,000,000-event guard, pending
fixture3/seed19/candidate/setup/eager_root vertex32 of98. Completed sampled
candidate solves were seed-only; zero candidate-leaf components were exercised.
Controls not reached are untested, not losses. The fixed seed list was7,19;
time guards55 seconds internal/60 seconds outer. Artifact hashes, exact command,
finite tables and review objections are in the result/admission records.

Historical executed command, **DO NOT RUN AGAIN**:

```text
timeout --signal=TERM --kill-after=2s 60s python3 -B research/experiments/H034/c4_probe.py --execute --output research/experiments/H034/initial_results.json
```

The cap is consumed: no reset, output deletion, import side-effect run, warmup,
new seed, trial or retry. No executable candidate experiment followed H034.
Earlier diagnostics retain their own protocols/budgets under experiments/;
this handover grants no replay permission. Read existing JSON/source instead.
No total research token budget was set; token/agent/audit counts are not results.

## Only after explicit user resumption

Read this handover, latest STATE and the exact finding before any action.
There is no surviving verified faster solver waiting merely for implementation.
The main bottleneck is an actual public operator or search process with a
credible matched complete-work advantage, not missing generic Lean machinery.
Check proposal duplicates and full cost first. Conditional signals require paid
evaluation plus recovery; walk kernels require useful stopping/detection laws;
sparse relations require paid source/selector/storage construction. Only a
surviving concrete candidate warrants a separately reviewed finite experiment
with a newly explicit budget and focused formal invariants. Do not silently
reuse consumed H034 authorization or restart safety-stopped work.

## Final shutdown verification

Collection complete. No new work may be launched. Authoritative checks:

- Native list_agents: both current native workers completed; old H006 role
  errored, not live. Zero running native children.
- Fable task_status: completed, hasPendingChildRuns=false; actual final report
  recovered and acknowledged through t3_thread_read.
- Project T3 live-thread inventory, statuses running/waiting/starting/preparing/
  queued, includeSubagents=true, nextCursor=null: zero live children belonging
  to this ECDLP coordinator. Other research threads were not modified.
- list_scheduled_tasks: empty tasks list. No recurring research scheduler.
- Process inspection for dlp-research/c4_probe/research_demo/lake.sh: no matching
  live process. No shell research loop or numerical experiment remains.
- `./scripts/check.sh > /tmp/ecdlp-handover-check.log 2>&1` passed exit0,
  including366 existing declaration audits. No new candidate experiment ran.

The existing research goal is to be set **paused**, never complete, as the
final administrative action after this local handover commit. The coordinator's
final response records the actual tool result and commit hash. This operating
state is **stopped pending explicit user resumption**; no automatic continuation
or further task launch is authorized, even if historical STATE sections say live.
