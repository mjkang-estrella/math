# W001: baseline and concrete-refinement prerequisites

Date: 2026-10-07. Starting commit: `815d920`.
Status: verified limited result; independent finite-result review passed with
documentation qualifications resolved. Prepared for local commit with W002.
No improved ECDLP algorithm claimed.

## Hypotheses and scope

H1: Executable coordinate arithmetic on a small nonsingular prime-field curve
can satisfy the current cyclic-orbit interface with ordinary coordinate input.
Falsifiers: failure of closure, a group-law counterexample, earlier generator
wrap, orbit collision, or coordinate-encoding collision. Small-curve success
validates a finite example only and says nothing about secp256k1 hardness.

H2: An exhaustive sequential orbit search recovers every scalar d and performs
exactly d+1 equality tests, hence at most q. This is a conventional baseline,
not a novel algorithm. Falsifiers: any missed scalar, incorrect first match,
or discrepancy between recursive execution and the claimed comparison count.

## Intake evidence and gaps

Read README, research policy/team/checkpoint, all seven initial library/entry
Lean source files, Audit.lean, build manifest and both checking scripts.
`git status --porcelain=v1` was empty; HEAD was `815d920`.
`./scripts/check.sh` passed: 7 screened files, 17 build jobs, all 12 dependency
audits, executable smoke check. This reproduces scaffold status, not a new result.

The source supports the limitations advertised by the README:

- `CyclicProblem` asserts an injective finite orbit, not elliptic-curve laws.
- No actual `ProblemFamily` is instantiated or independently frozen.
- The all-input deterministic bound cannot directly express expected-time rho.
- `descriptionBits` bounds finite control only; public parameters and point
  encodings still need external review for inverse advice and uniform generation.
- Tape transitions do not count physical GPU work, peak memory, or the cost of
  finite-control lookup in a concrete implementation.
- Input is a blank-extended binary tape with no explicit end marker. List
  injectivity alone may not guarantee operational distinguishability of inputs
  differing only by trailing zero bits. This is an audit question, not an
  accepted specification change; fixed-width framing needs separate review.
- Output inspection is external to the transition count. A program can leave
  an already-correct answer in place, as the original order-two example does.
- Source and named-declaration dependency screens are honest-mistake checks,
  not hardened validation against hostile code or changed statements.

## Baseline implementation (coordinator)

`Research/Baseline.lean` contains a recursive `scan`, returning a scalar option
and incrementing a comparison counter in each executed nonempty iteration.
It starts at the identity and takes successive generator steps. There is no
inverse table. `solve` supplies q fuel; proof uses the original interface's
orbit distinctness. Decidable equality on points is an explicit additional
typeclass argument; no efficient equality implementation is assumed.

Claims awaiting independent review and audit integration:

- `scan_comparisons_le`: any run performs at most its supplied fuel tests.
- `scan_orbit`: a target at scalar d is found from any earlier orbit offset
  when enough fuel remains, with d-offset+1 tests.
- `solve_publicKey`: every scalar d is returned with exactly d+1 tests.
- `solve_comparisons_le`: at most q tests on any point target.

Exact command: `./scripts/lake.sh env lean Research/Baseline.lean`.
First run failed on an unreduced structure projection in arithmetic and a
`0 + q` type mismatch. Simplifying the projection and goal fixed both; the
second run exited 0 (one harmless simplification-style linter warning).

This is an instrumented HIGH-LEVEL comparison count. Review confirms one counter
increment per equality test; it is not a separate cost interpreter. It does not count
addition, coordinate arithmetic, equality internals, memory, or bit operations;
it proves neither `SolvesWithin` nor `ConcreteGoal`. Runtime recursion is not
a constant-space implementation guarantee. No wall-clock or asymptotic
improvement is claimed; the baseline is linear in q in this limited metric.

## Review process

The checkpoint records full task IDs. Distinct wave-1 roles:
native Codex `gpt-6.1-sol` implements the small curve; T3 Claude
`claude-opus-5-5` audits mathematical specification and lower-bound scope;
T3 Grok `grok-4.7` investigates primary literature and falsifiable candidates.
All launches accepted; substantive results and provider failures remain to be
recorded. Core definitions remain unchanged. Only coordinator stages/commits.

Next: integrate small arithmetic, independently review baseline and concrete
refinement, add supporting claims to Audit.lean, run full checks, and commit
only with evidence and remaining limitations recorded.

## Independent finite cross-check

Selected curve: y²=x³+2x+1 over F5, G=(0,1). Coordinator independently generated
all solutions and used Python's modular inverse rather than the Lean cubic
inverse. `python3 scripts/small_curve_reference.py` exited 0. It checked all
49 addition pairs and 343 associativity triples, then every scalar 0 through 6.
Orbit: O, (0,1), (1,3), (3,3), (3,2), (1,2), (0,4), returning to O.
Equality counts: 1,2,3,4,5,6,7 (sum 28; worst case 7). No randomness or seed.
The coordinate arithmetic check is independent of Sol's implementation. The
Python scan and Lean baseline share the coordinator as author and the same
loop structure, so the scan test is only a consistency check. Python does not
explicitly test inverses; Lean's `add_neg` does. Neither check substitutes for Lean proofs
or an empirical speed measurement. The fixed experiment fits the initial
resource envelope; no curve-size extrapolation is made.

Primary source retrieved by coordinator: [Standards for Efficient Cryptography
1 (SEC 1), version 2.0](https://www.secg.org/sec1-v2.pdf), §2.2.1, pp. 6–7.
Its prime-field curve definition, discriminant condition and coordinate
addition/doubling formulas agree with the chosen mathematical model. This
source supplies the conventional interpretation; the finite implementation
still requires kernel checking and independent review. The custom seven-bit
toy encoding is not SEC 1 wire-format conformance.

## Integration validation

Integrated all 22 public SmallCurve theorem audits and four general Baseline
theorem audits: `./scripts/check.sh` passed 38 declarations, 9 screened files,
21 build jobs. Added `Checks.small_curve_baseline` and
`Checks.small_curve_baseline_worst_case`; their first build failed because Lean
did not unfold `SmallCurve.problem.Point` during decidable equality instance
search. A local explicit instance using the concrete subtype equality fixed it
(no classical equality or changed core definition).

Final `./scripts/check.sh` passed all 40 audits with only the allowed standard
dependencies, all 21 build jobs, and smoke output; `git diff --check` passed.
The baseline simplification linter warning was removed. No proof escapes or
compiler-based proof shortcuts were introduced.

Sol `/root/small_curve` completed; its own three bounded 60-second-limit Lean
compile commands passed without failures. Factory `claude-fable-5.1` now owns
the read-only independent finite-curve/baseline proof and cost review (full
request/task ID in STATE.md). Opus specification and Grok literature reviews
remain active. Accepted launch is not evidence of completed review. Await
asynchronous results before accepting this milestone and committing it.

## Completed independent review and resolution

Factory `claude-fable-5.1`, request
`ecdloop-w1-finite-review-fable-20261007-r1`, task
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w1-finite-review-fable-20261007-r1`
completed: PASS with qualifications, no blocking findings. Reproduced Python
checks and both 40- and 53-declaration full checks; inspected all seven inputs,
orbit, parameter header, arithmetic branches, and baseline outputs. A transitive
constant inspection found `enumerate` absent from executable addition, encoding,
and baseline paths. The ordinary coordinate/parameter claim is inspection
evidence, not an interface-level prohibition against advice.

Resolved qualifications:

- `homogeneous_nonsingular` quantifies F5 triples only. Its docstring now says
  so; geometric smoothness relies on the standard discriminant criterion,
  which is not formalized here. No claim about all extension-field triples.
- Equality counting is instrumentation whose increment-per-test match was
  reviewed, not Machine fuel. Valid target d uses d point additions; arithmetic,
  equality internals and linear recursion depth remain uncharged.
- Independence of the Python check is limited as clarified above.
- This record now contains the actual verdict and objections.
- Duplicated literal coefficients are a low-risk maintenance issue left for
  later generalization; finite closure/group-law checks pass. No curve
  parameters were changed in response to the review.

Process correction: the review brief said source was stable, but additional
negative-specification modules, imports, and audit entries were integrated
while the finite source stayed unchanged. The reviewer observed this and did
not deeply review the negative modules. W002 has its own independent Astra
review; the milestone commit explicitly includes BOTH records and their
separate evidence. No claim that Factory reviewed W002 is made.
