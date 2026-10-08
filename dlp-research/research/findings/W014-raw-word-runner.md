# W014: charged initialization and raw-input word execution

Date: 2026-10-07. Status: independently verified abstract runner; no solver or
hardware/tape-cost claim. Integration check passed.

## Claim and falsification target

The accepted W011 contract admits executable genuinely partial initialization,
a single setup/execution fuel budget and a ledger projected from actual semantic
events. Generic proofs establish initialized contents, the exact setup schedule,
fuel conservation, terminal monotonicity and exhaustion behavior. Falsifiers
include an exposed unwritten cell, erased setup charges, a free halt/fault,
delayed normalization at zero fuel, or a ledger unrelated to executed actions.
The source is the reviewed W011 contract, not a new literature/attack claim.

Native Astra `/root/encoding_review` implemented only Research/WordRun.lean;
coordinator independently reviewed, tested and integrated it. No child agents,
shared-file edits, staging or commits by the implementer. Frozen source SHA-256:
`72ced59f481e8aef7f3340f918fa3d24ce8e9ff7ceb497d356f3cf31238b76e6`.
Previously accepted WordCore/WordCodec are unchanged, committed in d830782.

## Definitions and generic evidence

PartialState contains optional finite register/heap cells, an action cursor and
readiness witnesses. Initial cells are none. setupStep clears R registers, then
M heap words, then copies L raw bits to the input region, one event per actual
action. finishSetup uses Option.get with readiness proofs, never a fallback for
an unwritten cell. Finite-index functions are the logical partial-store
representation; completion materializes vectors. This is no physical storage
or host-allocation bound.

Phase normalization happens before checking zero fuel. Each setup action or
actual WordCore.step attempt consumes one unit; halt/fault/invalid-PC attempts
are charged. Raw run takes fixed profile, admitted program, input Fin L→Bool
and fuel. Internal continuation/setup helpers are not fresh program-cost entry
points. Run outcomes distinguish halt, fault and exhaustion. A chronological
trace records actual actions; ledgerOf is its per-kind count, not a freely
chosen label or user-supplied counter. Completed loads/stores count only
continued dispositions, while faulting opcodes still count attempts.

The 38 public theorems include:

- run_conservation, run_ledger_conservation, run_terminal_mono and
  run_exhausted_remaining. Extra fuel preserves a terminal result's state,
  trace and used count and increases only remaining fuel.
- advanceSetup and completeSetup cursor, length, schedule and count facts,
  tied to actual setup transitions. completeSetup_counts gives R/M/L counts.
- initialized_registers_zero, initialized_input, initialized_rest_zero and
  initialized_pc_zero; heapAt additionally specifies exact partial heap contents.
- run_before_setup, run_at_setup and run_setup_boundary: before I=R+M+L no guest
  step occurs; budget I exhausts in the initialized guest state; I+extra runs
  that exact setup prefix followed by the shared remaining guest budget.
- Ledger setup/guest partition and used identities. The normalized complete
  setup fallback is proved unreachable. Pure executable definitions determine
  the next state; there is no nondeterministic choice of execution.

No separate convenience theorem exports full-run R/M/L counts after arbitrary
additional guest execution: the actual setup prefix, its counts and boundary
are proved, while the ledger remains a trace projection. Further refinements
may derive that corollary; it is not silently counted as an existing theorem.

The output observer returns only the fixed L..L+O−1 words of a halted state.
Produces compares expected output only through a fresh raw run. Kernel checks
show untouched zeros can satisfy a zero expectation, wrong expected output
fails, and fault/exhaustion certifies no output. This observer is not an executed
validation routine or an all-input lookup/ECDLP correctness assertion.

## Independent validation

Author's final command:
`timeout 60 ./scripts/lake.sh env lean Research/WordRun.lean` (exit 0, no warnings).
All 38 theorem audits were run by author and independently by coordinator using
`./scripts/lake.sh env lean --stdin` with the frozen source plus every public
`#print axioms` declaration (60-second command limit). Only permitted
propext/Classical.choice/Quot.sound appeared. All public claims are in Audit.lean.
Coordinator read the operational definitions, setup/content proofs, ledger
partition, terminal behavior and output predicate against W011. Verdict PASS,
no blocker; no frozen-core changes or proof escapes.

Coordinator independently wrote scripts/word_run_checks.lean, SHA-256
`acbedd25618f81ca27cb26a8d4cfa207ded42dec624eaca9976cb14387cf703e`.
Commands: `./scripts/lake.sh build Research.WordRun`, then
`timeout 60 ./scripts/lake.sh env lean scripts/word_run_checks.lean` (uses #eval,
not --run). Both exited 0. Its observed PASS line is archived verbatim in
W014-runtime-results.txt. No independent runtime check failed.

These compiled evaluations exercise manually specified raw-input programs:
copying a bit through executed load/store at 17 fuel budgets; an infinite jump
loop at 25 budgets; a conditional countdown at 19 budgets; load-fault attempts
versus completed loads; a committed store followed by invalid-PC fetch; and
empty-code setup/invalid-attempt charges. Copy takes setup8+guest5=13 units;
countdown takes setup8+guest7=15, with two const, two sub, two branch, one halt.
Assertions include exact remaining fuel, phase, opcode/ledger counts and output.
They are compiled execution evidence, distinct from kernel proofs and timing.

## Failed proof attempts retained

Intermediate author compiles failed on split/unfold/Fin-Vector reductions,
addition rewrites, an invalid reserved binder `prefix`, and Decidable synthesis
for conjunctions. Two initial ledger proof approaches hit default heartbeat
limits; finite opcode partition and count induction fixed them without raising
limits. Unused simp arguments were removed. There was no reported runtime
counterexample or command timeout. Parent runtime script compiled and passed
on its first run. None of these proof-development failures was hidden or
interpreted as an algorithmic result.

## Limits and next step

One unit is the reviewed checked-word action abstraction, not a CPU instruction,
bit operation, tape transition or physical memory access. Multiplication and
division remain unit abstract operations at arbitrary W. Source-input production,
code loading/decoding and interpreter metadata/trace storage remain outside
these units. Profile capacities are not total host/peak live memory. No family
word-growth bound, tape refinement, complete solver, calibration or speedup is
supplied. Machine/Problem/Goals remain unchanged.

W016 separately drafts a fair sorted-table lookup challenge satisfying the
Opus N1–N5 advice/input/domain/setup/unit gates. It is not accepted yet. No
linear/binary query implementation is authorized until the exact new contract
receives independent review; external query costs cannot silently price BSGS's
internally generated giant keys.


Final integrated `./scripts/check.sh` exited 0 with **265 theorem dependency
audits**, compiled demo and source screen. `git diff --check` passed. Staged
paths will include only the runner, its independent checks/evidence, imports,
audits, README and checkpoint; the unaccepted W016 draft is separate work.
