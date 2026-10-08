# W017: full fresh-run setup accounting and a valid guest split

Date: 2026-10-07. Status: independently verified generic word-run facts;
integrated audit passed. No query implementation or speed result.

## Motivation and claim

W014 proves actual setup-prefix counts and the raw-run boundary, but does not
export full terminal-run accounting. The W016 Opus review additionally found
that instruction events have no PC field: a preparation/search boundary cannot
be recovered by pretending a PC is present in the event log. This milestone
supplies generic fresh-run accounting and a continuation split justified by an
actual intermediate execution state. It changes no interpreter or cost unit.

Coordinator authored Research/WordRunFacts.lean, frozen SHA-256
`569c58e48dcff70728c21f33f40bdac8217f47f0ae2db8f46c01d8aa4a7ae1d5`.
Native Astra `/root/encoding_review` independently reviewed the frozen statements,
proofs and entry points, recompiled and audited every public claim. Verdict
PASS, no blockers or source changes. WordRun remains at its committed hash
72ced59f481e8aef7f3340f918fa3d24ce8e9ff7ceb497d356f3cf31238b76e6.

## Ten generic claims

- guest_trace and guest_setup_counts: once in the guest phase, only guest events
  are emitted and no new register/heap clear or input-copy events appear.
- run_setup_counts and run_setup_units: every fresh run with I+extra fuel pays
  exactly R register clears, M heap clears and L input copies, regardless of its
  later terminal or exhausted outcome.
- terminal_setup_fuel, terminal_setup_counts and terminal_pays_setup: a terminal
  fresh run cannot stop during setup and pays its entire setup charge.
- terminal_used: actual used = I + actual guestAttempts for a terminal fresh run.
- terminal_ordering: for the same profile/input/budget, terminal total-unit
  ordering is equivalent to guest-attempt ordering, retaining the common I.
- guest_split: when an actual a-fuel guest continuation exhausts in state mid,
  its a+b-fuel continuation equals its actual preceding trace concatenated with
  the b-fuel continuation from mid. It grants no alternate fresh entry point,
  preinitialized input, PC-tagged event or reset cost.

Terminal includes faults; none of these results implies successful output,
query/solver correctness or superiority of either program. W016 still needs to
prove and characterize the actual query prefix state, duration and trace, plus
its common-prefix identity, not merely cite guest_split without its hypothesis.

## Verification and failed attempts

Command: `timeout 60 ./scripts/lake.sh env lean Research/WordRunFacts.lean`
(final exit 0, no warnings). Independent reviewer also recompiled the frozen
source via `./scripts/lake.sh env lean --stdin` with all ten public axiom reports
(60-second command limit). Only permitted propext/Classical.choice/Quot.sound.
All ten public claims are included in Audit.lean for integrated checking.

First author compile failed because Event was ambiguous between two open
namespaces, and unfolding setupUnits too early prevented a syntactic rewrite;
explicit WordRun.Event and delayed unfolding fixed both. Unused simp arguments
were removed. The later guest-split/exact-total extension compiled on its first
attempt. No review checks failed, interpreter source changed or proof escape
was added. No runtime benchmark is relevant to these generic corollaries.

## Remaining scope

These are only reviewed abstract word-action units. No bit/hardware/tape
refinement, solver cost, table/query program, description feasibility, full
challenge family or improved algorithm follows. W016's admitted-size witnesses,
fixed primitive graphs, actual common preparation and all-input query proofs
remain separate acceptance gates. The active ECDLP research objective is open.


Integrated `./scripts/check.sh` passed all **275** named theorem dependency
audits, source screen, build and demo. `git diff --check` passed. Changes are
new corollaries/imports/audits and research records; the interpreter is unchanged.
The amended W016 policy records their role and their limitations before any
actual query implementation or comparison.
