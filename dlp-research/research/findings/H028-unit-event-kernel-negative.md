# H028 regular-kernel negative result under equal-unit events

2026-10-08. Root derived the consequence of the accepted exact block ledger;
NEW native Astra and Sol reviews independently confirmed the literal-kernel
scope. No new experiment or instance was needed. This changes the next action:
do not build a full solver merely to seek a squaring-based unit-event gain.

For the named h kernel, canonicalization computes -h and compares representatives
for every emitted key. The competent x kernel shares xC+xJ for each side pair.
For an identical regular block with k centers and ell side pairs, exact difference
in primitive work is

    Delta = -2kell*S + 3k(ell+1)*Af + k(2ell+1)*C.

The terms count actual saved squares, added field operations and added canonical
comparisons in these fixed straight-line kernels. They are not a worst-case
false-match upper bound being incorrectly used as a necessary rejection.
Under the current equal-unit primitive convention S=Af=C=1,

    Delta = k(3ell+4) > 0.

At ell=8 this is28/17 additional events per emitted key, BEFORE additional h
state, setup and table metadata. Thus eliminating output squares alone gives
no positive regular-generation hypothesis in that unit-event model.

## Conditional negation improves the kernel but does not reverse this result

Astra identified the conventional improvement: compare h to(p-1)/2, and negate
only upper-half representatives. If Nminus emitted keys need negation, the exact
regular-block difference becomes

    Delta = -2kell*S + [k(ell+2)+Nminus]*Af + k(2ell+1)*C.

The equal-unit difference is k(ell+3)+Nminus, still positive. The threshold's
setup and all remaining control/storage costs must also be counted. This variant
is a proposal, not a change to the already frozen diagnostic source or results.
It is not a theorem rejecting other key representations or arbitrary algorithms.

## Scope and research decision

These inequalities compare the same regular blocks and points. They do NOT by
themselves compare full runs with different stopping positions, exceptional
operations or table layouts. A small deterministic-seed benchmark could show a
lower total merely from earlier stopping; that would not vindicate the kernel
rationale or prove an expected improvement.

Sol's independently proposed27-solve cost-vector diagnostic is NOT admitted for
execution at this checkpoint: its unit-event hypothesis is poor value after the
paper result. Proposed sources, targets and controls can be revisited only for
an explicit remaining weighted-field or end-to-end timing question. Unknown
operation weights cannot turn a symbolic projection into a complete-work gain.
No rescaling, normalized prefix cost or instrumented timer is a physical result.

The larger-fixture source has been implemented but NOT run; its separate static
review continues. Source correctness approval alone does not establish that
running discovery is now useful. Root is separately reviewing whether a tightly
bounded production-kernel falsifier would justify further full-solver investment.
Positive kernel timing would still not establish whole-solver improvement. If no
useful objective survives, preserve these results and return effort to distinct
algorithmic hypotheses rather than broad refinement around this candidate.

Current best supported generic exponent remains1/2; verified complete-work
improvement NONE. High-memory applicability and lack of full-size GPU calibration
remain explicit. No new Lean/Audit claim or numerical experiment.

## Disposition after independent calibration decision reviews

Sol judged one small production-kernel timing falsifier useful only if it reused
an actual intended implementation. Astra independently specified a possible
fixed32-round direct-Python test, but qualified it on Python being the intended
target and advised against larger fixture discovery solely for that calibration.
Root does not choose Python as a production research target merely because its
prototype is convenient. No such microbenchmark or larger solver is admitted.
The candidate is PARKED as a conditional high-memory weighted-arithmetic result.
This is not a proof that its gain premise fails in every representation.

The completed initial diagnostic, paper fibre/visit bounds, exact unit-event
negative and source-reviewed unexecuted fixture program are all retained.
No diagnostic rerun or new numerical instance occurred. Reopening requires a
named implementation/cost regime with positive complete-work headroom and a
cheap falsifier capable of changing that assessment. The active overall ECDLP
research goal continues with other concrete mechanisms; this candidate's parking
is not goal completion or a blocked condition.

Validation: ./scripts/check.sh > /tmp/ecdlp-h028-unit-kernel-check.log 2>&1
exit0,366 existing audits. Only pure AST source parsing checked the new Python
syntax; its behavior has NOT been numerically executed. No Lean/Audit changes.
