# H024 detected-reversal escape: finite arithmetic premise rejected

2026-10-08. Verified improvement NONE. Keep the independently checked cheaper
slope-state component, but park this detected-then-double schedule under its
stipulated same-useful-hit-law10% saving hypothesis. Do not enlarge this probe.

## Frozen test and result

Native Sol designed and statically reviewed the root implementation. Root ran
ONE bounded experiment on the four predeclared increasing synthetic fixtures:

    timeout 60s python3 -B research/experiments/H024/escape_probe.py > research/experiments/H024/initial_results.json

Working directory: dlp-research. Exit0; run_status completed; no cap/error.
The implemented diagnostic ledger records150590 events (not CPU operations,
bit complexity, full solver work, or a batched-kernel benchmark).

| p | prime group order q | attempted transitions N | escapes D | disposition |
|---:|---:|---:|---:|---|
|59|73|18|9|permanent block rejection|
|101|103|17|9|permanent block rejection|
|251|271|13|9|permanent block rejection|
|8191|8053|15|9|permanent block rejection|

Eight labels per fixture were generated before trajectories, from the frozen
32-bit LCG seed7 xor p xor q. At most32 transitions per start, no replacements.
The ninth escape stops the fixture: even if all unexecuted slots were regular,
D/N>=9/256>21/620, violating the strict finite-block arithmetic gate. No iid,
confidence interval or extrapolation from these small fixtures is asserted.
All four terminate early for the declared reason; unused starts are not hidden
failed trials. They are unnecessary for this permanent finite-block verdict.

The gate derives from 4M+S+rho(10M+3S), S/M=.8, versus .9*(5M+S), under
an ASSUMED equal useful collision stopping constant. This diagnostic refutes
that finite-block rate premise; it does not measure a rho stopping constant,
rule out a compensating collision gain, or prove an asymptotic lower bound.
Reference reconstruction, scalar label checks, recovery and known exceptions
are paid diagnostic overhead, not a model of the optimized batch kernel.

## Independent evidence audit and qualifications

Native Astra reviewed recorded artifacts without rerunning. Root independently
checked source/protocol/H018-base hashes, phase-event sum and trajectory totals.
N and D reconcile on every completed block; pending_transition is false.
Public p/q primality, nonsingularity, generator equation, qG=O and Hasse
uniqueness are certified in the executed code. Full-affine reference checks
confirm ordinary transitions; label checks cover entered loop states.

The ninth escape exits before the next loop's canonical/label check. Therefore
do not claim every final escaped point was separately rechecked. Its reversal
predicate and corresponding affine translation WERE checked before D increments;
that is sufficient for the recorded rate rejection. Direct trace-field updates
are not all individually charged despite broad wording in the frozen protocol;
150590 is the implemented bounded-word ledger, not exhaustive trace-write work.
This discrepancy has no bearing on N,D or a claimed performance win (there is
none). It is retained, not repaired with an unnecessary rerun.

Static reviewer also clarified that pending_transition=true means possibly
unfinished work: a cap can happen before N increments. No cap occurred here.
The external timeout and -B were used as requested. The preliminary attempt to
edit that wording used an incorrect dlp-research prefix from within that cwd
and raised FileNotFoundError; the following experiment command nevertheless
ran correctly and returned0. The old protocol bytes/hash remain preserved.
There was no failed/hidden numerical run, warmup, tuning or parameter change.

## Decision

Stop this schedule's numerical investigation unless a new, explicit mechanism
changes the escape or useful-collision analysis. Do not turn its negative result
into a prohibition on all slope-coordinate walks. The next useful branch is
an explicit many-family coverage construction compared to both proved two-family
BSGS and the separately labelled empirical negated-grumpy prior art, with matched
memory/tails/blocks. No generic Lean infrastructure or dashboard change.
