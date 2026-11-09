# W006 rational-map primitive screen — frozen protocol

2026-10-08. One permitted execution after independent symbolic audit and freezing
candidate, runner, protocol and instrumentation hashes. No preflight candidate
runs, pilot corpus, reruns, parameter search, larger primes or silent budget
extension. If a decisive symbolic obstruction makes the screen redundant, report
that and do not run. All artifacts use research/findings/W006-rational-review*.

Hypothesis: a genuinely nonmonomial member F_a can create useful fixed-point
basin growth without acquiring a smooth group exponent. Finite evidence cannot
establish asymptotic improvement. Parameters and primes below are frozen before
any candidate observation.

Ordered primes: 5,7,11,13,17,19,23,29,31,37,41,43.
Ordered integer parameters for every prime: 0,1,3,2,5.
Exactly 60 cases. Ordered checkpoints k: 0,1,2,4,8,12.
Each case exhausts H_p={(u,v):0<=u,v<p,u^2+v^2=1}.
Enumeration is evaluation-only and must be counted separately; no composite
candidate is given hidden prime labels or a table. No composite benchmark here.

Candidate boundary: p,a,u,v for ONE map transition only. It evaluates the
literal uncancelled denominator, checks its norm, and returns either the next
pair or DENOMINATOR_NONUNIT. It does not receive group orders, roots, graph
tables, image sizes, labels or a point-selection oracle. All modular arithmetic
and gcd/inverse operations are charged. p in this boundary is an explicitly
prime primitive test, not a disguised factorer contract.

Evaluator obtains the transition table by applying that boundary once to each
group point. Derive all later graph facts from this saved table, without
unrecorded repeated candidate executions. Record every point, output or
nonunit, denominator norm, input/output norm check, transition arithmetic,
and exact outcomes. At every checkpoint report image size among trajectories
whose denominators remain units; cumulative first-hit counts at +/-1 including
time zero; first denominator-failure counts; and surviving nonhit counts.
Retain the initial-group-size denominator throughout.

Also record all directed cycles and their lengths, which cycles contain
+/-1, total eventual fixed-point basin, eventual denominator basin, and remaining
cycle basins. Do not mistake a small image for large useful basin. Cases with
exceptional a modulo p remain in the record. Controls a=0,1,3 are paid reference
cases, not excluded from cost or evidence. The main diagnostic comparisons for
a=2,5 are against these controls, with the exact same initial group.

Budgets: 60 seconds whole execution including group setup; 1 second per case;
20,000 recorded arithmetic events per case; 32 MiB soft traced Python allocation;
1 MiB retained evidence per case and 16 MiB total. Freeze the event definitions.
Any unstarted/capped/error case is UNKNOWN and remains in the 60-case ledger.
No randomized seeds or outcome filtering. Standard-library Python only.
One execution marker prevents accidental reruns. Run scripts/check.sh after
scratch-code changes and save the result separately from this experiment.

Rejection scope: any proper nonhit cycle disproves full eventual attraction for
that particular p,a. Equality with a power-map control can expose repackaging.
Neither statement alone disproves all adaptive schedules or factoring. Report
the exact failed assertion rather than inventing a global theorem. If all
finite diagnostics look favorable, disposition remains INCONCLUSIVE for a
uniform polylogarithmic capture claim.

