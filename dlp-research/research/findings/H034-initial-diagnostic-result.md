# H034 initial diagnostic: capped, seed-only, no observed gain

Status: the ONE admitted run is consumed. Exit2, valid JSON status
`censored_inconclusive`, aggregate event guard at exactly1,000,000. No retry,
resume, extra seed or source modification. Best supported main exponent remains
1/2; verified improvement NONE. This is partial diagnostic evidence, not a
complete experiment, new-attack demonstration or hardness change.

Admission was committed as c89ebda BEFORE execution. Exact command from
dlp-research:

    timeout --signal=TERM --kill-after=2s 60s python3 -B research/experiments/H034/c4_probe.py --execute --output research/experiments/H034/initial_results.json

Frozen source/protocol hashes matched before execution and remain unchanged.
Artifact SHA256:
`158f562be204de13a1bd1d6785f869a8e9c38d7a3b40b5778fc05aadb4b42f89`.
Artifact size774598 bytes; internal elapsed0.3519427480059676 seconds is only
local guard evidence, not calibrated EC throughput or a benchmark.

## Completed and incomplete evidence

All four fixtures certified and completed their public component checks. The
three explicit q73 cases O,G,-G completed for candidate and primary, including
second-orientation recovery. The separately forced fallback component completed.

Seven sampled candidate arms completed: both seeds for q73,q103,q271, then
seed7 for q8053. Every one stopped successfully during SEED scanning, with
`leaf_reached=false`. All completed arms verified their own scalar and passed
the private harness comparison. Twenty-six admitted sampled control arms
completed; the predeclared omitted controls stayed omitted.

There were212 completed regular arithmetic subtotal checks, all matching their
expected M/S/A/I vectors. These are PUBLIC/Baseline component checks: there
were ZERO candidate_leaf components. No actual candidate graph/leaf lookup or
leaf recovery path was reached. Public paired formulas passing cannot validate
that unexecuted integration or the asymptotic Poisson law.

The cap interrupted q8053,seed19 candidate setup at eager-root vertex32 of98.
That candidate is incomplete; all its controls are untested. One Fp inverse
was interrupted after2M+3S; the retained row correctly distinguishes391 completed
inverses from392 attempted. No partial inverse is removed from completed-kernel
projections. No *_unrecoverable outcomes occurred, so the predeclared D4
case-specific reconstruction issue was not triggered. No replay was performed.

## Matched named-model observations

Below, raw arm events include reference checks. Model columns subtract only
that arm's separately recorded reference sheet and one harness comparison event;
all setup, table, arithmetic, recovery, release and internal verification work
remain. Administrative-model caveats from admission still apply. These are
fixed diagnostic cases, not uniform-input averages or a hardware comparison.

| q | seed | candidate raw | candidate setup | candidate model | primary raw | primary reference | primary model |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 73 | 7 | 12323 | 10475 | 12322 | 5111 | 587 | 4523 |
| 73 | 19 | 12326 | 10727 | 12325 | 7436 | 1201 | 6234 |
| 103 | 7 | 13422 | 10572 | 13421 | 9224 | 1977 | 7246 |
| 103 | 19 | 14052 | 12224 | 14051 | 6230 | 641 | 5588 |
| 271 | 7 | 19185 | 15751 | 19184 | 10777 | 1647 | 9129 |
| 271 | 19 | 20211 | 17187 | 20210 | 10671 | 1647 | 9023 |
| 8053 | 7 | 208201 | 200562 | 208200 | 63155 | 21673 | 41481 |

The candidate used MORE modeled work than the frozen primary in all seven
completed sampled cases. This does not extrapolate to large q, but it rejects
an observed improvement for these cases. The baseline is itself unfavorably
initialized, and the candidate never used its proposed leaf search. Thus there
is no positive headline to rescue by dropping setup or reference costs.

## Reviewer predictions versus observations

The pre-run capacity/omission table matched the artifact exactly: lifecycle
peaks9998,10124,11006,24355 bits and the stated admitted IDs. Root checked both
candidate-only maxima and fallback-stage peaks. These remain logical packed
capacities, not Python/hardware peaks.

The reviewer's predicted cutoff at q8053 seed7 was WRONG: that entire case and
all six controls completed, and seed19 setup began. The claim that seed19 would
be untested in every scenario is therefore rejected. The runtime3–8s prediction
also did not match the artifact, and was already rejected as unvalidated in
the admission. Estimates are preserved in the raw report, not overwritten.

Root read JSON only and checked:
- sum(global event categories)=sum(all phase categories)=reported total=1M;
- every completed subtotal has pass=true and observed=expected;
- completed candidate/primary harness flags, counts and no null classifications;
- declared peaks/admitted control sets against the pre-run table;
- exact metadata source hashes, partial stage and interrupted inverse evidence.
These are artifact checks, not another solver run. Independent native artifact
review is now completed and agrees; no claim extends beyond retained evidence.

## Disposition and next conclusion-changing work

Preserve this losing/limited finite evidence and park this consumed diagnostic.
Do not tune seeds to reach leaves, erase censorship, or call public checks a
full solver trial. The mathematical sparse/thickened hypothesis remains a paper
hypothesis with no full-work gain. H035's shared coordinate/hash optimization
now needs its own competent-baseline/prior-art cost decision. It must improve
both arms consistently; an optimized-candidate/unoptimized-baseline comparison
would be invalid. No new implementation/run is admitted by this result.

Validation after artifact capture: `./dlp-research/scripts/check.sh >
/tmp/ecdlp-h034-result-check.log 2>&1` from repository root, exit0,366 existing
audits. It does not execute this probe. Root also checked every recorded source,
support and interpreter SHA256 against current bytes. The output is preserved
unchanged. No new Lean claim or Audit entry was introduced.

Process correction: root initially sent the artifact-review request as a message
to the already-completed native reviewer. That did not start work. Agent inventory
exposed the mistake; an explicit followup_task now starts the independent review.
No review result or live work is claimed for the intervening idle period.

Independent native Astra review COMPLETED after explicit followup: confirmed
artifact/source hashes, event sums,7seed-only candidates,26controls,212passing
subtotals,0candidate-leaf components, all seven matched-cost rows, capacity
consistency, no null outcomes and exact partial inverse/cap location. It agrees
that dynamic graph/leaf behavior remains untested and approves only recording
this finite censored result. No solver replay, PRNG reconstruction or new
experiment was performed. This supersedes the earlier pending-review status.
