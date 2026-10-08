# W012: finite public-width tuning of signed BSGS

Date: 2026-10-07. Status: finite experiment independently reviewed and accepted within scope.
This is a bounded continuation of W006 using its unchanged executable engines,
not a new algorithm, cost model, hard family or calibrated performance claim.

## Hypothesis and falsifiers

While W011's exact cost contract is drafted, test whether the W006 signed choice
m=ceil(sqrt(q/2)) is dominated when sorting, lookup and sign-handling event sums
are considered together. A dominating configuration has no greater total in
any of the five instrumented classes and a strictly smaller total in at least
one. This would falsify competitiveness within that declared event vector and
search domain. Any wrong scalar, omitted scalar, skipped admissible width,
counter inconsistency or analysis error invalidates the experiment instead.

This is deliberately a finite public-parameter study. The scalar domain remains
complete. Curve selection is the three smallest existing W004/W006 coordinate
instances, with q=7,19,31. For each, ordinary widths are 1..q and signed widths
1..(q+1)/2 (these odd orders satisfy W006's strict 2(m-1)<q guard). Larger curves
and widths beyond q are outside this study. No general optimum is claimed.

## Protocol and evidence

```
timeout 60 python3 scripts/signed_tuning_experiment.py > research/findings/W012-signed-tuning-results.json
```

The script revalidates primality, discriminant, point set and full generator
orbit, then invokes W006's solver independently on every target/width pair.
Each invocation rebuilds/sorts its table. It sums adds, lookup_comparisons,
sort_comparisons, negations and canonical_order_tests across all secrets.
The retained data include every configuration and its explicit dominating
configurations, not just favorable selections. A one-million-event workload
guard applies to these instrumentation counters, not binary-tape transitions.

All 2085 scalar/width cases passed, comprising 11+29+47 configurations on the
three curves and 128691 counted events. The default signed widths 2,4,4 were
undominated in their respective finite event-vector sets. Thus the proposed
Pareto-domination falsifier did not occur. This neither establishes an optimal
weighted cost nor confirms a practical improvement. Many configurations remain
incomparable; memory and internal work are absent from this vector.

## Uncalibrated sensitivity calculation

As a separate calculation from the same recorded event sums, assign addition
weight A in {1,4,16,64} and all four other class weights1. These numbers are
hypothetical, not measurements or accepted machine weights. Search the same
full configuration sets and retain all minimizing ties.

| q | A=1 | A=4 | A=16 | A=64 |
|---|---|---|---|---|
| 7 | ordinary m2 | ordinary m2 | ordinary m2 | ordinary m2 |
| 19 | ordinary m2 | ordinary m2 | signed m3 | signed m3 |
| 31 | ordinary m2 | ordinary m4 | signed m3 | signed m3 |

This shows why addition-only tuning cannot supply a unique full-cost choice.
The objective is a sum over all scalar targets (equivalently a uniform-secret
mean on each finite curve), not the worst-case addition objective used for the
W006 default. It does not refute the earlier observation about worst-case
addition minimizers, prove randomized-algorithm semantics, or justify selecting
hardware weights after seeing favorable results.

Field/bit work, key construction, index access, allocations/copies, register
work, peak memory and elapsed time remain excluded. Dominance of these partial
vectors need not imply dominance after missing components are included. No
whole-cost, asymptotic, secp256k1 or tape inference is accepted.

Native Astra `/root/encoding_review` receives the frozen script/data for an
independent reproduction, scalar/width coverage audit and dominance/proxy check.
The experiment is separate from Sol's live W011 contract-writing task.

## Independent review and decision

Native Astra: PASS, no blockers. It reproduced the exact archived JSON and
independently checked full scalar/width coverage, ordinary/signed first-hit
addition totals, negation-counter relations, aggregate sums, every dominance
relation and all proxy minimizers. No tests failed. All three default widths
are undominated, yet none minimizes the four displayed proxies. This is not
per-scalar dominance or worst-case optimization, and does not contradict W006.
Accept only this finite partial-event-vector result with the stated exclusions.

`./scripts/check.sh` also passed all159 existing theorem audits and smoke output
before commit. This wave added no Lean claim and changed none of the engines.
