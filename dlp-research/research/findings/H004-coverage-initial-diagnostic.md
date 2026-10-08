# H004 P1: capped exact coverage test loses to a fixed two-list rule

**Finding:** the frozen four-list schedule has greater mean emission count than
the same predeclared signed two-list c=2 rule at every tested q. This rejects its
observed emission-count advantage on those inputs; it proves neither asymptotic
impossibility nor a complete arithmetic/runtime comparison. Verified ECDLP gain NONE.

## Frozen protocol and independent preflight

Native Sol proposed P1; separate native Sol /root/small_curve implemented only
coverage_gate.py. Native Astra /root/encoding_review independently checked the
mathematics and then source, approving one run. Root also inspected the source.
No preliminary coverage test consumed or reset the cap. Implementer's only check:
`PYTHONPYCACHEPREFIX=/tmp/H004-coverage-pycache python3 -m py_compile research/experiments/H004/coverage_gate.py`, exit0.

Source SHA256: `8922240d5f2eabf7e9113122cac849210cf573e9a666f19b26c41b82f28b285b`.
Protocol H004-progression-coverage-protocol.md SHA256:
`011ee6254fcd39829a862552047ad016d82317f6925813497b1ab9ec8e24ab80`.
Source reviewer performed only reads/hash, no arithmetic execution. Clarifications
frozen before the run: T(0)=0, weighted order0,0,1,2, all valid negative collisions,
and separate censored versus fully charged fallback means.

Root command, ONCE from dlp-research:
`python3 research/experiments/H004/coverage_gate.py --output research/experiments/H004/coverage_initial_results.json`.
Exit2 is the explicit global event-budget stop, not completion or a passed solver.
Exactly1,000,000 charged algorithmic events; sum of the event vector agrees.
Elapsed before output finalization0.254974998999387seconds is diagnostic metadata,
not an EC throughput or hardware estimate. Raw JSON643296bytes, SHA256:
`118bc3cda44688cfbeb12267524f494fdb17ef26e9d2f92d156374aa8db3b19b`.

## Actual complete observations

Four full profiles(q31,61,127,251),58 completed configurations total. At q509,
P1 and all four two-list configurations complete, plus the first three-list
configuration. The next three-list run stops partway through emission44. Other
q509 configurations and all q1021 configurations did not run. No missing result
is inferred or completed after the cap.

The same predeclared baseline for all rows is b=(0,1),s=(1,−M), round robin,
M=floor(sqrt(2q)). This is c=2 in the declared grid, not an online best-grid oracle.
All use the full uniform scalar domain, equal output cost and the same sign/identity
handling. Means below include the fixed fallback where needed.

| q | P1 mean outputs | Fixed B2 mean outputs | P1 uncovered at prefix cap |
|---|---:|---:|---:|
|31|7|6|0|
|61|554/61|502/61|0|
|127|1537/127|1450/127|0|
|251|4060/251|3908/251|0|
|509|11460/509|11222/509|1|

At q509 even P1's censored lower bound11412/509 exceeds B2's exact complete
mean11222/509, so its loss there does not rely on the fallback choice. Earlier
rows have complete coverage and require no fallback. P1 can look favorable
against the weaker c=1 comparator; omitting stride choice would be misleading.
No statistical confidence interval is needed for exact enumeration of these
finite full domains. They are not sampled larger instances or an asymptotic proof.

## Cost scope, partial records and next action

Events count integer/modular arithmetic, Euclidean inverse steps, pair visits,
coverage/metric operations and setup. Nested inverse observations are not added
again. Modular-operation units include their reduction; integer bit complexity,
Python/metadata/JSON/I/O/allocation/hash internals and physical traffic are excluded.
This is a bounded diagnostic ledger, not the candidate solver's cost model.
Offline scalar-indexed hit arrays are never available as solver advice.

Partial arrays can stop within an emission or insertion: their recorded emission
count does NOT certify a complete prefix. Only completed configurations are used
above. A stop during reference aggregation would leave completed configuration
means valid but the profile incomplete. Source preflight explicitly checked these
interpretation boundaries. Independent native Astra JSON audit PASSED:58 completed configurations,9,164
recorded hit entries, all declared parameters/metrics/digests and exact category-by-
category reconciliation to1M events. It performed no collision enumeration,
inverse calculation, coverage rerun or completion of partial data. The audit
confirmed the fixed c=2 comparator and the stronger q509 censored-bound loss.

Decision: do not fund EC implementation or a larger run of this frozen P1 solely
from these results. A changed schedule requires its own structural rationale and
fresh protocol; these data do not exclude every four-list design. P2/P3 remain
unsupported cost hypotheses. Other H004 algebraic proposals are separately reviewed.

Validation: `./scripts/check.sh > /tmp/ecdlp-h004-coverage-check.log 2>&1` exit0.
No new Lean claims, so Audit.lean unchanged. Source/digests and finite evidence
support only the stated diagnostic; no complete ECDLP baseline was benchmarked.

Durable independent audit: `research/experiments/H004/audit_recorded.py` is the
exact assertion body exported by the reviewer after its successful heredoc run.
Reproduction command from dlp-research: `python3 research/experiments/H004/audit_recorded.py`.
Root inspected and copied that existing body without rerunning it. Reviewer output:
`PASS 58 complete configs; 9164 complete hit rows; exact global vector reconciliation; partial [(509, 'baseline3_6', 44, 44, 231)]`.
It validates stored evidence, not a fresh experiment or a missing-prefix completion.
