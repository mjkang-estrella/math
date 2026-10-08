# H025 finite signed-layout result

2026-10-08. Verified limited result, independently audited. **No verified
complete-work ECDLP improvement.** The classical square-root reference remains.

## Question and frozen comparison

Does either fixed signed arithmetic-progression layout A/B save at least5%
of uniform-target generated keys against the GWZ-style control at BOTH509
and1009 under experiments/H025/protocol.md? The exact schedules, signed
comparisons, paid O/G/Q records, block size3, key caps69/96 and complete fallback
were frozen before the sole run. Allq scalars are included; there is no narrowed
secret range, inverse advice or random sampling. Seeds are not applicable:
this computes the exact finite distribution over every scalar.

The control is the declared three-family schedule under this wrapper, not a
reproduction of a published runtime constant. Known many-giant/shift techniques
are prior art, not a discovery. See H024-manygiant-coverage.md and
H025-layout-mathematical-review.md for primary sources and mathematical scope.

## Sole numerical command and result

From /home/mj-kang/Documents/Dev/math/dlp-research:

```sh
timeout 60s python3 -B research/experiments/H025/coverage_probe.py > research/experiments/H025/initial_results.json
```

Exit0. All six cases completed. One global ledger recorded426964 bounded-word
instrumented events, below1M; no cap or assertion failure. This count is the
coverage diagnostic's work, not solver work or measured EC throughput.

| q | Control exact mean | A exact mean | B exact mean | B key saving |
|---|---:|---:|---:|---:|
|509|12183/509|11433/509|10836/509|11.06%|
|1009|32457/1009|32172/1009|29745/1009|8.36%|

The exact gate is20*N_candidate<=19*N_control. B passes both; A passes509
but fails1009, so A fails the declared joint gate. This parks A for this finite
screen, not a proof against all sizes. No labels, shifts or order were retuned.

Maximum generated keys through full coverage were60/57/57 at509 and81/81/81
at1009 (control/A/B). Peak search records including three inputs were63/60/60
and84/84/84. These exclude EC support/scratch. All main failure counts and
expected clearing counts were zero: fallback correctness was statically reviewed
but the numerical run did NOT exercise fallback. No claim of fallback runtime
validation follows from this artifact.

## Independent review and verification

Native Astra /root/h007_additive_relations performed a NEW static correctness
review before execution, then a separate NEW artifact-only audit after execution.
Both GO. Native Sol /root/h010_early_dependencies performed the NEW pre-run
budget review: GO for one capped run, inner recurrence at most14 events with
setup/outer/input work extra, no guarantee all cases would fit. Root implemented
and fixed phase attribution and pending-block/partial-array preservation before
the run. Neither static reviewer imported or ran the probe.

Artifact audit found no discrepancies: hashes match; both phase/category totals
sum to426964; first-discovery sums equal block survival sums; initial zero-cost
hits are exactly0,+1,-1; schedules, negative extensions and actual family lengths
agree; cross-only unions obey their ceilings; record maxima match; all discovery
times are completed-block costs and no pending blocks remain. Root separately
parsed the recorded JSON and checked hashes, event sums and mean identities.
Artifact inspection was not a second experiment.

Recorded SHA256:
- source:898300516b9beb3af07c20567c76bef312d7657b5197cd63f102745675722628
- H018 dependency:0865eac9be57655ec1ddde3d76f2aba79bff91ea5384110a7d2205041a764da7
- frozen protocol:8844d850289d406284725270c70b70b3d7d59809fda6250f532f429fb2e7f252

Prior cross-provider review task IDs and objections remain in
hypotheses/H025-layout-review-register.md. Its raw budget estimates, equal
three-family lengths and recommendation to dropzero were not adopted: the
accepted reconciliation and concrete code were reviewed independently.

## What this does and does not establish

B uses fewer generated keys in this exact finite comparison. The absolute
mean savings are1347/509 and2712/1009, only about2.65 and2.69 keys. Candidate
initialization and four frontiers may outweigh them. Arithmetic, scalar setup,
lookup/sorting, exceptional points, reconstruction/verification and total memory
are not measured by the diagnostic. Equal key caps are not equal total memory,
and this is not an equal-memory comparison against H019's smaller two-family
reference. Input and same-family linear terms, rounding, block quantization and
shift geometry may dominate at these tiny sizes. No curve implementation,
full-solver gain, improved exponent or full-size hardness change is demonstrated.

Next conclusion-changing work: independently assess the unchanged B layout's
scaling geometry and a frozen larger-size screen with explicit setup/memory
break-even accounting. Do not infer a constant from these two values or tune
the same fixtures. The coverage enumerator's quadratic enumeration is a testing
method, never proposed as the faster solver. No broad Lean extension is needed
for this finite result; no Lean/Audit claim changed.

Validation is recorded in STATE.md with the checkpoint. The research goal stays
active; current supported complexity remains square-root, verified improvement
against the accepted full-work baseline NONE.
