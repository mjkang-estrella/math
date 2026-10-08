# H002 A1 initial diagnostic: valid tiny identities, no solver evidence

Status: initial run intentionally INCOMPLETE at the declared event cap; independent
JSON-only evidence review completed and accepted with the limits below. Best supported ECDLP work remains the
applicable square-root baseline; verified improvement NONE.

## Frozen protocol, review and exact command

Native Sol `/root/small_curve` implemented the two-file diagnostic, syntax checked
only. Source SHA256 `3957ba8f020545339793f2cac6d09f2f9e39c80ac1d6ccdb38634d27d6849554`.
Protocol at review SHA256 `dac3e9649496a335f4adb669ad8ab1963b441607c2ed3e7a1c5efe1e9e92fa4c`.
Factory Fable5.1 `ecdloop-h002-eds-code-review-fable-20261008-r1` independently
approved a run after desk review; exact task ID in expanded register and raw
review in H002-eds-code-review-raw.md. Root also read the complete source.

From dlp-research, root ran ONCE:

```
python3 research/experiments/H002/eds_diagnostic.py --output research/experiments/H002/eds_initial_results.json
```

Exit2, status `incomplete_budget_stop`, exactly1,000,000 instrumented events,
observed arithmetic elapsed0.23372573603410274 seconds. This Python observation
excludes final hashing/JSON output and is not an EC throughput or solver benchmark.
No cap reset, skipped case, enlarged budget, curve search or post-result sign
choice occurred. Full raw JSON is retained, including the partial final case.

## What actually completed

All five curves were requested, but only four reached validation before the cap.
Six of eleven generator cases completed. The seventh, p127/q139 seed19, completed
its pointwise table and five of six correlations before stopping. Seed43 there
and all p251/q257 cases were not run. Do not claim full prescribed scaling.

| Curve p, order q | Generator | c | Case status | Retained rows |
| --- | --- | --- | --- | --- |
| 13,17 | (0,2), fixed | +1 | complete | 16 |
| 19,23 | (0,16), fixed | −1 | complete | 22 |
| 59,73 | (34,35), seed7 | +1 | complete | 72 |
| 59,73 | (4,47), seed19 | −1 | complete | 72 |
| 59,73 | (4,12), seed43 | +1 | complete | 72 |
| 127,139 | (71,58), seed7 | −1 | complete | 138 |
| 127,139 | (6,124), seed19 | −1 | INCOMPLETE, correlations | 138 |

Every retained row passed the independently computed pointwise phi versus
phi(P)^(n²)*W_P(n) identity at n=k and n=k+q, the corrected character c^n identity,
and quasi-periodicity. Thus530 rows give1060 retained index checks. This is finite
arithmetic evidence, not a general Lean theorem or a full ECDLP refinement.

The two fixed fixtures give phi(P)=4 mod13 and18 mod19, while W_P(1)=1.
Thus n=1 also explicitly contradicts the old pointwise n²−1 formula, which
would predict phi(P)=1. This is an independently implemented finite counterexample
to that normalization, without rerunning the earlier over-budget scratch script.

## Fixed orientation correlations, without selecting winners

Columns are the six predeclared offset families, all with frozen +1 orientation.
Entries are exact signed numerator/eligible count. Correlation is twice advantage
over one-half; exclusion may make one-half weaker than the majority-label baseline.

| q, generator seed | (0) | (0,1) | (0,1,2) | (0,1,3) | (0,2,4) | (0,1,2,4,8) |
| --- | --- | --- | --- | --- | --- | --- |
| 17, fixed | 0/16 | −5/15 | 0/14 | −6/14 | 2/14 | −2/12 |
| 23, fixed | −2/22 | 1/21 | −8/20 | 2/20 | 6/20 | 12/18 |
| 73,7 | −20/72 | −11/71 | 2/70 | 12/70 | −12/70 | 10/68 |
| 73,19 | −12/72 | 5/71 | −10/70 | −8/70 | −8/70 | 6/68 |
| 73,43 | 12/72 | 5/71 | 10/70 | 8/70 | 8/70 | −6/68 |
| 139,7 | 6/138 | −23/137 | −8/136 | 10/136 | −2/136 | 12/134 |
| 139,19 PARTIAL | 30/138 | −19/137 | 20/136 | −2/136 | 18/136 | NOT COMPLETED |

All41 recorded family results and their three predeclared shuffled-label controls
remain in JSON. Three shuffles are not a significance test. Do not turn the
largest absolute correlation or a retrospectively flipped sign into a held-out
predictor. Each fixed +1 family has nonpositive correlation on at least one
completed case. This defeats an unconditional claim of positive orientation on
all these curves, not a learned sign/selector or the broader EDS mechanism.

The q73 seed19 and43 generators are negatives. Since phi(−R)=−phi(R) and
chi(−1)=−1 at p59, negating the generator flips odd-family predictions and
preserves even-family predictions at each k. Their observed sign changes are
not independent successes/failures. The protocol already allowed dependence;
the actual dependence is now identified. The c=+1 cases remain legitimate
point predicates; even families are not null controls.

## Work accounting and verdict

The raw vector includes187828 field multiplications,2970 field additions,
25676 field subtractions,1826 inversions,530 phi evaluations and840 group additions.
The inversion/character powers execute actual field multiplications. Event sums
also include55718 exponent-multiplication ticks overlapping field multiplications,
so1M is a conservative instrumented-event cap, not disjoint primitive work.
Cache/table accesses, labels, validation and failed partial work are retained.
Reviewer noted omitted trivial integer additions in one expression; interpreter,
PRNG internals, hashing/output and hardware traffic are explicitly unpriced.
No complete bit-cost or wall-clock advantage over a baseline follows.

Native Astra `/root/encoding_review` independently reconciled validation and
complete/partial case vectors to1M and counted530 rows/1060 checks,41 families,
without rerunning any field computation. It also independently recomputed all
recorded-character correlations, masks, denominators and correctness counts;
41 family records cover2969 eligible windows. Results SHA256
`0f3ae4f3e6ae60c4821156c9f5bb64e3457d0391ca133735bfbe400f2e8feec2`.
A review-only summary initially used the wrong JSON key `numerator`, then corrected
to `signed_numerator`; no diagnostic failure or extra field run occurred.
Example imbalance: q17,(0,2,4) scores8/14, exactly the constant-majority baseline.
The five-offset family is positive in its three COMPLETED c=−1 cases; this
restricted observation is not refuted by failures outside that class, but gives
no scaling, fresh-case or complete-cost guarantee. No p-values are claimed.

No matched full-solver baseline was run: this candidate still lacks a specified
noisy recovery algorithm. Small biases with unpredictable signs are insufficient.
No larger run is automatically authorized because the requested schedule was
incomplete. Decision: do NOT enlarge this diagnostic from these data alone. Specify a
data-independent domain/orientation rule and an explicit noisy recovery algorithm
with required advantage and complete cost before any further held-out scaling
budget. Native Astra is examining that specific recovery gate from primary
constructive algorithms; it is not implementing a solver or accepting the observed
bias as general. Other concrete algorithm-development work continues in parallel. Do not build generic proof infrastructure.

Validation: `./scripts/check.sh > /tmp/ecdlp-h002-eds-check.log 2>&1` exited0
with the363 existing audits; no new Lean claim was added. Python syntax check
was performed by the implementer with cache under/tmp. Root inspected staged
paths/diffs; the unrelated research-monitor and generated Python caches are excluded.

H003 follow-up: the reviewed conditional Fourier recovery in
`H003-noisy-recovery-disposition.md` removes the need for known orientation: a
sufficient ABSOLUTE full-domain magnitude works. The earlier sign-based gate
above is historical and superseded in that respect. The tiny-instance evidence
and no-larger-run decision remain unchanged pending magnitude/full-cost evidence.
