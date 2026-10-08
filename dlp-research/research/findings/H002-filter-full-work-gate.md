# H002 L3/L4: a complete-work gate for learned filters

Status: coordinator cost derivation for the named learned endpoint/decomposability
filter hypotheses; pending independent review. Not an experiment or improvement.
No general machine/Lean infrastructure is needed. This gate replaces accuracy/AUC
alone as a decision criterion; it does not assume a useful predictor exists.

## Explicit restricted model

Each fresh candidate costs a to generate and independently has a usable outcome
with probability p>0. The ordinary downstream procedure costs C on every attempt
and reveals that outcome. A fixed filter costs g per candidate, accepts a true
usable outcome with probability t>0, and accepts an unusable outcome with
probability f. Its marginal acceptance rate is r=pt+(1−p)f. All rates refer to
fresh post-training data from the actual proposal distribution. They include
verification, rank usefulness or endpoint membership as appropriate, rather than
merely an optimistic label. Candidate costs and rates are stationary here.

Without the filter, expected online work per useful outcome is `(a+C)/p`.
With it, expected online work is `(a+g+r*C)/(p*t)`.
Reason: an attempt costs a+g and incurs C with probability r; it succeeds with
probability pt. The renewal equation E=E[cost]+(1−pt)E gives the ratio. Cost and
success within one attempt need not be independent. Successive attempts do need
the stationary renewal assumptions; reused samples, correlated starts or changing
tables require their actual process instead.

Thus online gain requires
`a+g+r*C < t*(a+C)`.
Lost true positives and candidate generation can destroy a superficially good
classifier. For t=1 and f=0 the expected cost is `(a+g)/p+C`, not simply C.
Even this perfect filter pays to generate all candidates and evaluate the filter.
For t=0 success never occurs in this model, regardless of reported accuracy.

If additional training/setup costs H and is legitimately shared across K useful
outcomes, include H/K on the filtered side. Against the same baseline setup,
necessary average-work improvement becomes
`p*t*H/K + a+g+r*C < t*(a+C)`.
For a single target K cannot be chosen from hypothetical future users. Common
preprocessing cancels only if it is actually identical and reused under the same
rules. Extra model/advice memory must also be compared to a baseline allowed the
same resource budget. We have no measured values proving this inequality.

## What to measure if a card survives pool review

- Count candidate generation, feature computation, downstream successes/failures,
  predictor inference and label generation. Training labels are not free.
- Evaluate t and f at the chosen threshold on untouched data, with uncertainty;
  use conservative bounds in the inequality. AUC alone does not supply t/f.
- Check true outcomes with the actual solver/relation verification. A cheap
  proxy label needs its own correctness link; do not assume m=2 labels transfer.
- Include H, storage and explicit K, and match baseline preprocessing/memory.
- If C varies with the candidate, use measured conditional expected cost, not r
  times an unconditional C. For evolving walks/relations, model dependencies.
- Use increasing ordinary synthetic sizes and seeds. A negative pilot eliminates
  that configuration, not all learning or a full-size asymptotic possibility.

This derivation is an analytic decision tool for L3/L4. It does not fund training
before the broader independent pool is synthesized. Current reference remains
square-root work with applicable tradeoffs; verified improvement NONE. Next
conclusion-changing evidence would be a specific filter satisfying this full-work
inequality and a separately verified end-to-end algorithm, not a high AUC alone.
