# Source mapping and proof components (partial)

The target remains Petersen arXiv:1607.02425 Conjecture 4.6.8 and Petersen–Wilson arXiv:1512.01143v6 Conjecture 6.3: existence of a fully supported stationary one-step Markov measure locally maximizing the rank-zero, uniform-subset intricacy on the two-sided full two-shift, relative to stationary one-step Markov measures. There is no uniqueness/global maximum/arbitrary invariant measure/higher-order claim.

The original ordinary proof is frozen in `../fresh-corpus-r13/PROOF-333569.md`. This lane does not replace it with a complete formal proof. The inherited independent review (`../intricacy-source-review-r1/REVIEW.md` and `review.json`) is a qualified PASS for ordinary mathematics and substantive candidacy; it is not formal acceptance.

Actual cached source text was read at Definition 5.1 and (5.1)–(5.5), Proposition 5.10 and its proof (5.28)–(5.31), Section 6 and (6.1), Conjecture 6.3, and Petersen's Conjecture 4.6.8. The finite-cylinder formula in (6.1) motivates `wordProb`; uniform coefficients and complement symmetry motivate `finiteIntricacy`. Only the former has newly proved finite normalization/positivity/extension lemmas; the entropy identification and complement/limit bridges are not yet proved.

## What the Lean files prove

- `Target333569.lean`: inherited finite-cylinder definitions and unproved `SourceClaim`, with only narrowed imports to fit bounded replay memory. No endpoint theorem was added.
- `Algebra333569.lean`: `chart(l,t)` gives the stated diagonals u,v; `kernel=l I+(1-l)J` agrees with the source transition matrix. Its rows sum to one and pi is invariant. Direct finite algebra gives `kernel_comp`, and induction gives `steps_eq`, the exact gap-transition identity. The chart lies in the positive interior for `0<l<1,-1<t<1`, its stationary formula agrees with pi, and its inverse is the ordinary rational chart. Word weights are strictly positive in the source parameter interior.
- `Cylinders333569.lean`: direct stationary normalization/invariance; snoc extension factorization and consistency; finite word-weight normalization by induction using a word/prefix-last-symbol equivalence; nonnegative, normalized, strictly positive subset marginals; empty marginal mass one and empty sample entropy zero. These remain finite distributions, not a constructed probability measure on the two-sided shift.
- `Diagonal333569.lean`: defines the positive-gap series with geometric weights and entropy differences. Binary entropy monotonicity gives nonnegative terms, strict positivity at gap two, and a summable geometric majorant. Uniform domination yields continuity on `[0,1]`. Both endpoints vanish, so compact attainment and interior positivity give an interior maximizer. This is the analytic diagonal series, not an identified source-measure functional.
- `Curvature333569.lean`: defines log odds using a log difference; proves equality to the ratio-log formula on its domain. Computes c' and c'' via `HasDerivAt`. The positive c'' and zero c'(0) give positive c' on `(0,1)` and strict increase of c on `[0,1)`. All power comparisons are proved, with a strict gap-two comparison.
- `SeriesCurvature333569.lean`: bounds each weighted coefficient difference between zero and a geometric multiple of `c(l)-c(0)`, proves absolute summability and strict negativity of the sum through the gap-two term. Identifying this sum with a derivative of the actual intricacy is explicitly residual.
- `Entropy333569.lean`: defines the ordinary conditional-entropy formula; proves evenness, the diagonal restriction, entropy-argument domain bounds, nonnegativity, upper bound log 2, and summability of the weighted conditional entropies. It does not prove the finite Shannon chain rule or termwise differentiation.

All these proofs are reusable components with no extra analytic hypotheses standing in for the source endpoint. See `RESIDUALS.md` for the missing implications.

## Provenance and novelty boundaries

The upstream OpenAI manuscript pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (2026-10-08). The inherited current-head receipt is only a head receipt; no current full-repository proof clearance follows. MathDB/Palomar inherited 403 blocks were not retried. No new external searches, source fetches, browser tabs, external messages, publication, git operations, child agents, shared edits, or acceptance changes occurred here.

Retain every bounded-prior-art/publisher/version limitation from the independent review: Petersen–Wilson publisher body not inspected (403); Huang–Xiao publisher body not compared; Wilson dissertation and Buzzi–Zambotti 2012 proof body not audited; Li–Tu and remaining citing literature not fully audited; all earlier source versions not compared. No worldwide novelty or priority certification, and no updated current registry clearance, is claimed. Qualified significance review does not accept a partial Lean development.

## Trust and replay

Lean is 4.34.1. Mathlib is pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`; the copied Lake manifest records transitive pins. The supplied external prebuilt dependency cache is explicitly trusted; it is read only and was not rebuilt or audited from source. Fresh extraction rebuilds every new local module and prints transitive axioms for every proved theorem. This is a partial-component replay only, not an endpoint certificate. Early experiments with the full Mathlib import exceeded a 2048 MB Lean memory limit; narrowed imports and a 4096 MB limit worked. No linter was disabled to obtain strict replay. CPU affinity is restricted to two CPUs with a per-module CPU time limit of 180 seconds.
