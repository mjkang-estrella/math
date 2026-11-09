# H012 independent review: frozen audit protocol

Registered before executing the review checks, 2026-10-08.

Ownership: H012-independent-review.md and H012-review-* only. Original H012
source, protocol, and results are read-only. No factorer, new input-size sweep,
package installation, or change to the frozen continuation criterion.

One review-script invocation, internal deadline 55 seconds, external timeout
60 seconds. Record all stage outcomes, failures, and unfinished stages in a new
H012-review-audit.json; refuse overwrite. Do not invoke the frozen main/run_case.

1. Verify the three published SHA-256 hashes. Audit all 96 saved rows, both
   congruences, positivity/unit hypotheses, exact roots, cells, K/H, source-cell
   centering, candidate generation by an independent basis replay, and all
   covered/noncovered cells using rational quadratic extrema. Compare selection
   to independent dynamic programming, retaining saved counts and timings.
2. Compare both frozen envelope predicates against that independent rational
   oracle for all N in {1,2,3,7}, u,t in [-3,3], v in [-5,5], H in {0,1,2,5},
   and [P,Q] in {[1,1],[1,2],[2,5],[3,7]}. Include zero/negative coefficients,
   H=0, repeated roots, closed endpoints, stationary boundary equality.
3. Check greedy minimum interval counts for all pools of at most three distinct
   coverage masks on one to four cells. A disconnected mask counts as separate
   runs. Compare an independent dynamic program, including uncovered outcomes.
4. New finite algebra screen (not scaling evidence): for m in {6,30,210,2310}
   and (U,T) in {(2,3),(7,11),(17,23)}, count every nonzero signed pair in the
   rectangle for every unit c. Compare the proposed exact residue-average
   divisor-sum identity, including nonprimitive pairs. Record all 12 outcomes.

Any discrepancy is a review failure. Passing validates these finite checks
only; new analytic arguments require their own proof and independent review.
No parameter/budget changes or selective second screen after observing output.
