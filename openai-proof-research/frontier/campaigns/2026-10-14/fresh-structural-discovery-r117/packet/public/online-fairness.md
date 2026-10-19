# Fixed-work random relabeling: feasibility calculation, not a nominee

This is prefreeze research: no target was frozen before or after this calculation. Its purpose is to test the strongest compatible existing compiler, including exact reference costs. It is not a substantiality claim.

## Existing interfaces actually inspected

Pinned source110, `01_introduction.tex`, `thm:main`, gives one causal randomized policy for all finite oblivious request words on every metric, with expected ratio C log²(k+1), arbitrary finite additive loss for repeated starts, and zero additive loss for distinct starts. Its `10_transfer.tex`, `lem:compact-policy`, realizes the same behavioral rule at every history on a single probability space. This is stronger than separately choosing a policy for every horizon. The uniform-computation companion's `thm:main` additionally permits polynomial dependence on log(t+1) and an unrestricted finite startup loss; it does not solve I113's useful-startup target.

The closest primary is [Daneshvaramoli et al., *Fairness in the k-Server Problem*, arXiv:2512.20960v1](https://arxiv.org/pdf/2512.20960v1), Algorithm2, Theorem9, AppendixC.3/Theorem22 and Remark2. It accepts an arbitrary virtual online policy, independently permutes physical server labels at phase boundaries, charges at most D per server per permutation, and applies concentration to phase workloads. Its growing thresholds j^gamma give a sublinear additive loss and a cost-dependent success probability. Remark2 includes an ID-oblivious adaptive adversary; it does not grant fully label-observing adaptivity.

## Exact calculation

Let k>=2. Fix a metric of finite diameter D>0, any labeled starting tuple, and any causal virtual policy A moving at most one server to each request. There is no efficiency assertion. Fix a finite oblivious word before all random choices. Write C_t for the realized cumulative cost of A through its t-th request. Take 0<delta<=1, 0<epsilon<=1 and 0<p<1. Put

    B = kD/delta, H = B+D,
    beta = (H/epsilon) log(k/p) + H + D.

A physical auxiliary process tracks A's unlabeled configuration. At the beginning of each phase, including the first, independently choose a uniform bijection from physical labels to virtual labels and move the physical servers accordingly. Every physical server moves at most D. Follow A's requests under that assignment until its cumulative service work in the phase first reaches B, then start a new phase. Decisions use only the past and current request. All full phase costs S_j lie in [B,H]; a final incomplete phase has cost at most H. Zero-cost requests cause no additional phase changes.

Conditional on the entire virtual trajectory, each phase's workload vector is fixed and independent of the physical permutations. For each physical label i, its phase service work X_ij is a uniformly sampled coordinate of that vector. Thus

    0<=X_ij<=H, E X_ij=S_j/k.

With lambda=epsilon/H, convexity on [0,H] gives

    E exp(lambda X_ij)
       <= 1 + (S_j/(kH))(exp(epsilon)-1)
       <= exp((1+epsilon)lambda S_j/k).

The second step uses exp(epsilon)-1<=epsilon+epsilon² for 0<=epsilon<=1. Therefore

    M_i(m)=exp(lambda sum_{j<=m}(X_ij-(1+epsilon)S_j/k))

is a nonnegative supermartingale of initial value1 in the independent permutation filtration. The elementary maximal inequality gives

    Pr{some m: sum_{j<=m}(X_ij-(1+epsilon)S_j/k)
                    >= (H/epsilon)log(k/p)} <= p/k.

For completeness, stop at the first crossing and at a finite deterministic terminal index. The stopped expectation is at most1, whereas on crossing the stopped value is at least k/p. Let the terminal index increase. This proves the displayed bound without any horizon-dependent union bound. A union bound over the k labels costs only p.

At a prefix ending inside a phase, its unfinished service contribution is at most H. If m phases have finished, mB<=C_t, and the swaps incurred by each physical label are at most (m+1)D<=delta C_t/k+D. Consequently with probability at least1-p, **simultaneously for every prefix of this fixed word and every label i**, its auxiliary physical cost V_i(t) satisfies

    V_i(t) <= (1+epsilon+delta) C_t/k + beta.

Pathwise, the total auxiliary cost satisfies

    sum_i V_i(t) <= (1+delta) C_t + kD.

The same policy and constants work before a horizon is chosen. The probability event is for each fixed oblivious word; this is not one event simultaneously valid over all adversarially selected words. Conditioning can be integrated over A's independent random seed. No rationality or finite-cardinality restriction was needed, but finite D was essential to these bounds.

## Exact one-move implementation

The auxiliary process moves multiple servers at swaps. This does not silently change the implementation contract. Keep the entire auxiliary process internally. When it serves a request with physical label i, move only real label i directly from its last real position to that request. This is one allowed server move; collisions and zero moves are permitted. For each fixed label, these real positions form a subsequence of that label's auxiliary path starting at the same initial point. The triangle inequality gives, at every prefix,

    real_cost_i(t) <= V_i(t).

This is a per-label path shortcut, not a claim that a generic total-cost lazy coupling preserves labels. It proves the same displayed individual upper bound and total-cost upper bound for the actual one-move process. Combining the latter with source110 merely gives

    E total_real_cost <= (1+delta)[C_source log²(k+1) OPT + B_source] + kD.

That application is a compatible ordinary compiler. It neither supplies effective source probabilities nor removes the companion's startup limitation.

## What was and was not obtained

The individual bound uses **C_t, the virtual base cost**. Since shortcutting can reduce total real movement, it does not imply

    real_cost_i <= (1+epsilon+delta) total_real_cost/k + beta.

Replacing C_t by a smaller quantity has the wrong inequality direction. No own-total-cost fairness theorem is asserted for the shortcut process.

For a fully label-observing adaptive input, the virtual phase workload may depend on the physical permutation. The uniform-coordinate conditional expectation used above then fails as an available premise. A heuristic policy that swaps a currently expensive server with a cheaper one also lacks a charge for repeated relocation of the same server. Those observations only mark missing proofs; they are not counterexamples to all adaptive fair algorithms.

The primary already pays the physical/virtual label architecture and phase accounting. Fixed-budget regrouping, exponential maximal control and per-label triangle shortcuts complete the calculation with standard operations. There is no identified additional compatibility lemma left to propose for review. This is why neither the new display of constants nor the all-prefix wording is nominated. No independent contribution classification is assigned.
