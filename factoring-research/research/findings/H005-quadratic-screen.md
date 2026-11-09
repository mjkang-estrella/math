# H005: threshold passed, but tiny intervals make the test weak

The preregistered quadratic inverse-patch screen completed all 27 available
instances in about 0.03 seconds. Its largest-size median node fraction was 0.375,
below the 0.8 rejection threshold. No true solution was pruned and all returned
factors matched direct enumeration. The N=115 false-feasibility control passed.

However, all actual patch t intervals had at most two integers. With the given
K and s, the interval lengths are one or two, so every integer t is an endpoint.
The tangent/secant constraints then force z=t² exactly. Consequently there were
zero false feasible nodes, for a structural reason unrelated to general pruning
power. The decreasing node fraction mostly reflects rejection of empty roots,
not evidence of a small search tree for wider or higher-degree patches.

Disposition: **inconclusive for the research gain; advance to a stronger falsifier**.
Retain the raw `screen_pass_only_no_complexity_claim` result as the preregistered
threshold outcome, but do not promote it as evidence for an exponent improvement.
The reference feasibility routine also enumerates t and q, so its measured
runtime is not a fast integer-programming implementation.

Evidence: research/experiments/H005/result.json and quadratic_screen.py, with
source/protocol hashes. The file records real pool shortfalls: 4,7,8,8 instances
for K=10,12,14,16. The prescribed eight were not silently resampled.

Next: H006 tests the actual degree-five claim by constructing sound relaxed
feasibility certificates on wide intervals. Its certified subtree is a lower
bound on how much this relaxation-driven bisection must visit; inability to find
a certificate is inconclusive, not a pruning decision or infeasibility proof.
Current verified complexity improvement remains NONE.
