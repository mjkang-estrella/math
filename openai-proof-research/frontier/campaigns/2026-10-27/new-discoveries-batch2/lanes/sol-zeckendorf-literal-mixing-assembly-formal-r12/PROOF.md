# Proof mechanism and limits

Split plus combine equals one at every actual move. On a complete word the combine sum is exactly N-Z(N). The take/drop decomposition makes the combines in a prefix at most this total. After termination, the padded split sum is constant. Thus m minus its split sum exceeds N-Z(N) exactly when T<m, including the strict boundary T=m. LastSplit is attained whenever positive, so its threshold event is a finite union of split-coordinate events through the actual maximum duration.

Actual finite probabilities obey the elementary Frechet bounds. A case split on the two marginal probabilities, followed by the nonnegative square (p-1/2)^2, proves covariance at most 1/4. Complementing one event gives the negative bound. Taking the supremum over the full generated sigma-algebras preserves it. Measurability is proved directly from coordinate measurability and finite sums/unions.

The least median exists because every word ends by duration. Its preceding CDF is below one half. The r11 interval estimate bounds the intervening atom and hence the median CDF. Every outcome is in the early event, the near-median window, the long-suffix error event, or the late-split event. The union bound gives the lower late probability. This is positive eventually, forcing an admissible median cut. The early and late events are disjoint, so absolute covariance equals the product of their probabilities. This yields alpha at least 1/4 minus intervalError minus suffixError/2, uniformly for every k in 1..n^6.

The least Fibonacci upper interval index has the claimed lower endpoint by minimality; monotonicity proves uniqueness and divergence of the index. Composing both r11 error limits with this index and squeezing proves the all-N limit. The same uniform inequality eventually exceeds 1/9. No stochastic independence of the two stopping events enters this argument.

Weighted mixing failure and signed-v1 equivalence remain residual as specified in SUMMARY.md.
