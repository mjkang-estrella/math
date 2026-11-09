# Frozen author statement — r162aj

There exist one deterministic finite-bit algorithm A and one numerical constant C>=1 with the following property.

For every explicitly encoded finite total turn-based stochastic arena with n>=1 vertices partitioned into Max, Min, and chance vertices; every signed binary integer reward on each edge; every exact binary rational probability on each chance edge, nonnegative and summing to one at each chance vertex; every unrestricted binary nonnegative integer priority on each vertex; and every exact binary rational threshold theta, A outputs the n-bit characteristic vector of precisely those initial vertices v for which

there exists a possibly infinite-memory behavioral Max strategy sigma such that for every behavioral Min strategy tau,

P_v^(sigma,tau)( liminf_(T->infinity) (1/T) sum_(t=0)^(T-1) w(X_t,X_(t+1)) >= theta
                 AND the least priority occurring infinitely often is even ) = 1.

Both players may use arbitrary history dependence and private randomization. Zero chance probabilities, zero rewards, threshold zero, non-coprime rational encodings, arbitrarily small positive chance probabilities, arbitrary reward magnitude, and arbitrary numbers and numerical magnitudes of priorities are included. There is no graph, gap, precision, or finite-memory restriction.

If L is the complete explicit binary input length, including all numerical data and delimiters, A uses at most 2^(C (log_2(L+2))^2) elementary bit operations. Input parsing, validation, exact rational arithmetic, graph construction, all oracle implementations, and writing the output are charged. A rejects malformed encodings within the same bound. Any fixed conventional explicit adjacency-list binary encoding with self-delimiting integer fields may be chosen once for A; the result is invariant under polynomial-time intertranslatable such explicit encodings.

The algorithm outputs the winning set. This statement does not assert a finite-memory winning strategy or include a strategy-output or online-response complexity bound. Strategies constructed in the semantic proof may use unbounded counters and an exponentially large finite recursive description; these are not uncharged outputs of A. The algorithm instead evaluates a polynomial-size monotone equation system.

The stipulated Source104 proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are premises. This is an author-proof nomination only, subject to independent correctness and contribution review. No acceptance, grade, campaign increment, or literature-priority claim is assigned here.
