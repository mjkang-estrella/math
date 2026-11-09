# I254 — independent mathematical reconstruction

Date: 2026-10-12. Scope: mathematical correctness of the final I248 candidate only. No contribution verdict or count change is made. The stipulated OpenAI revision is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The full submitted proof was read, lines 1–167, and its SHA256 is the requested 47a0fa44fdc57a1c2009da17f14a6dab8aa6d05fec63d49e55f013d49487886b.

## Working reconstruction (recorded before final disposition)

For a fixed root set Y let V=[n]\\Y, N=|V|, b=ds+binom(d,2), tau=1-(1-r)^2, L=64d, and a=floor(N/(16d^2)). A pattern is a subset of the *formal* coordinate set ([d]×Y) disjoint-union binom([d],2), containing at most s root incidences in each slot. Every actual injection of the d slots into V identifies those coordinates with distinct host edges. Shared roots therefore create dependence between different blocks but do not identify two coordinates of a single block. No root-root edge is a coordinate.

The Bernoulli compression construction works for every nonempty family of supports of size at most b, including the empty support: every greedy insertion raises the success probability by more than r^b/2. Closing the original family and then its compressed subfamily under slot permutations leaves at most d! ceil(2r^(-b)) patterns and preserves membership in the closed original family. For a compatible block the success probability after smoothing is at least 1/2. Hence nu_R(G)≤2W_Q(G), where W_Q maximizes the sum of smoothed probabilities over disjoint d-sets.

For a full independent graph G', the conditional expectation of the number of Q-compatible members of *any fixed* matching is its sum of weights. The compatible members form a packing in G∪G', so W_Q(G)≤E[nu_Q(G∪G')|G]. Thus EW_Q≤mu_Q, with mu_Q=E nu_Q(G(n,tau)). Maximization is on the correct side; block-event independence is unnecessary.

Expose one independent coordinate block per nonroot vertex v: all v–Y edges and the nonroot edges vw owned by the earlier endpoint v. Changing this block changes only d-sets containing v, even though its edges may have many different other endpoints. A matching contains at most one such d-set. Its weight is between zero and one; deleting that set leaves a feasible matching whose other weights agree. Applying this argument in both directions proves the required Lipschitz constant one for both W_Q and nu_Q.

For a fixed test, mu_Q≥floor(N/d) r^b≥c_d n^.99 by testing one pattern on predetermined disjoint blocks. This is only an expectation argument. It does not assert independent compatibility of arbitrary candidate blocks.

The permutation/tie-breaking and filtration argument, full constants, simultaneous union bound, and Aharoni–Haxell application are being checked next. No objection requiring a theorem change has emerged in the steps above. This paragraph is a progress record, not the final verdict.
