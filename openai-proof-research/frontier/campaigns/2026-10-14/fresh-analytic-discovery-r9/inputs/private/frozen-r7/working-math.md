# Incremental proof work

These are working derivations, not a completed theorem or independent review.

1. A bridge whose far component has original degree mass s contributes the PSD rank-one inverse-energy operator R (1_A-s/M) tensor_m (1_A-s/M), M=2n; its eigenvalue is R s(1-s/M). In a one-link block, s=|T_i| for the opposite-pole child, by exact corner accounting. Each node has link-mark probability theta=p_2/2; N/n->2 gives K=2 theta E|T|^alpha.

2. For a nonbridge block B with k=2m corners, fix its pole o. Two edge-disjoint o-x paths with lengths l1,l2<=m imply R_B(o,x)<=min(S_l1,S_l2). For alpha-Pareto sums P(S_l>t)<=C_alpha l t^{-alpha}, by union and truncated expectation. Independence yields E R_B(o,x)^alpha<=C_alpha sqrt(l1 l2)<=C_alpha m. No block shape or high degree moment is used here.

3. The trace Z_B of its global inverse-energy contribution is at most sum_i |T_i| R_B(o,x_i). Thus E[Z_B^alpha | k, child subtrees] <=C_alpha k sum_i |T_i|^alpha. Its unconditional expectation is at most C E xi^2 E|T|^alpha, finite exactly in the proposed range. Mere integrability of an arbitrary fringe toll is NOT enough under conditioning; a conditioned uniform-integrability proof remains necessary.

4. Proposed endpoint bound for h(T)=xi sum_i |T_i|^alpha: E[h(T); |T|=s]=o(s^{-1}). Split chosen child size l at s/2. For l<=s/2, use forest local bound C(k-1)s^{-3/2} exp(-c(k-1)^2/s), and finite second offspring moment gives sum k^3 p_k exp(-ck^2/s)=o(s^{1/2}). For l>s/2, l^alpha P(|T|=l)<=C s^{alpha-3/2}, and sum residual forest probabilities <=1, yielding C E xi^2 s^{alpha-3/2}=o(s^{-1}). Need write full uniform forest bound and cyclic-fringe identity.

5. If conditioned additive toll UI is paid, nonbridge trace sum=o_P(n^{1/alpha}) follows from finite-alpha-moment triangular truncation, WITHOUT assuming independence of the block trace tolls. Bridge toll empirical law would give n^{-1}sum s_e^alpha->K. Extreme s<=L cuts are disjoint with high probability: O(n L) potentially nested pairs and each pair has probability O(n^{-2}) for resistance exceedances. Centered indicators for disjoint small cuts are asymptotically orthogonal. Small bridge weights have normalized expected sum O(epsilon^{1-alpha}).
