# Frozen author target: compact factorization with simultaneous dual cotype control

Frozen after the full Source326 operative reading, original Pisier 1980/1981/1983 proof comparison, guarded original-history reads, and visual reading of Figiel 1973 Sections 2–7. Earlier working calculations are prefreeze feasibility work. This is an author target, not a correctness/contribution/acceptance/count decision and not a new-to-literature claim.

**Exact statement.** For every real number r with 2 <= r < infinity and D >= 1, for all real Banach spaces X,Y satisfying C_r(X*) <= D, for every compact linear operator T:Y -> X, and for every finite-dimensional linear subspace E of X, there exist a separable reflexive real Banach space G, an injective compact linear operator J:G -> X, a compact linear operator U:Y -> G, and a linear contraction i:E -> G such that

    J U = T,    J i = inclusion of E in X,
    ||J|| <= 2,    ||U|| <= 2 ||T||,

and, simultaneously for every real s with r < s < infinity,

    C_s(G*) <= 48 D H(r,s),
    H(r,s) = (sum_{k=1}^infinity (1 + log_2(k))^s k^(-s/r))^(1/s).

The series defining H(r,s) is finite. Here C_a(Z) is the least constant in

    (sum_j ||z_j||^a)^(1/a)
      <= C_a(Z) (E_epsilon ||sum_j epsilon_j z_j||^2)^(1/2)

for every finite tuple in Z, with independent uniform real signs. The same G,J,U,i work for every s>r. The spaces X,Y may be nonseparable and finite- or infinite-dimensional. E may be {0}; T may be zero; if X={0}, the conclusion uses G={0}. No approximation property, bounded approximation property, cotype of X or of Y, or reflexivity of X or Y is assumed. No assertion of cotype r for G*, of AP for G or G*, of primal cotype for G, or of K-convexity for G is part of the target. The field in this frozen statement is real only.

**Comparison obligation.** Source326 lem:compact-domain controls one fixed tuple length and embeds a prescribed finite-dimensional E through a compact map. The target must integrate all tuple lengths into one reflexive quotient and also compactly lift an arbitrary compact operator, with the above uniform constants. Figiel's original compact factorization gives a reflexive intermediate space, but its universal-space proof alone supplies no stated finite-dual-cotype control. Distinctness and substantial contribution require independent review of actual literature; inaccessible references or excluded history are not evidence of novelty.
