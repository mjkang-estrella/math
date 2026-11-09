# I347 — SAT predictable quadratic variation

Date: 2026-10-13. **UNRESOLVED; finite endpoint with a proved two-root partial.** No CLT, refutation, acceptance, count increase, shared-index change, or publication is proposed.

## Exact outcome

All five detached I343 hashes match. Its needed endpoint deletion proof was independently checked, including the exceptional frozen-coordinate error, the two filtrations, conditional higher-duration induction, and every collision count. The uniform (k−1)-moment and resulting conditional Lindeberg for every fixed k ≥ 4 are valid. Its realized/predictable variation comparison and late-cap control are also valid.

For independent uniform signed proper k-clauses with replacement, keep H as the first unsatisfiable prefix, T = min(H,floor(Bn)), B > U_k, the natural clause-prefix filtration, and σ² = Var(T) = Θ(n). The remaining target Q/σ² → 1 in probability was neither proved nor refuted. All centering remains at the exact finite-size mean; no limit for σ²/n is assumed.

## New paid finite partial

For two fixed disjoint marked clauses, write R⁺ for the occupation count of prefixes where the twice-deleted formula is satisfiable but either marked clause alone kills it. Write R⁻ for prefixes where both clauses together kill it and neither alone does. The mixed deletion difference is exactly R⁺−R⁻. Uniformly in the pair of indices and the fixed disjoint marked clause values,

\[
E[(R^+)^{2(k-1)}\mid C_i=c,C_j=d]\le C_{k,B},\qquad
E[(R^-)^{k-1}\mid C_i=c,C_j=d]\le C_{k,B}.
\]

The stronger first estimate uses one common falsifying slice, 2k independent conditional root-test families, the same bounded potential exponent k/(k−1), and all collision counts up to 2k−1. Intermediate collision contributions are O(n^(−v/k)); the cap-only contribution is O(n^(−2)). This is a proved nonroutine exact-model partial. Its new-to-literature status is not established, and it is not promoted as the substantial fluctuation theorem.

Cooperative killing has no common-slice guarantee. An explicit proper-clause formula enforcing all 2k marked roots equal to a nonroot z gives cooperative killing by opposite marked clauses, with no background clause meeting two marked roots. Thus logical interactions need not be supported on root collisions. This finite witness concerns a failed proof implication and refutes no asymptotic SAT statement.

## Precise unpaid estimates

For a prefix P before j, fresh marked clauses c,d, and a shared fresh future Y, let T_c = T(P,c,Y), T_d = T(P,d,Y). A posterior-variance martingale calculation gives the exact identity

\[
\operatorname{Var}(Q)=\frac12\sum_j E_{P,c,d}
[\operatorname{Cov}_Y(T_c-T_d,T_c+T_d)^2].
\]

An o(n²) bound for this nonnegative sum would pay the requested concentration. For k ≥ 5, writing T₀ for the omitted-clause hitting time and D_c = T₀−T_c, it is equivalent to the still-unproved bound

\[
\sum_j E[\operatorname{Cov}_Y(D_d-D_c,T_0)^2]=o(n^2).
\]

The delay-variance remainder costs only O(n). The available marginal moments bound the full sum only by O(n²), with no little-o.

For every k ≥ 4, including k = 4, bounded ghost kernels v_i^[K] approximate the conditional variances with E|Q−Σv_i^[K]| ≤ CnK^(−(k−3)). A sufficient unpaid estimate is Σ_(i≠j) Cov(v_i^[K],v_j^[K]) = o(n²) for each fixed K. This removes the fourth-moment obstacle without removing the shared-formula correlation obstacle. It is proved as a conditional reduction, not asserted as SAT concentration.

## Deliverables and limits

- [Proofs, independent I343 audit, and exact joint gaps](../experiments/i347_sat_quadratic_variation/analysis.md).
- [Reading scopes and failed routes](../experiments/i347_sat_quadratic_variation/reading-and-failures.md).
- [Input hashes and provenance](../experiments/i347_sat_quadratic_variation/input-authentication.json).
- [Primary-source operations and novelty limits](../sources/i347_sat_quadratic_variation/literature.md).

No subagents, git, numerical scans, live-sibling bodies, retained full external source bodies, or edits beyond the five assigned outputs were used. The covariance identities, bounded-kernel reduction, and conditional CLT/cap implications do not increase the theorem count. The endpoint leaves the predictable-variation concentration genuinely unpaid for every fixed k ≥ 4, with no claimed restricted-k success.
