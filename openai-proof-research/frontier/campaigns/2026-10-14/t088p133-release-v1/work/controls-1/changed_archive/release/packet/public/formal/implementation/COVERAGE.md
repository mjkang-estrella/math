# Exact formal coverage and use-site mapping

The unchanged target is the original frozen theorem: every nonempty-interior convex 4-polytope with at most six actual facets satisfies V4(ΠK) ≤ (160/3)V4(K)^3, equality iff simplex. **No theorem about convex bodies, measures, random variables, facets, or projection bodies is declared in this Lean package.** This is the implementation submission, not an independent formal review.

Use site: original `fresh-analytic-discovery-r133/packet/public/proof.md`, Section 5, **Proposition B**, especially its mixed-sign case. Author proof hash is `971506a4ea3de75a883da6d0eced6b11b0b997cc2a6598c2e0487ee5a6e2bc84`; frozen scope hash is `86e1f30e2c867215026b2a4c2bc0c50144660618c486d2b2029e044bfce8d354`. The full independent `t088p133-proof-r3/packet/public/review.md`, Section 5, confirms this universal algebra's role; its correctness verdict is for the entire original theorem, not a verdict on this new Lean package.

All real parameters are explicit in the elaborated types. In this table, F=`firstBracket`, G=`secondBracket`, M=`mixture`, A=P/p, B=N/q. The names below have prefix `T088P133.`.

| Declaration | Precise role in original Proposition B |
|---|---|
| `firstBracket` | Defines F=pAβ+qBα−dαβ. After A=P/p,B=N/q, F/(αβ)=P/α+N/β−d, the original first bracket. This last division/substitution explanation is a prose mapping; the formal proof uses F directly. |
| `secondBracket` | Defines G=AB−d(pαB+qβA). G/(αβ) is the original AB/(αβ)-weighted second bracket; the mapping uses pα/A=p²α/P and qβ/B=q²β/N. These explanatory normalized identities are not separate Lean declarations. |
| `mixture` | Defines (1+d)[pα/(α+A)+qβ/(β+B)], the deterministic upper bound obtained after the unformalized conditional HNBUE step. |
| `firstBracket_decomposition` | Exact polynomial identity from α+β=2,q=1−p. Replaces the square-root/Cauchy–Schwarz route by moment residuals and d(2p−α)². No sign premises needed for the identity. |
| `secondBracket_decomposition` | Exact identity G=[αB(A−2dp)+βA(B−2dq)]/2, using α+β=2. |
| `cleared_slack` | Exact universal expansion (α+A)(β+B)−(1+d)[pα(β+B)+qβ(α+A)]=F+G, assuming q=1−p only. |
| `slack_identity` | 1−M=(F+G)/[(α+A)(β+B)], with q=1−p and explicit nonzero denominators. |
| `firstBracket_nonneg` | F≥0 from α,β,p,q,d≥0, the two normalizations and A≥2dp,B≥2dq. No bracket sign assumed. |
| `secondBracket_nonneg` | G≥0 from α,β,A,B≥0, α+β=2 and both moment residuals nonnegative. |
| `secondBracket_pos` | G>0 from α,B>0; β,A≥0; α+β=2; A>2dp and B≥2dq. This supplies actual strictness even at d=0. |
| `mixture_le_one` | A,B-variable non-strict deterministic bound. α,β,A,B>0; p,q,d≥0; normalizations; both residuals nonnegative. |
| `mixture_lt_one` | Same hypotheses except A>2dp, giving M<1. |
| `moment_lt_iff` | For p>0, 2dp²<P iff 2dp<P/p. |
| `moment_le_iff` | For p>0, 2dp²≤P iff 2dp≤P/p; also used with q,N. |
| `conditional_means` | For 0<p<1,q=1−p,P,N>0, proves q>0,A>0,B>0,pA=P,qB=N. It is algebra, not a conditional-expectation theorem. |
| `rational_mixture_lt_one` | Exact requested P,N wrapper: all real α,β>0 with sum 2; 0<p<1,q=1−p; d≥0,P,N>0; 2dp²<P and 2dq²≤N imply (1+d)[pα/(α+P/p)+qβ/(β+N/q)]<1. |
| `rational_mixture_le_one` | Exact same wrapper with both moment inequalities and conclusion non-strict. |
| `positive_sum_two_bounds` | α,β>0 and α+β=2 imply α<2 and β<2, needed in endpoint cases. |
| `one_sided_lt_one` | For real 0<a<2,M>0,2d≤M, proves (1+d)/(1+M/a)<1; no assumption on sign of d is needed. |
| `p_one_bound` | Original p=1 deterministic expression with a=α,M=P, deriving α<2 rather than assuming it. It does not assert P=EW or p=1 for any law. |
| `p_zero_bound` | Original p=0 deterministic expression with a=β,M=N, deriving β<2. |

The general proof uses positive denominators proved from the explicit α,β,A,B hypotheses. Strictness is never inferred from continuity or just a nonnegative coefficient. All implications are universal; rational samples only check use and boundaries.

## All control declarations

The prefix is `T088P133Controls.`. Every control's full elaborated type and axiom list is saved alongside the support types. The arithmetic countermodel conjunctions check the other hypotheses, the omitted assumption's failure, and an exact value greater than 1. Duplicate numerical hypotheses when α=β or p=q are stated once because they are definitionally the same assertion.

- `rational_example_hypotheses`, `rational_example_bound`, `rational_example_value`: the asymmetric 12/13 witness; the bound theorem actually applies the universal strict wrapper. Second moment is exactly at equality.
- `zero_d_bound`, `zero_d_value`: d=0 is admitted by the same strict wrapper, with value 1/3.
- `nonstrict_equality_hypotheses`, `nonstrict_example_bound`, `nonstrict_cannot_imply_strict`: α=β=d=1,p=q=P=N=1/2 yields exactly 1; actual application of the non-strict wrapper and refutation of a strict conclusion.
- `missing_first_moment`: P=1/8,N=1/2 with α=β=d=1,p=q=1/2 gives 13/10. Even the weakened first moment is false; all other requested strict-wrapper hypotheses hold.
- `missing_second_moment`: P=1,N=1/8 in that normalization gives 17/15 while the first moment remains strict.
- `missing_sum_normalization`: α=β=2,d=1,p=q=1/2,P=1,N=1/2 gives 7/6; only α+β=2 is dropped.
- `missing_alpha_positivity`: α=−2,β=4,d=1,p=q=1/2,P=3/4,N=1/2 gives 24/5.
- `missing_beta_positivity`: α=4,β=−2,d=1,p=q=1/2,P=1,N=3/4 gives 14/3. Both positivity controls explicitly verify that the rational denominators are nonzero, so totalized division is not their cause.
- `missing_weight_normalization`: α=β=1,p=1/2,q=1,d=0,P=1/8,N=1/4 gives 6/5; p still lies in (0,1).
- `missing_probability_range`: α=β=1,p=2,q=−1,d=0,P=1,N=2 gives 7/3 with both denominators nonzero; all other requested hypotheses hold. These countermodels do not purport to describe probabilities.
- `endpoint_examples`: actual applications of each endpoint wrapper at α=β=d=1 and P or N=2.
- `endpoint_zero_d`: actual application of `one_sided_lt_one` at a=M=1,d=0.
- `endpoint_upper_boundary`: a=M=2,d=1 gives 1, illustrating the a<2 requirement.
- `endpoint_zero_moment`: a=1,d=M=0 gives 1, illustrating the positive moment requirement in the endpoint theorem.
- `endpoint_missing_moment`: a=M=1,d=2 gives 3/2, illustrating why its moment hypothesis cannot be deleted.

These are counterexamples to specified weakened **algebraic** statements, not a proof that every hypothesis is individually necessary in every equivalent formulation. No invalid p=P=N=0 substitution is used as a mixed-case example. No result concerning the best auxiliary constant is inferred.

## Unformalized interfaces and final scope

1. Actual-facet geometry: facet vectors/normals, Gale normalization, nonzero middle coefficient vector, zonotope volumes and determinants.
2. Mixed volumes and the attained variational maximum, coarea, simplex sections, Gamma–Dirichlet and density values, all constants in Proposition A and Lemmas 1–4.
3. Distributions and random variables, signed exponentials, conditional laws/means, log-concavity, HNBUE and its integration argument. In particular, the inequality bounding the expectation by our rational mixture is **not** formalized.
4. The exact ten-pattern coefficient certificate of Proposition C and its probabilistic interpretation, partial fractions, recurrence and polynomial quotient identities. Neither the author certificate nor the independent recurrence is imported as a Lean axiom.
5. Continuity and all zero/repeated-knot/stratum assembly, including the probabilistic source of a strict moment. We assume only the explicit real moment inequalities in our algebra theorem.
6. Simplex equality, every-six-facet strictness as a geometric assertion, and the final projection-body theorem and equality iff simplex.

To use this package in the original proof, the unformalized preceding steps must establish α,β,p,q,d,P,N and every stated hypothesis, including the strict first moment in the mixed case. The parent adopted full-scope correctness review and separate bounded-search contribution decision are external provenance, not Lean imports, axioms, or an acceptance for this package. Implementation complete does not close the independent formal-review, manuscript/review or release obligations.

Original prose © 2026 Myeongjin Kang, CC BY 4.0.
