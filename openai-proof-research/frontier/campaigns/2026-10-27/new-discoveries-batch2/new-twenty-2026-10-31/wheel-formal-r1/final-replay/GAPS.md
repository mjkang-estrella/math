# Exact outstanding obligations — zero credit

There is no theorem of type WheelFormal.Target. The package does not resolve MathDB 371637. No wheel-specific optimal fractional colouring is provided. No bound on every independent wheel-square set is proved. The existing general weighted_lower_inf theorem takes the independent-set bound as a hypothesis; it is not a substitute for proving it.

The following are still required, in order:
1. Prove the cyclic independence bound |A| <= t for C_(2t+1).
2. Formalize deletion of a nonempty independent A into |A| nonempty paths, with total order m-|A| and at most |A|-1 odd orders. This requires an actual graph decomposition, including cyclic wraparound.
3. Formalize a matching in every P_u box P_v covering all but at most one vertex and deduce the independent-set bound ceil(uv/2).
4. Transport and sum that bound over the deletion-component rectangles. Combine with two_sided_arithmetic and the hub and one-sided cases to prove the universal vertexWeight bound C=2(2t²+t+1). hub_excludes_mixed and rim_fibre_independent are only initial restrictions, not cardinality bounds.
5. Construct the three actual parametric independent-set families with profiles (1,0,tm), (0,2,2t²), and (0,2t,t²+1). Prove independence and counts, with t=1 included.
6. Prove exact coverage after explicit rotations and coordinate swap, or prove finite orbit averaging. Assign the coefficients 1,m/D,m²/D to produce an actual FractionalColouring attaining the formula.
7. Apply fracChromatic_le_total and weighted_lower_inf to prove equality for all t>=1, without remaining combinatorial hypotheses.
8. Repeat fresh replay, leanchecker, all-declaration audit, negative controls and independent statement-fidelity review for the completed endpoint.

Best next decomposition: put cyclic independent sets and deletion components in one module, path-grid matching in a second, the universal weight bound in a third, the three constructed families in a fourth, and averaging/coverage in a fifth. The present infimum and double-counting foundation can be reused. The shortest new arithmetic step is the identity F(a,b)=-(t-a)(b-1)-(t-b)(a-1), already proved uniformly.

Prior-art limitations are separately listed in PRIOR-ART.md. Neither successful replay of the partial components nor the ordinary proof permits acceptance. Root review and acceptance are outstanding.
