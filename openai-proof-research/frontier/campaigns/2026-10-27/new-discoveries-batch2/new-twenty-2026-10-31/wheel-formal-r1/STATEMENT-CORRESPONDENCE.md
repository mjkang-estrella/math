# Statement correspondence

| Source notion or obligation | Literal Lean object | Status |
|---|---|---|
| C_m with consecutive cyclic vertices | rimAdj on ZMod m | Defined with distinct endpoints and ±1 adjacency |
| W_m = C_m join K_1 | wheel m on Option (ZMod m) | Defined; none is the hub and adjacent to all some vertices |
| Cartesian square W_(2t+1) box W_(2t+1) | wheelSquare t using SimpleGraph.boxProd | Defined using mathlib product |
| Independent subsets | Independent G s | Pairwise absence of graph adjacency at distinct vertices |
| Nonnegative weights on independent subsets covering every vertex at least once | FractionalColouring G | Literal structure, including empty set |
| Fractional chromatic number | fracChromatic G | Real sInf of range of all colouring totals; nonempty and bounded below proved |
| Infimum upper bound from explicit colouring | fracChromatic_le_total | Proved for every finite simple graph |
| Weighted double count and lower bound | coverage_double_count, weighted_lower, weighted_lower_inf | Proved for every finite simple graph; independent-set weight bound remains a hypothesis |
| Weights 2, t+1, 2 on hub/mixed/rim classes | vertexWeight t | Defined literally on vertices |
| Total weight 2(6t²+7t+3) | vertexWeight_total | Proved for every natural t |
| Hub forces absence of mixed vertices | hub_excludes_mixed | Proved for actual independent sets |
| Cyclic independence on rim fibres | rim_fibre_independent | Proved; no cardinality bound yet |
| Two-sided F(a,b) <= 0 on [1,t]² | two_sided_arithmetic | Proved over reals |
| Independent-set maximum weight <= 2(2t²+t+1) | None | Unproved |
| Fractional colouring attaining conjectured value | None | Unproved; singletonColouring proves feasibility only |
| All t >= 1 equality | Target | Proposition defined, NOT proved |

MathDB's cached record has no t quantifier bound. Source Conjecture 7.3 displays the formula without repeating one, in a paper studying nontrivial odd wheels t >= 2. The binding task requests t >= 1; Target uses exactly that. The t=1 case is W_3=K4, included in the definition but not separately proved here. No inference from the source's unrelated higher-power questions is used.
