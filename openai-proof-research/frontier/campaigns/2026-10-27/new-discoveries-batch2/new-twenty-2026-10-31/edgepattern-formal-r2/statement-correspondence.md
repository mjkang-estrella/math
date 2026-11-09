# Statement correspondence

| Source/task requirement | Declaration or artifact | Status |
|---|---|---|
| finite simple graph with root edge | EdgePattern.Rooted | Defined |
| distance to edge, layers, exact/upper depth | rootDistance, layer, ExactDepth, DepthAtMost | Defined using extended shortest-path distance, avoiding disconnected-distance collapse |
| cubic/degree-d pattern | RegularPattern | Defined; degree exactly d below deepest two layers |
| girth at least / exactly g | GirthAtLeast, ExactGirth | Defined via all cycle walks and existence of an attaining cycle |
| maximum independent sets | Independent, Maximum, maxima | Defined literally; no maximal-set substitution |
| uniform expectation | expectation | Defined over every maximum independent set |
| T'_r(d) | TreeFamily | Defined with exact depth r and acyclicity |
| weaker relation | Weaker | Defined with positive rational tests, real constraints |
| all d,r, arbitrary finite vertex types | Conjecture2 | Defined in arbitrary universe; d≥3,r≥1; tree vertex types also arbitrary |
| witness graph and root | Concrete.graph, Concrete.pattern | Constructed and root adjacency checked |
| full maximum-set classification | Concrete.maximum_iff, Concrete.maxima_eq | Proved; universal over all subsets of Fin 8 |
| supplied layer subset occupancies | Concrete.totals_values, occupancy_values | Proved (2,14,4), then (2/5,14/5,4/5); metric bridge missing |
| strictly positive alpha, strict separation | Concrete.alpha_positive, separating_value, separating_lt_one | Proved for Concrete.occupancy; not yet expectation |
| independent sets and maxima under isomorphism | independent_map_iff, maximum_map_iff | Proved for arbitrary vertex types |
| expectation invariant under rooted isomorphism | none | Missing |
| every source tree has canonical form | none | Missing |
| all 81 arithmetic summaries | Canonical.all_81 | Proved by kernel decide; no graph-semantic soundness claim |
| universal bound on all source trees | none | Missing |
| finite real convex separation | finite_separation | Proved with explicit positive test, family-bound and witness-bound hypotheses |
| literal negation of source conjecture | none | Missing, zero credit |

## r2 additions

| Source obligation | Checked declaration | Scope |
| --- | --- | --- |
| Rooted graph isomorphism preserves layers and e_i | RootedIso.distance_eq, RootedIso.layer_map, RootedIso.expectation_eq | All finite types, independent universes |
| Witness has depth 2 and cubic regularity in Definition 1 | Concrete.distance_values, Concrete.regular | Actual graph-distance layers |
| Witness attains girth 2r+2 = 6 | Concrete.girth_at_least, Concrete.exact_girth | Every cycle, plus explicit six-cycle |
| Witness's source expectation | Concrete.expectation_values | Uniform over all five maximum independent sets |
| Exact separating weight | Concrete.expectation_separating_value, Concrete.expectation_separating_lt_one | Actual e_i, rational arithmetic |
| Final reduction | neg_conjecture_of_tree_bound | Conditional on unproved CubicTreeBound, universe 0 |

The generic tree classification and recursion-semantic correspondence remain open. The original arithmetic 81-case check is not used to assert the universal tree bound.
