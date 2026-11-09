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

## r3 semantic evaluation continuation

| Source obligation | Added formal object | Scope and limitation |
|---|---|---|
| Enumerate every vertex subset | MaskR3.complete and decode_inj | Arbitrary n; Nat.testBit masks below 2^n are a bijective encoding of Fin n subsets. |
| Retain exactly maximum independent sets | MaskR3.best_iff, maxima_eq and best_of_checks | Definitions use the literal Independent and Maximum predicates; block certificates have a proved semantic bridge. |
| Canonical depth-2 edge-rooted cubic shapes | TreeModelsR3.Counts, graph and pattern | Four labelled leaf counts in Fin 3; graph has at most 14 vertices. The zero-leaf form is included even though it has depth 1. |
| Actual layers and uniform maximum-set expectations | TreeModelsR3.distance_eq, layer_eq and expectation_eq | Proved for every Counts value; not merely arithmetic state summaries. |
| Finite separating bound | EvalR3_*.bound_* and BridgeR3.all_81 | All 81 labelled forms; no symmetry reduction is needed. Strict replay status is in results.json. |
| Arbitrary finite tree to canonical form | TreeModelsR3.ClassifiedCubicTrees | An explicit open hypothesis, not a proved classification. |
| Universal tree bound | TreeModelsR3.tree_bound_of_classification | Conditional on ClassifiedCubicTrees. |
| Negation of Conjecture 2 | TreeModelsR3.neg_conjecture_of_classification | Conditional, Type 0; no unconditional refutation or higher-universe endpoint. |

The 81 forms and their numerical data are generated in Python only as proposed certificates. Every accepted certificate is subsequently checked by ordinary kernel reduction and the sound mask bridge. The generator is not a trusted proof dependency. No prior-art searches were repeated.
