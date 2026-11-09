# Statement correspondence

All inherited definitions and declarations are byte-identical. The source standing assumptions, graph labellings as edge equivalences, explicit +1 shift, degree-one leaves, chiLA and FullTree predicate are unchanged.

| Obligation | Round 3 result | Status |
| --- | --- | --- |
| Depth-two root/special low-label partition | lowMap_bijective and formula agreement | Proved symbolically |
| Depth-two middle-block partition | middleMap_bijective, middleEntry_unique, depthTwo_middle | Proved symbolically |
| Depth-two closed row weights | depthTwo_root_sum, depthTwo_ordinary_weight, depthTwo_special_weight | Proved symbolically |
| Literal incidence specialization | literal_weight_row, literal_depthTwo_root, literal_depthTwo_row_one | Proved for a supplied formula-realizing edge equivalence |
| Full even depth-two construction, t >= 4 | DepthTwoConstruction | Open |
| Higher-depth construction, even t >= 4 | NonbinaryHigherConstruction | Open |
| Higher-depth binary patch | BinaryHigherConstruction | Open |
| Arbitrary source-tree isomorphism | ModelBridge | Open |
| Model least spectrum | Round3.even_case | Conditional on the three construction Props |
| Arbitrary finite full-tree spectrum and chiLA | Round3.mathdb_354228 | Conditional on those Props and ModelBridge |

remaining_iff proves the three construction Props jointly equivalent to the exact inherited RemainingConstruction. Axioms printed for conditional endpoints are not proofs of their hypotheses. Finite regressions remain regressions.
