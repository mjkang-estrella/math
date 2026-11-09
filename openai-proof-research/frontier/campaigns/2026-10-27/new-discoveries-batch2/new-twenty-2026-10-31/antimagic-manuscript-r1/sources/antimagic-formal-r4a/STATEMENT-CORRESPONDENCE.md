# Statement correspondence

All 20 inherited modules are byte-identical. Labels remain literal edge equivalences into Fin |E|, with natural labels obtained by +1. Degree-one leaves, the spectrum, chiLA, the full-tree predicate, and the arbitrary-tree bridge statement are unchanged.

| Obligation | Round 4A result | Status |
| --- | --- | --- |
| Full ordinary depth-two partition | highMap_bijective, highEntry_formula, ordinary_label_unique | Proved for all s >= 2 |
| Full formula edge equivalence | formulaMap_bijective, depthTwoLabeling_label | Proved for all s >= 2 |
| Depth-two properness and exact colour count | depthTwo_local, depthTwo_colors | Proved for all s >= 2 |
| Even depth-two family, t >= 4 | depthTwoConstruction : Round3.DepthTwoConstruction | Discharged |
| Generic higher leaf permutation and sum | leafMap_bijective, leafEntry_sum | Proved symbolically |
| Direct leaf formula agreement | largeLabel_leaf | Proved under explicit parameter and parity identities |
| Generic parity shell partition and sums | shellEntry_unique, shellEntry_sum | Proved symbolically |
| Nonbinary higher-depth construction | Round3.NonbinaryHigherConstruction | Open |
| Binary higher-depth construction | Round3.BinaryHigherConstruction | Open |
| Arbitrary-tree model isomorphism | ModelBridge | Open; sibling lane |
| Model least spectrum | Round4A.even_case | Conditional on two higher construction Props |
| Arbitrary finite full-tree endpoint | Round4A.mathdb_354228 | Conditional on those Props and ModelBridge |

The completed depth-two construction matches the inherited FormulaConstruction, including equality with the reviewed piecewise formula on every child edge. The generic higher-depth helpers do not imply that their row-index bounds or tuple parameters hold in the full tree. Their explicit hypotheses must not be silently dropped. There is no claim of a closed higher-depth family or full conjecture.
