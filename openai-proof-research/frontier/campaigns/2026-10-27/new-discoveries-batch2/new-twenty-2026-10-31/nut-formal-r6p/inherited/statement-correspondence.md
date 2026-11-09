# Statement correspondence

| Declaration | Exact scope | Source/goal correspondence |
|---|---|---|
| Nut8.Coverage8 | Structural C s implies a permutation and membership in GraphClosure7_000.targets with SupportCode | Fixed root interface, unchanged; no inhabitant supplied |
| Nut8.catalogueGraph_adj | SimpleCode n code implies Adj i j iff graphBit n code i.val j.val = true | Goal 1, step 1 |
| Nut8.catalogue_simple_1 .. catalogue_simple_8 | Every code in the actual corresponding catalogue list is SimpleCode | Goal 1, step 1; no universal graph classification asserted |
| Nut8.extendLabels_last / extendLabels_castSucc | Full permutation sends the last vertex to v and old i to v.succAbove (e i) | Goal 1, step 2 |
| Nut8.transportedMask_lt | transportedMask G v e < 2^n | Goal 1, step 2 |
| Nut8.transportedMask_bit | Bit i is true iff G.Adj v (v.succAbove (e i)) | Goal 1, step 2; no eligibility asserted |
| Nut8.encodeBits_testBit | Test bit of a sum of distinct selected powers is the selected Boolean inside the bound and false outside | General no-carry binary lemma |
| Nut8.extendGraph_testBit | Every in-domain extension bit equals extensionBit | Goal 1, step 4, arbitrary n |
| Nut8.transported_extension_spec | Old deletion adjacency specification implies the full transported graph has extendGraph adjacency | Goal 1, step 4; no eligibility or catalogue membership implied |
| Nut8.finite_of_parts | Coverage8 → PerSupport → FiniteObstruction | Exact goal 2, proved using admissible_structural, admissible_relabel, obstruction_of_relabel |
| Nut8.endpoint_of_finite | FiniteObstruction → Target | Inherited r4a, unchanged |
| Nut8.target_of_parts | Coverage8 → PerSupport → Target | Checked conditional composition; both assumptions remain |
| Nut8.nut8_target | PerSupport → Target | Requested assembly source only; NOT checked because Coverage8.lean is absent |

The literal Nut8.Target is inherited unchanged from Nut.lean. No stronger
scientific claim or literature novelty is made by this partial formalization.
