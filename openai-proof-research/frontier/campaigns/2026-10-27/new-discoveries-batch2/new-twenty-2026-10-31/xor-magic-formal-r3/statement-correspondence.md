# Statement correspondence

| Required item | Lean declarations | Scope and status |
| --- | --- | --- |
| Literal graph predicates | Literal.lean, byte-identical to r1 | SimpleGraph, regularity, connectivity, bijective labels in Fin n -> ZMod 2, zero open or closed sums |
| Literal printed refutation | XorMagic.not_printed_all; not_printed_positive; not_printed_ge_four | Complete, unchanged from r1 |
| Corrected bases | XorMagic.corrected_at_4; corrected_at_5 | Complete, all 32 finite graph certificates unchanged |
| Actual affine lift | affineTransport; EdgeTransport.graph; neighbors; degree; sum_label | Defined with inverse edge maps and exact coordinate formulas; special slope assignment and zero sums absent |
| Component fibres | fibreEquiv; fibre_card_reachable; section_of_singleton; section_of_three | Actual lifted components; distinguished-cycle scalar and full connectivity absent |
| Concrete translation existence | affine_translation_exists_regular | Every nonempty d-regular base on Fin m with d >= 4, any scalar assignment; c in ker B outside im D |
| Graph matching persistence | EdgeTransport.matching | Exact full decomposition of the lifted graph; complement decomposition remains absent |
| Universal corrected statement | No declaration | **Absent** |
| Scalar F4 maps | omega_cube; omega_sum; omega_add; omega_fixed; omegaSq_fixed | Complete finite identities for Four = ZMod 2 × ZMod 2 |
| Label bridge | bitsFourEquiv; bitsFourEquiv_add | Explicit additive equivalence Bits n × Four to Bits (n+2) |
| Fibre finite argument | affine_bijective; affine_unique_fixed; invariant_fibre_sizes; invariant_singleton; invariant_three_complement | Finite statements proved; fibre transport and section obstructions now proved, distinguished-cycle holonomy bridge still absent |
| Translation cardinality | translation_exists; translation_exists_four | Abstract lemmas proved; incidenceD, incidenceB, nonzero BD witness and edge count now instantiate translation existence |
| Factored seeds | Seed16Closed4.seed; Seed16Open5.seed; Seed32Closed4.seed; Seed32Open5.seed | Both decompositions and cycles bound to r1 graphs; strong cycle bridges and graph matching lift proved; complement factors and cycle persistence absent |
| Interpolation arithmetic | interpolation_indices; interpolation_degree | Exact d+2t index coverage; literal parity assembly and graph operation absent |
| Sum of all labels | total_bits; total_labels | All n >= 2, complete |
| High-degree connectivity | connected_of_high_degree | Any nonempty finite regular graph with |V| <= 2d, complete |
| Complement magic bridges | closed_to_open_compl; open_to_closed_compl | Complete with explicit high-degree condition for connectivity |
| Uniform literal obstruction | no_closed_top_four; not_closed_top_four | Closed degree 2^n-4 impossible for all n >= 2 |

Declarations are in namespace XorMagic unless a fuller prefix is displayed. Literal.lean itself has no edits. Helper hypotheses are described explicitly; none is a surrogate endpoint for CorrectedAt.

## r3 additions

All added definitions and lemmas concern the construction and its prerequisites, not the corrected endpoint. `EdgeTransport.graph` has vertices V × Four and literal adjacency G.Adj u v and transport(u,v)(x)=y. `affineTransport` uses ordered edges with three scalar choices and inverse reverse maps. `incidenceD` sends b to b_v + a_e b_u; `incidenceB` uses source coefficient 1 and target coefficient a_e inverse. `affine_translation_exists_regular` proves existence of c with Bc=0 outside im D for nonempty d-regular bases and d>=4. It does not assert that this graph is magic or connected. `constants_in_range_of_singleton` and `constants_in_range_of_three` prove concrete obstructions for actual lifted component fibres. `StrongFactorCycleData` strengthens, rather than changes, the inherited cycle definition. The universal target has no declaration.
