# Statement correspondence

| Required item | Lean declarations | Scope and status |
| --- | --- | --- |
| Literal graph predicates | Literal.lean, byte-identical to r1 | SimpleGraph, regularity, connectivity, bijective labels in Fin n -> ZMod 2, zero open or closed sums |
| Literal printed refutation | XorMagic.not_printed_all; not_printed_positive; not_printed_ge_four | Complete, unchanged from r1 |
| Corrected bases | XorMagic.corrected_at_4; corrected_at_5 | Complete, all 32 finite graph certificates unchanged |
| Universal corrected statement | No declaration | **Absent** |
| Scalar F4 maps | omega_cube; omega_sum; omega_add; omega_fixed; omegaSq_fixed | Complete finite identities for Four = ZMod 2 × ZMod 2 |
| Label bridge | bitsFourEquiv; bitsFourEquiv_add | Explicit additive equivalence Bits n × Four to Bits (n+2) |
| Fibre finite argument | affine_bijective; affine_unique_fixed; invariant_fibre_sizes; invariant_singleton; invariant_three_complement | Complete finite statements; not yet connected to graph components |
| Translation cardinality | translation_exists; translation_exists_four | Complete abstract lemmas; edge maps and witness not instantiated |
| Factored seeds | Seed16Closed4.seed; Seed16Open5.seed; Seed32Closed4.seed; Seed32Open5.seed | Both decompositions and explicit cycles bound directly to r1 graphs; persistence absent |
| Interpolation arithmetic | interpolation_indices; interpolation_degree | Exact d+2t index coverage; literal parity assembly and graph operation absent |
| Sum of all labels | total_bits; total_labels | All n >= 2, complete |
| High-degree connectivity | connected_of_high_degree | Any nonempty finite regular graph with |V| <= 2d, complete |
| Complement magic bridges | closed_to_open_compl; open_to_closed_compl | Complete with explicit high-degree condition for connectivity |
| Uniform literal obstruction | no_closed_top_four; not_closed_top_four | Closed degree 2^n-4 impossible for all n >= 2 |

Declarations are in namespace XorMagic unless a fuller prefix is displayed. Literal.lean itself has no edits. Helper hypotheses are described explicitly; none is a surrogate endpoint for CorrectedAt.
