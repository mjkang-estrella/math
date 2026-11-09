# Statement correspondence

Primary input: Bašić–Damnjanović, arXiv:2411.16904, Section 1, Sections 2–3,
and Conjecture 16 (cached text line 877): “There exists no cubic 8-circulant nut
graph.” No live prior-art or acceptance gate is claimed by this implementation.

| Requirement | Declaration | Exact scope and remaining limit |
| --- | --- | --- |
| Source cyclic group definition | CyclicGroupCirculant, cyclicGroupCirculant_iff | A cyclic subgroup of vertex permutations preserving adjacency; its literal subgroup orbits have the prescribed count and common size; equivalent to inherited Circulant |
| Original target | Nut8.Target | Inherited bytes unchanged; no inhabitant |
| Global coordinates | nut_circulant_global_coordinates | Inherited unchanged |
| Actual graph transport | coordinateGraph, coordinateGraph_adjacency | Pullback through the full vertex equivalence; adjacency commutes with transport |
| Translation invariance | coordinateGraph_translation | Derived from the generator action formula, not assumed of the original graph |
| Coordinate character | nut_coordinate_character | Actual Nut kernel, integral periodic ε, full vector, parity for ε = -1 |
| Kernel lift | characterLift, adjacency_characterLift, quotientKernelLift | Explicit linear Fourier lift into actual labelled adjacency kernel; representative evaluation proves injection |
| Real quotient nullity | nut_circulant_quotient | From Nut G and Circulant 8 G alone, yields symmetric integer quotient, real nullity 1, full real kernel vector; witnesses retain actual labelling |
| Nut connectivity | nut_crossing, nut_connected | Every nut graph, no degree or orbit hypothesis |
| Cancellation | cubic_kernel_no_cancel | No two distinct neighbors have cancelling full-kernel entries in a cubic graph |
| Coherent contributions | neighbor_character_coherent | Actual adjacent shifts to the same quotient vertex have equal character sign; assumes coordinate character formula |
| A4 principal minors | principal_minor_ne_zero | Every real symmetric (n+1) by (n+1) matrix with nullity 1 and a full kernel vector |
| A4 adjugate | full_kernel_det_adjugate | Same hypotheses imply det = 0 and every diagonal adjugate entry nonzero |
| A4 integer transfer | integer_full_kernel_det_adjugate | Eight by eight integer matrices with the corresponding real kernel hypotheses |
| Combined algebraic extraction | nut_circulant_matrix | Original nut 8-circulant yields a symmetric integer singular matrix with all principal cofactors nonzero; does NOT assert admissibility |
| A3 | None | Exact graph-to-Admissible assembly is missing; see GAPS.md |
| Requested endpoint_of_finite | None | NOT proved or declared |

## Universe and small periods

All original graph statements quantify over `V : Type` (universe zero), matching
the byte-identical Target. The matrix lemma is dimension-parametric and includes
n = 0 (one by one matrix). The real field is used throughout the graph kernel.
A nonempty nut graph forces m > 0; no m = 0 label is used. The NeZero instance
in the extraction is obtained from orbit_size_pos. No assumption m > 2 occurs.

m = 1 is allowed by both the source and the inherited definition; coordinates
have singleton orbits, with no internal simple-graph edge. The extracted
negative-character branch asserts Even m, so it cannot apply when m = 1.
m = 2 is allowed; the internal shift 1 is self-inverse, representing a semi-edge,
not a paired loop. For ε = -1 it has sign -1; for ε = 1 it has sign 1.
The general formal pairing, shared-sign classification, and diagonal grammar
including these edge cases remain part of A3. They are not claimed proved here.

The subgroup proof does not require semiregularity as an extra assumption.
Equal orbit sizes and the existing period lemma give the common period in the
actual coordinate extraction. Choosing the trivial cyclic subgroup is permitted
by the source definition and corresponds to m = 1.
