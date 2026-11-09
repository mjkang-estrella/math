# Statement correspondence

Source: arXiv:1908.05797v2, Definition 5.1 (text lines 266–267), Example 2.2
(lines 111–116), Conjecture 5.6 (lines 293–294 and 308–313), read from the
immutable expanded-corpus-r131 source cache. No new priority claim.

- G m n is literally Mathlib pathGraph m boxProd pathGraph n on Fin m × Fin n.
  grid_adj_iff proves the coordinate adjacency formula. Coordinates are 0-based.
- IsEquitable counts the finite subtype {x // Adj u x ∧ r x w} using Nat.card.
  This is |N(u) ∩ [w]|. Every cell has a representative w, so quantifying w
  is Definition 5.1 exactly. No decidability parameter changes the proposition.
- EqPart is an abbrev for the subtype of Setoid satisfying IsEquitable.
  Its inherited partial order is relation inclusion: finer ≤ coarser.
  This round has not yet supplied a lattice instance on that subtype.
- orbitSetoid G H relates u,v iff some g∈H sends u to v; H is a subgroup
  of the FULL graph automorphism group G ≃g G, acting on vertices.
- HasFreeVertex states ∃x, every automorphism fixing x equals 1. It is
  equivalent to the stabilizer subgroup being trivial.
- mathdb_343536 has exactly three conjuncts, universally quantified over m,n≥1:
  S1 equitable iff subgroup orbit; S2 abstract order isomorphism iff free vertex;
  S3 free vertex iff ¬(2≤m ∧ m=n ∧ n≤3). An order isomorphism of lattices is a
  lattice isomorphism. Lattice construction remains an infrastructure task.
- natural_iso_iff additionally gives the stronger NATURAL-map reading of S2.
  naturalIso has subgroup-to-partition orientation and preserves refinement.
- mathdb_343536 is CONDITIONAL on exactly three explicit Prop premises:
  MainOrbit, FreeClassification, ExceptionalNoIso (see GridFinal.lean).
  These premises have not been discharged. There is no unconditional solution.
- GridRegression.labelEquitable is the finite-list computation of the same
  neighbour counts; labelEquitable_iff connects it to IsEquitable.
  The table tests do not prove exhaustive counts or subgroup enumeration.
