# Statement correspondence

Frozen GridBasic uses Mathlib pathGraph.boxProd on Fin m × Fin n.
IsEquitable is Definition 5.1: equality of neighbour counts in every class for
vertices in a common class. EqPart is the corresponding Setoid subtype in source
refinement order: finer ≤ coarser (v2 lines 111–116). orbitSetoid uses subgroups
of the full graph automorphism group. HasFreeVertex uses that full group.

GridLattice supplies the complete lattice on this same order, for all finite
graphs. Arbitrary joins are ordinary Setoid joins; meets are joins of equitable
common refinements, matching Proposition 4.5 and Example 5.3. No MainOrbit premise
is used in this construction. neighbourCells uses Quotient r and a multiset;
equitable_iff_neighborCells proves the literal Definition 5.1 bridge.

row_determinism uses the actual first row. positive_layer_propagation requires
every layer value ≥ 1. transportPartition f r relates u,v exactly when
r (f.symm u) (f.symm v). Conjugation back is f.symm ∘ g ∘ f. A0 membership
still needs generator conjugation identities; it is not inferred without proof.

GridFinal2.mathdb_343536 is the exact original conjunction for m,n ≥ 1,
CONDITIONAL on exactly MainOrbit, FreeClassification and ExceptionalNoIso.
Their full quantified definitions remain frozen in src/GridFinal.lean.
No axiom or placeholder discharges them. There is no unconditional endpoint.
