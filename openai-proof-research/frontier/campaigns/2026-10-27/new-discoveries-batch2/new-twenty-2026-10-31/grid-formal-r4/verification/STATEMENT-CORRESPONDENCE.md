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

## Round 3 additions

Grid343536.exceptional_no_iso proves literally ExceptionalNoIso as defined in
the frozen GridFinal module, for all natural k with 2 ≤ k ≤ 3. The target
uses EqPart of the literal grid and Subgroup of its full graph automorphism
group. Explicit subgroups supply a lower bound; no replacement of the full
automorphism group by an assumed abstract dihedral group occurs.

relEquitable uses finite neighbour counts for a decidable binary relation.
relEquitable_iff identifies this with the original Nat.card definition of
IsEquitable when the relation is a setoid. Candidate partitions block2 and
block3 are actual kernels. The certificate proves completeness before counting.

free_column_path and free_row_path use HasFreeVertex in the full automorphism
group. They cover all m ≥ 1 with n = 1 and all n ≥ 1 with m = 1.

GridFinal3.mathdb_343536 has the same literal conclusion as the frozen endpoint,
with only MainOrbit and FreeClassification as premises. No unconditional
Conjecture 5.6 theorem is claimed.

## Round 4 update

No definitions or quantifiers were changed. The theorem
Grid343536.free_classification proves the exact inherited FreeClassification
Prop, concerning the full graph automorphism group, for all positive sizes.
It uses no MainOrbit assumption. GridFinal4.mathdb_343536 is the same literal
three-sentence conjunction, now conditional only on the exact inherited
Grid343536.MainOrbit Prop. The complete lattice instance is inherited.
The source partition order remains refinement. No new novelty claim is made.
