import FlatBalance

/-!
# MathDB 352972 audit: transitive axioms, body origin, safety

Prints the transitive axiom dependencies of every endpoint-relevant theorem of
`FlatBalance`, and the bodies of the definitions on which the literal
(refutation) endpoint rests.  Allowed axioms: `propext`,
`Classical.choice`, `Quot.sound` only; no `sorry`, `admit`, added `axiom`s,
`unsafe`, `partial`, or `native_decide`.
-/

-- Endpoint chain: literal universal negation and existential counterexample.
#print axioms FlatBalance.not_flat_balanced_conjecture
#print axioms FlatBalance.flat_not_balanced_exists
#print axioms FlatBalance.FlatBalancedConjecture

-- Unbalancedness and discrepancies of the witness (both conventions).
#print axioms FlatBalance.K33_not_balanced
#print axioms FlatBalance.K33_discrepancy_gt_one
#print axioms FlatBalance.K33_discrepancyPos_gt_one
#print axioms FlatBalance.discrepancyNat_K33
#print axioms FlatBalance.discrepancyNatPos_K33

-- Parity sums bridge (finite range, integer absolute value).
#print axioms FlatBalance.oddCliqueSum_K33
#print axioms FlatBalance.evenCliqueSum_K33
#print axioms FlatBalance.evenCliqueSumPos_K33

-- Exact clique counts of the witness (c0=1, c1=6, c2=9, higher 0).
#print axioms FlatBalance.cliqueCount_K33_zero
#print axioms FlatBalance.cliqueCount_K33_one
#print axioms FlatBalance.cliqueCount_K33_two
#print axioms FlatBalance.cliqueCount_K33_three
#print axioms FlatBalance.cliqueFinset_K33_ge3

-- Flatness (every edge in at most two triangles) and the empty triangle sets.
#print axioms FlatBalance.K33_flat
#print axioms FlatBalance.K33_triangleSet_empty

-- The witness graph structure: symmetry/irreflexivity faithfulness.
#print axioms FlatBalance.K33
#print axioms FlatBalance.K33_adj_ne
#print axioms FlatBalance.K33_symm

-- Definitional bodies (body-origin record; no opaque or generated bodies).
#print FlatBalance.SimpleGraph
#print FlatBalance.IsClique
#print FlatBalance.cliqueFinset
#print FlatBalance.cliqueCount
#print FlatBalance.triangleSet
#print FlatBalance.Flat
#print FlatBalance.oddCliqueSum
#print FlatBalance.evenCliqueSum
#print FlatBalance.evenCliqueSumPos
#print FlatBalance.discrepancyNat
#print FlatBalance.discrepancyNatPos
#print FlatBalance.Balanced
#print FlatBalance.FlatBalancedConjecture
