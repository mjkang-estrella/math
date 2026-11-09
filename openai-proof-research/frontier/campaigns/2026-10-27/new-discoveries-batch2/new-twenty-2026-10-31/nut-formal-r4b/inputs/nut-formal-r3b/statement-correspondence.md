# Statement correspondence

Primary cached text, arXiv:2411.16904, line 877, Conjecture 16:
“There exists no cubic 8-circulant nut graph.” The inherited Nut8.Target is
unchanged and has no new inhabitant in this lane.

| Assignment | Declaration or artifact | Exact scope / limitation |
| --- | --- | --- |
| Fixed finite interface | Nut8.FiniteObstruction in FiniteGrammar | Unchanged definition: ∀ C ε s, Admissible C ε s → ¬ (C.det = 0 ∧ ∀ i, C.adjugate i i ≠ 0) |
| Required theorem | finite_obstruction | ABSENT |
| Sign-free grammar | Nut8.Structural; admissible_structural | Structural C s := Admissible C (-1) s; every Admissible C ε s implies it |
| Permutation invariance | admissible_relabel; relabel_principal | Every permutation of Fin 8; cofactor at i becomes cofactor at e i |
| Determinant relabelling | Matrix.det_submatrix_equiv_self | Imported mathlib theorem, no additional hypothesis |
| Switching invariance | structural_switch; switch_det; switch_principal | Every diagonal sign function; latter two generic in dimension |
| Transport | obstruction_of_switch; obstruction_of_relabel | A refutation for a representative implies refutation for the original |
| Explicit isomorphism checks | GraphExtensions*.checked; graphIsoCheck_sound | Permutation list and equality of every encoded adjacency bit |
| Finite extension closure | GraphClosure*.closed*; extensionClosed_sound | Every eligible bitmask for each specified source has a checked target; no universal graph induction |
| Tree sign construction | treeSign_unit; treeSign_edge; treeSign_weight | Arbitrary strictly decreasing parent map; no extraction of parents from connected graphs |
| Actual matrix certificates | Certificates0000.certificate0 through certificate31 | First 32 exact r2 records, each actual det or diagonal adjugate equality using sparseDet correctness |
| Universal normal form | None | Missing B2 graph induction, B3 augmentation and B4 graph-to-tree bridge |

No new prior-art or novelty clearance is claimed. This is implementation work
on an already reserved target, with zero acceptance credit.
