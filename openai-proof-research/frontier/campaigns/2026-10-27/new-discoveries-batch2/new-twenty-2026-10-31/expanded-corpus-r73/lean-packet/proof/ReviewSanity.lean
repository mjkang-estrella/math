/-
  REVIEWER SUPPLEMENT (not part of the literal module `MathDB378395`).
  Prints the literal statement of the conjecture, the endpoint types and their transitive axioms,
  and checks non-vacuity of the witness: the facet is a nonempty proper subset of the cone.
-/
import MathDB378395
set_option warningAsError true
open MathDB378395 MathDB378395.Main MathDB378395.Cert
#print CollapsingConjecture
#print ObtainedByCollapsing
#print IsFacet
#print IsFace
#print marginalCone
#print margins
#print collapseMap
#print IsCollapsing
#print IsElementaryMerge
#check (collapsing_conjecture_false : ¬ CollapsingConjecture)
#check (exists_noncollapsible_facet : ∃ F : Set (Margin 4 4 5 → ℝ),
  IsFacet (marginalCone 4 4 5) F ∧ ¬ ObtainedByCollapsing 4 4 5 4 4 4 F)
-- non-vacuity: a tight column lies in F and the column of c0 lies in the cone but not in F
example : col (bcell 0) ∈ F := (col_mem_F_iff _).mpr (ell_basis 0)
example : col c0 ∈ marginalCone 4 4 5 ∧ col c0 ∉ F :=
  ⟨col_mem c0, fun h => by have := (col_mem_F_iff c0).mp h; rw [ell_c0] at this; exact one_ne_zero this⟩
#print axioms collapsing_conjecture_false
#print axioms exists_noncollapsible_facet
