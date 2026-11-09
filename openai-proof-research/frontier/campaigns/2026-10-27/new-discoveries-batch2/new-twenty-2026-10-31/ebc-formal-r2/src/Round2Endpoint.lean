import Splitting
import BFSRecurrence
import Endpoint
import BFSTable
namespace EBC337062
/-- The table bridge is now unconditional. -/
theorem distanceAndCounts : DistanceAndCounts := by
  intro a t
  exact ⟨g32_dist_table a t, g32_sigma_table a t⟩

/-- Round 2 endpoint: only the edge-splitting proposition remains. -/
theorem conjecture21_false_of_pathSplitting (hs : PathSplitting32) : ¬ Conjecture21 :=
  conjecture21_false distanceAndCounts hs

#print axioms EBC337062.distanceAndCounts
#print axioms EBC337062.conjecture21_false_of_pathSplitting

/-- The predecessor certificate supplies walks between every pair. -/
theorem g32_connected : G32.Connected := by
  constructor
  · intro a t
    obtain ⟨w, _⟩ := exists_walk_of_labels G32 t (fun a => tabDist a.val t.val)
      (table_zero t) (table_pred t) a
    exact w.reachable

/-- The second and last round-1 bridge is discharged by the general splitting theorem. -/
theorem pathSplitting32 : PathSplitting32 := by
  intro x y u v _ h
  exact sigmaEdge_split G32 g32_connected x y u v h

/-- Literal unconditional refutation of the complete seven-class conjecture. -/
theorem conjecture21_false_unconditional : ¬ Conjecture21 :=
  conjecture21_false distanceAndCounts pathSplitting32

#print axioms EBC337062.conjecture21_false_unconditional
end EBC337062
