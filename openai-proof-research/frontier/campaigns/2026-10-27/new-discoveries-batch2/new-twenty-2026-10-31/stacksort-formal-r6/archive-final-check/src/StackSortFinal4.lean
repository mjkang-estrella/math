import StackSortFinal3
import StackSortLabels4
import StackSortCount4
import StackSortDeletion4

open Filter Topology
namespace StackSort.Round4

/-- PARTIAL round 4: both exact counting obligations remain explicit hypotheses. -/
theorem exactSeeds20_of_counts (hc : Round3.CommonCutCount) (hm : Round3.MaximumFinalCount) :
    ExactSeeds20 := Round3.exactSeeds20_of_recursion (Round3.additiveRecursion_of_counts hc hm)

theorem lower130_of_counts (hc : Round3.CommonCutCount) (hm : Round3.MaximumFinalCount) :
    Lower130 := Round3.lower130_of_recursion (Round3.additiveRecursion_of_counts hc hm)

theorem mathdb_345545 (hc : Round3.CommonCutCount) (hm : Round3.MaximumFinalCount) : ¬ Conj :=
  Round3.mathdb_345545 (Round3.additiveRecursion_of_counts hc hm)

theorem limit_ge (hc : Round3.CommonCutCount) (hm : Round3.MaximumFinalCount) : ∀ L,
    Tendsto (fun n => deg n ^ (1 / (n : ℝ))) atTop (𝓝 L) → (1.73 : ℝ) ≤ L :=
  Round3.limit_ge (Round3.additiveRecursion_of_counts hc hm)

theorem nonvacuity (hc : Round3.CommonCutCount) (hm : Round3.MaximumFinalCount) :
    ∃ᶠ n in atTop, (1.73 : ℝ) < deg n ^ (1 / (n : ℝ)) :=
  Round3.nonvacuity (Round3.additiveRecursion_of_counts hc hm)

theorem subsequence_companion (hc : Round3.CommonCutCount) (hm : Round3.MaximumFinalCount) :
    ∀ k, (1.73 : ℝ) < roots (index 130 k) :=
  Round3.subsequence_companion (Round3.additiveRecursion_of_counts hc hm)

theorem mathdb_345545_max : ¬ ConjMax := StackSort.mathdb_345545_max

theorem max_companion : ∀ n, 5 ≤ n → (1.73 : ℝ) < maxRoots n := StackSort.max_companion

end StackSort.Round4

#print axioms StackSort.Round4.exactSeeds20_of_counts
#print axioms StackSort.Round4.lower130_of_counts
#print axioms StackSort.Round4.mathdb_345545
#print axioms StackSort.Round4.limit_ge
#print axioms StackSort.Round4.nonvacuity
#print axioms StackSort.Round4.subsequence_companion
#print axioms StackSort.Round4.mathdb_345545_max
#print axioms StackSort.Round4.max_companion
#print axioms StackSort.Round4.irreducible_suffix_unique
#print axioms StackSort.Round4.labelledIrreducibles_card
#print axioms StackSort.Round4.delete_last_collision_iff
#print axioms StackSort.Round4.commonCutCount_one_left
