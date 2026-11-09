import StackSortTaggedCount6
import StackSortFixedCount6
open Filter Topology
namespace StackSort.Round6

theorem taggedDeletionCount_proved : Del5.TaggedDeletionCount := Del6.taggedDeletionCount_proved

theorem fixedMaximumDecomposition_proved : Del5.FixedMaximumDecomposition :=
  Fixed6.fixedMaximumDecomposition_proved

theorem maximumFinalCount_proved : Round3.MaximumFinalCount :=
  Del5.maximumFinalCount_of_bridges fixedMaximumDecomposition_proved taggedDeletionCount_proved

theorem additiveRecursion_proved : Seeds2.AdditiveRecursion :=
  Round3.additiveRecursion_of_counts Cut5.commonCutCount_proved maximumFinalCount_proved

theorem exactSeeds20_proved : ExactSeeds20 := Round3.exactSeeds20_of_recursion additiveRecursion_proved

theorem lower130 : Lower130 := Round3.lower130_of_recursion additiveRecursion_proved

theorem mathdb_345545 : ¬ Conj := Round3.mathdb_345545 additiveRecursion_proved

theorem limit_ge : ∀ L, Tendsto (fun n => deg n ^ (1 / (n : ℝ))) atTop (𝓝 L) → (1.73 : ℝ) ≤ L :=
  Round3.limit_ge additiveRecursion_proved

theorem nonvacuity : ∃ᶠ n in atTop, (1.73 : ℝ) < deg n ^ (1 / (n : ℝ)) :=
  Round3.nonvacuity additiveRecursion_proved

theorem subsequence_companion : ∀ k, (1.73 : ℝ) < roots (index 130 k) :=
  Round3.subsequence_companion additiveRecursion_proved

theorem mathdb_345545_max : ¬ ConjMax := StackSort.mathdb_345545_max

theorem max_companion : ∀ n, 5 ≤ n → (1.73 : ℝ) < maxRoots n := StackSort.max_companion
end StackSort.Round6
#print axioms StackSort.Round6.taggedDeletionCount_proved
#print axioms StackSort.Round6.fixedMaximumDecomposition_proved
#print axioms StackSort.Round6.maximumFinalCount_proved
#print axioms StackSort.Round6.additiveRecursion_proved
#print axioms StackSort.Round6.exactSeeds20_proved
#print axioms StackSort.Round6.lower130
#print axioms StackSort.Round6.mathdb_345545
#print axioms StackSort.Round6.limit_ge
#print axioms StackSort.Round6.nonvacuity
#print axioms StackSort.Round6.subsequence_companion
#print axioms StackSort.Round6.mathdb_345545_max
#print axioms StackSort.Round6.max_companion
