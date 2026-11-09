import StackSortRootSplit3
import StackSortDoubling3
import StackSortSeeds3
import StackSortInj2Final
import StackSortControls
import StackSortInj2Controls
import StackSortSeeds2Controls
open Filter Topology
namespace StackSort.Round3
/-- Partial round 3 endpoint: only the two tuple counting identities remain. -/
theorem exactSeeds20_of_recursion (h : Seeds2.AdditiveRecursion) : ExactSeeds20 :=
  Seeds2.exactSeeds20_of_additiveRecursion h
 theorem lower130_of_recursion (h : Seeds2.AdditiveRecursion) : Lower130 :=
  lower130_of_seeds rootSplit_proved (exactSeeds20_of_recursion h)
 theorem mathdb_345545 (h : Seeds2.AdditiveRecursion) : ¬ Conj :=
  StackSort.mathdb_345545 doubling_proved (lower130_of_recursion h)
 theorem limit_ge (h : Seeds2.AdditiveRecursion) : ∀ L,
    Tendsto (fun n => deg n ^ (1 / (n : ℝ))) atTop (𝓝 L) → (1.73 : ℝ) ≤ L :=
  StackSort.limit_ge doubling_proved (lower130_of_recursion h)
 theorem nonvacuity (h : Seeds2.AdditiveRecursion) :
    ∃ᶠ n in atTop, (1.73 : ℝ) < deg n ^ (1 / (n : ℝ)) :=
  StackSort.nonvacuity doubling_proved (lower130_of_recursion h)
 theorem subsequence_companion (h : Seeds2.AdditiveRecursion) :
    ∀ k, (1.73 : ℝ) < roots (index 130 k) :=
  StackSort.subsequence_companion doubling_proved (lower130_of_recursion h)
 theorem mathdb_345545_max : ¬ ConjMax := StackSort.mathdb_345545_max
 theorem max_companion : ∀ n, 5 ≤ n → (1.73 : ℝ) < maxRoots n :=
  StackSort.max_companion
end StackSort.Round3
