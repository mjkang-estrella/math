import StackSortInj2Fixed
import StackSortInj2Linkage
open Filter Topology
namespace StackSort.Inj2
/-- Partial round 2A endpoint: the two injection bounds remain explicit. -/
theorem mathdb_345545 (hd : StackSort.DoublingInjection) (hr : StackSort.RootSplit)
    (hs : StackSort.ExactSeeds20) : ¬ StackSort.Conj :=
  StackSort.mathdb_345545 (doubling_of_injection hd) (lower130_of_seeds hr hs)
theorem limit_ge (hd : StackSort.DoublingInjection) (hr : StackSort.RootSplit)
    (hs : StackSort.ExactSeeds20) :
    ∀ L, Tendsto (fun n => StackSort.deg n ^ (1 / (n : ℝ))) atTop (𝓝 L) → (1.73 : ℝ) ≤ L :=
  StackSort.limit_ge (doubling_of_injection hd) (lower130_of_seeds hr hs)
theorem nonvacuity (hd : StackSort.DoublingInjection) (hr : StackSort.RootSplit)
    (hs : StackSort.ExactSeeds20) :
    ∃ᶠ n in atTop, (1.73 : ℝ) < StackSort.deg n ^ (1 / (n : ℝ)) :=
  StackSort.nonvacuity (doubling_of_injection hd) (lower130_of_seeds hr hs)
theorem subsequence_companion (hd : StackSort.DoublingInjection) (hr : StackSort.RootSplit)
    (hs : StackSort.ExactSeeds20) :
    ∀ k, (1.73 : ℝ) < StackSort.roots (StackSort.index 130 k) :=
  StackSort.subsequence_companion (doubling_of_injection hd) (lower130_of_seeds hr hs)
end StackSort.Inj2
