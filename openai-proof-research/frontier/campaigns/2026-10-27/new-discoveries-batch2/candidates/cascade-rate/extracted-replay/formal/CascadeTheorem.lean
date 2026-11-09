import SelectedCounting
import KraftSummability
set_option autoImplicit false
set_option warningAsError true
namespace CascadeRate
/-- The actual fixed cascade series converges, but has no geometric rate. -/
theorem convergent_non_geometric :
    Summable (kappa sourceTree (fairAssignment sourceTree) [true]) ∧
    (∑' n, kappa sourceTree (fairAssignment sourceTree) [true] n) ≤ 2 ∧
    ¬ GeometricDecay (kappa sourceTree (fairAssignment sourceTree) [true]) :=
  ⟨sourceTree_fair_one_series.1, sourceTree_fair_one_series.2, fixed_kappa_not_geometric⟩
end CascadeRate
