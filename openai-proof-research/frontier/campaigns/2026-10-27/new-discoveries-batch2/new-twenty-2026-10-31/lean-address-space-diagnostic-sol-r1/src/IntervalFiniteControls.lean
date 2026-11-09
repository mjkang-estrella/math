import IntervalBlockCounts
import IntervalGridAdditive
import Mathlib.Algebra.Order.Group.Int
namespace IntervalWidth
theorem balanced_nontrivial : (balancedBlock 7 3 0).card = 3 ∧
    (balancedBlock 7 3 1).card = 2 ∧ (balancedBlock 7 3 2).card = 2 := by decide
theorem grid_positive_control : (0 : Int) ≤ 0 + (0+0) ∧ (0 : Int) ≤ 0 + (0+0) := by
  apply cdf_grid_envelope 1 (by decide) (fun q : Nat => q)
    (fun _ => (0 : Int)) (fun _ => (0 : Int))
    (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) 0 0
    (fun _ _ => ⟨le_rfl,le_rfl⟩) (fun _ _ => le_rfl) 0 le_rfl (by decide)
#print axioms balanced_nontrivial
#print axioms grid_positive_control
end IntervalWidth
