import Definitions
namespace AK350721
open Finset MvPolynomial

theorem sign_control3 (pi : Equiv.Perm (Fin 3)) (h : cycleGe 3 pi) :
    (-1 : ℤ) ^ invCount pi = 1 := by
  fin_cases pi <;> revert h <;> unfold cycleGe <;> decide

/-- At (3,3) all admissible permutations have positive inversion sign, so the
literal polynomial is the map of its sum of natural monomials. -/
theorem nonvacuity_control : InNat (F 3 3) := by
  classical
  refine ⟨∑ pi ∈ univ.filter (cycleGe 3),
    (∏ i ∈ rlmv pi, (X (Sum.inl i) : MvPolynomial (Fin 3 ⊕ Fin 3) ℕ)) *
    (∏ i ∈ excv pi, X (Sum.inr i)), ?_⟩
  simp only [F, show (-1 : ℤ) ^ (3 - 1) = 1 by norm_num, map_one, one_mul,
    rawSum, map_sum, map_mul, map_prod, map_X]
  apply Finset.sum_congr rfl
  intro pi hp
  rw [sign_control3 pi (Finset.mem_filter.mp hp).2]
  simp [term]
end AK350721
