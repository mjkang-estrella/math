import Symmetry
import Mathlib.Algebra.Order.Archimedean.Real.Basic
set_option autoImplicit false
set_option warningAsError true
namespace FloorSums
open Finset

theorem actual_real_floor (n m : ℕ) :
    ⌊((n : ℝ) / (m : ℝ))⌋ = ((n/m : ℕ) : ℤ) := by
  rw [Int.floor_div_natCast, Int.floor_natCast, Int.natCast_ediv]

theorem actual_source_sum (m K : ℕ) (a : Fin 4 → ℕ) :
    (∑ j ∈ range (K+1), ∑ T ∈ (univ : Finset (Fin 4)).powerset,
      (-1 : ℤ)^(4-T.card) * ⌊(((j + ∑ i ∈ T, a i : ℕ) : ℝ)/(m : ℝ))⌋) =
      literalSum m K a := by
  simp only [actual_real_floor, literalSum]

theorem source_arguments (m : ℕ) (a : Fin 4 → ℕ) (hm : 0 < m)
    (j : ℕ) (T : Finset (Fin 4)) :
    (0 : ℝ) < (m : ℝ) ∧ 0 ≤ (((j+∑ i ∈ T, a i : ℕ) : ℝ)/(m : ℝ)) := by
  constructor
  · exact_mod_cast hm
  · positivity

end FloorSums
