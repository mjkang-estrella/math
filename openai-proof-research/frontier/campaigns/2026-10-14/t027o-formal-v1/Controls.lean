import T027O

/-! MIT, Myeongjin Kang. Concrete controls for the scalar algebra only. -/
namespace T027OControls

def symmetricM : Fin 3 → Fin 3 → ℚ := !![0, 1, 1; 1, 0, 1; 1, 1, 0]
def cycleE : Fin 3 → Fin 3 → ℚ := !![0, 1, -1; -1, 0, 1; 1, -1, 0]

theorem nonzero_off_diagonal : ∀ i j, i ≠ j → symmetricM i j ≠ 0 := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [symmetricM]

theorem stationary_diagonal : ∀ i, cycleE i i = 0 := by
  intro i; fin_cases i <;> norm_num [cycleE]

theorem stationary_pairs : ∀ i j,
    cycleE i j * symmetricM j i + symmetricM i j * cycleE j i = 0 := by
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [cycleE, symmetricM]

theorem stationary_cycles : ∀ i j k,
    T027O.cycleDerivative symmetricM cycleE i j k = 0 := by
  intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [T027O.cycleDerivative, cycleE, symmetricM]

theorem genericity_fails :
    symmetricM 0 1 * symmetricM 1 2 * symmetricM 2 0 -
      symmetricM 0 2 * symmetricM 2 1 * symmetricM 1 0 = 0 := by
  norm_num [symmetricM]

theorem not_diagonal_commutator :
    ¬ ∃ h : Fin 3 → ℚ, ∀ i j, cycleE i j = (h i - h j) * symmetricM i j := by
  rintro ⟨h, hh⟩
  have h01 := hh 0 1
  have h12 := hh 1 2
  have h20 := hh 2 0
  norm_num [cycleE, symmetricM] at h01 h12 h20
  linarith

def genericM : Fin 3 → Fin 3 → ℚ := !![0, 1, 1; 2, 0, 1; 1, 3, 0]

theorem generic_witness : ∀ i j k, i ≠ j → j ≠ k → k ≠ i →
    genericM i j * genericM j k * genericM k i -
      genericM i k * genericM k j * genericM j i ≠ 0 := by
  intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [genericM]

def genericE : Fin 3 → Fin 3 → ℚ := !![0, -1, -2; 2, 0, -1; 2, 3, 0]

theorem rigidity_positive_control : ∃ h : Fin 3 → ℚ, ∀ i j,
    genericE i j = (h i - h j) * genericM i j := by
  apply T027O.principal_minor_rigidity 0 genericM genericE
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [genericM]
  · intro i; fin_cases i <;> norm_num [genericE]
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [genericM, genericE]
  · intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [T027O.cycleDerivative, genericM, genericE]
  · exact generic_witness

end T027OControls
