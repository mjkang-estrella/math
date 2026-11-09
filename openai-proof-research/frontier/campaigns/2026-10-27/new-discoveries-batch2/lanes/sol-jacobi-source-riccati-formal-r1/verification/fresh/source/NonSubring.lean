import Riccati
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option warningAsError true

noncomputable section
namespace JacobiShifted.BinaryFiltration

/-- An integral-ring negative control: `a` and `b` are weighted, while `ab` is not. -/
theorem filtration_not_subring :
    Weighted (MvPolynomial.X (0 : Fin 2) : P ℤ) ∧
    Weighted (MvPolynomial.X (1 : Fin 2) : P ℤ) ∧
    ¬ Weighted (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) : P ℤ) := by
  constructor
  · simpa [initial, MvPolynomial.X] using weighted_initial (1 : ℤ) 0
  constructor
  · simpa [initial, MvPolynomial.X] using weighted_initial (0 : ℤ) 1
  intro hw
  have hne : bidegree 1 1 ≠ 0 := by
    intro he
    have := congrArg (fun α : Exponent => α 0) he
    simp at this
  have hd := hw.2 (bidegree 1 1) hne
  have he : (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) : P ℤ) =
      MvPolynomial.monomial (bidegree 1 1) 1 := by
    simp [MvPolynomial.X, bidegree, MvPolynomial.monomial_mul_monomial]
  rw [he] at hd
  norm_num [MvPolynomial.coeff_monomial, weight] at hd

end JacobiShifted.BinaryFiltration
