import BergmanPolynomial
import BergmanSOS
import BergmanRootAllocation

namespace BergmanUnitCircle

theorem polynomialQ_unitcircle_nonzero {m n : ℕ} (hn : 0 < n) (hmn : n < m)
    (hcop : Nat.Coprime m n) {z : ℂ} (hz : ‖z‖=1) : (polynomialQ m n).eval z ≠ 0 := by
  have hnz : z ≠ 0 := by intro he; simp [he] at hz
  rw [polynomialQ_eval_source hn hmn hnz]
  exact source_conjecture_368572 hn hmn hcop hz

theorem source_root_allocation {m n : ℕ} (hn : 0 < n) (hmn : n < m)
    (hcop : Nat.Coprime m n) :
    ((polynomialQ m n).roots.filter (fun z => z ≠ 0 ∧ ‖z‖ < 1)).card=m-n := by
  exact BergmanRootAllocation.reciprocal_root_allocation (polynomialQ m n) (m-n)
    (polynomialQ_degree hn hmn) (polynomialQ_reverse hn hmn)
    (polynomialQ_constant_ne_zero hn hmn)
    (fun _ hz => polynomialQ_unitcircle_nonzero hn hmn hcop hz)

/-- Both the unit-circle and multiplicity-count assertions of source Conjecture4.20. -/
theorem source_full_conjecture_368572 {m n : ℕ} (hn : 0 < n) (hmn : n < m)
    (hcop : Nat.Coprime m n) :
    (∀ z : ℂ, ‖z‖=1 → (polynomialQ m n).eval z ≠ 0) ∧
      ((polynomialQ m n).roots.filter (fun z => z ≠ 0 ∧ ‖z‖ < 1)).card=m-n :=
  ⟨fun _ hz => polynomialQ_unitcircle_nonzero hn hmn hcop hz,
    source_root_allocation hn hmn hcop⟩

end BergmanUnitCircle
