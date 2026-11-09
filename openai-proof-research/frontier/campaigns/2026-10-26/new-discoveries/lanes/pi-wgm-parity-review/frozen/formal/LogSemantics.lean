import FlowExistence

open scoped BigOperators

namespace WGMParity

theorem exp_potential_feasible {L I : Type*} (child : I × Bool → L ⊕ I)
    (u : L ⊕ I → ℝ)
    (hu : ∀ i, 2 * u (Sum.inr i) = u (child (i, false)) + u (child (i, true))) :
    CircuitFeasible child (fun v => Real.exp (u v)) := by
  intro i
  have he := congrArg Real.exp (hu i)
  rw [Real.exp_add] at he
  have hp : Real.exp (2 * u (Sum.inr i)) = Real.exp (u (Sum.inr i)) ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, Real.exp_nat_mul]
  rw [hp] at he
  exact he.le

theorem circuitSound_log_le {L I : Type*} [Fintype L]
    (s : L → ℕ) (root : I) (child : I × Bool → L ⊕ I)
    (h : CircuitSound s root child) (u : L ⊕ I → ℝ)
    (hu : ∀ i, 2 * u (Sum.inr i) = u (child (i, false)) + u (child (i, true))) :
    (∑ j, s j : ℕ) * u (Sum.inr root) ≤ ∑ j, (s j : ℝ) * u (Sum.inl j) := by
  have hh := h (fun v => Real.exp (u v)) (fun _ => (Real.exp_pos _).le)
    (exp_potential_feasible child u hu)
  simp only [← Real.exp_nat_mul, ← Real.exp_sum] at hh
  exact Real.exp_le_exp.mp hh

theorem circuitSound_log_equalities {L I : Type*} [Fintype L]
    (s : L → ℕ) (root : I) (child : I × Bool → L ⊕ I)
    (h : CircuitSound s root child) (u : L ⊕ I → ℝ)
    (hu : ∀ i, 2 * u (Sum.inr i) = u (child (i, false)) + u (child (i, true))) :
    (∑ j, s j : ℕ) * u (Sum.inr root) = ∑ j, (s j : ℝ) * u (Sum.inl j) := by
  apply le_antisymm (circuitSound_log_le s root child h u hu)
  have hn : ∀ i, 2 * (-u (Sum.inr i)) = -u (child (i, false)) + -u (child (i, true)) := by
    intro i
    have := hu i
    linarith
  have hh := circuitSound_log_le s root child h (fun v => -u v) hn
  simp only [mul_neg, Finset.sum_neg_distrib] at hh
  linarith

end WGMParity
