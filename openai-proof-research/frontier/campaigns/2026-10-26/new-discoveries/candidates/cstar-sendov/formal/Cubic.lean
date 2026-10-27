import Analytic

namespace CStarSendov

noncomputable def cubicValue (t : ℝ) (z : ℂ) : ℂ :=
  (z-rootOne t)*(z-rootPlus t)*(z-rootMinus t)

noncomputable def cubicDeleted (t : ℝ) (z : ℂ) : ℂ :=
  (z-rootPlus t)*(z-rootMinus t) + (z-rootOne t)*(z-rootMinus t) +
    (z-rootOne t)*(z-rootPlus t)

theorem cubicDeleted_formula (t : ℝ) (z : ℂ) :
    cubicDeleted t z = 3*z^2 - (9/5:ℂ)*z - (729/1600:ℂ)*phase t^2 := by
  unfold cubicDeleted rootOne rootPlus rootMinus
  ring

theorem cubicDeleted_factorization (t : ℝ) (z : ℂ) :
    cubicDeleted t z = 3*(z-criticalPlus t)*(z-criticalMinus t) := by
  rw [cubicDeleted_formula]
  unfold criticalPlus criticalMinus
  linear_combination (27/100:ℂ)*(branch_squared t)

theorem criticalPlus_zero (t : ℝ) : cubicDeleted t (criticalPlus t) = 0 := by
  rw [cubicDeleted_factorization]
  ring

theorem criticalMinus_zero (t : ℝ) : cubicDeleted t (criticalMinus t) = 0 := by
  rw [cubicDeleted_factorization]
  ring

theorem pointwise_critical_classification (t : ℝ) (z : ℂ) :
    cubicDeleted t z = 0 ↔ z = criticalPlus t ∨ z = criticalMinus t := by
  rw [cubicDeleted_factorization]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · have hz : z-criticalPlus t=0 := (mul_eq_zero.mp h).resolve_left (by norm_num)
      exact Or.inl (sub_eq_zero.mp hz)
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (rfl | rfl) <;> ring

theorem rootPlus_ne_rootOne (t : ℝ) : rootPlus t ≠ rootOne t := by
  intro h
  have hn := congrArg norm h
  rw [rootPlus_norm, rootOne_norm] at hn
  norm_num at hn

theorem rootMinus_ne_rootOne (t : ℝ) : rootMinus t ≠ rootOne t := by
  intro h
  have hn := congrArg norm h
  rw [rootMinus_norm, rootOne_norm] at hn
  norm_num at hn

theorem rootPlus_ne_rootMinus (t : ℝ) : rootPlus t ≠ rootMinus t := by
  intro h
  have hz : phase t = 0 := by
    unfold rootPlus rootMinus at h
    linear_combination (20/27:ℂ)*h
  exact phase_ne_zero t hz

theorem deleted_at_rootOne (t : ℝ) :
    cubicDeleted t (rootOne t) = (rootOne t-rootPlus t)*(rootOne t-rootMinus t) := by
  unfold cubicDeleted
  ring

theorem deleted_at_rootPlus (t : ℝ) :
    cubicDeleted t (rootPlus t) = (rootPlus t-rootOne t)*(rootPlus t-rootMinus t) := by
  unfold cubicDeleted
  ring

theorem deleted_at_rootMinus (t : ℝ) :
    cubicDeleted t (rootMinus t) = (rootMinus t-rootOne t)*(rootMinus t-rootPlus t) := by
  unfold cubicDeleted
  ring

theorem critical_ne_roots {t : ℝ} {z : ℂ} (hz : cubicDeleted t z = 0) :
    z ≠ rootOne t ∧ z ≠ rootPlus t ∧ z ≠ rootMinus t := by
  refine ⟨?_, ?_, ?_⟩
  · intro he
    rw [he, deleted_at_rootOne] at hz
    exact (mul_ne_zero (sub_ne_zero.mpr (rootPlus_ne_rootOne t).symm)
      (sub_ne_zero.mpr (rootMinus_ne_rootOne t).symm)) hz
  · intro he
    rw [he, deleted_at_rootPlus] at hz
    exact (mul_ne_zero (sub_ne_zero.mpr (rootPlus_ne_rootOne t))
      (sub_ne_zero.mpr (rootPlus_ne_rootMinus t))) hz
  · intro he
    rw [he, deleted_at_rootMinus] at hz
    exact (mul_ne_zero (sub_ne_zero.mpr (rootMinus_ne_rootOne t))
      (sub_ne_zero.mpr (rootPlus_ne_rootMinus t).symm)) hz

theorem scalar_polynomial_split (t : ℝ) :
    ((Polynomial.X - Polynomial.C (rootOne t)) *
      (Polynomial.X - Polynomial.C (rootPlus t)) *
      (Polynomial.X - Polynomial.C (rootMinus t))).derivative =
      Polynomial.C 3 * (Polynomial.X - Polynomial.C (criticalPlus t)) *
        (Polynomial.X - Polynomial.C (criticalMinus t)) := by
  apply Polynomial.funext
  intro z
  simpa [Polynomial.derivative_mul, cubicDeleted, add_mul] using
    cubicDeleted_factorization t z

end CStarSendov
