import FunctionAlgebra

namespace CStarSendov

open scoped ComplexOrder BigOperators
open Polynomial

noncomputable abbrev sourceCStarStructure : CommCStarAlgebra FunctionAlgebra := inferInstance

noncomputable def sourceCubicDeleted (a : Fin 3 → FunctionAlgebra) (z : FunctionAlgebra) :
    FunctionAlgebra :=
  (z - a 1) * (z - a 2) + (z - a 0) * (z - a 2) + (z - a 0) * (z - a 1)

noncomputable def sourceCubicPolynomial (a : Fin 3 → FunctionAlgebra) :
    Polynomial FunctionAlgebra :=
  (X - C (a 0)) * (X - C (a 1)) * (X - C (a 2))

def sourcePositiveConvex (a : Fin 3 → FunctionAlgebra) (b : FunctionAlgebra) : Prop :=
  ∃ w : Fin 3 → FunctionAlgebra,
    (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧ b = ∑ j, w j * a j

def sourceCubicConjecture353909 : Prop :=
  ∀ (a : Fin 3 → FunctionAlgebra),
    (∀ j, sourceClosedDisc 0 1 (a j)) →
    ∀ (b : Fin 2 → FunctionAlgebra),
      (∀ k, sourceCubicDeleted a (b k) = 0) →
      (∀ k, sourceClosedDisc 0 1 (b k)) →
      (∀ k, sourcePositiveConvex a (b k)) →
      ∀ j, ∃ z : FunctionAlgebra,
        sourceCubicDeleted a z = 0 ∧ sourceClosedDisc (a j) 1 z

def sourceSplitCubicConjecture4 : Prop :=
  ∀ (a : Fin 3 → FunctionAlgebra),
    (∀ j, sourceClosedDisc 0 1 (a j)) →
    ∀ (b : Fin 2 → FunctionAlgebra),
      (sourceCubicPolynomial a).derivative =
        C 3 * (X - C (b 0)) * (X - C (b 1)) →
      ∀ j, ∃ z : FunctionAlgebra,
        sourceCubicDeleted a z = 0 ∧ sourceClosedDisc (a j) 1 z

theorem sourceCubicPolynomial_monic (a : Fin 3 → FunctionAlgebra) :
    (sourceCubicPolynomial a).Monic := by
  exact ((monic_X_sub_C _).mul (monic_X_sub_C _)).mul (monic_X_sub_C _)

theorem sourceCubicPolynomial_degree (a : Fin 3 → FunctionAlgebra) :
    (sourceCubicPolynomial a).natDegree = 3 := by
  unfold sourceCubicPolynomial
  rw [((monic_X_sub_C _).mul (monic_X_sub_C _)).natDegree_mul (monic_X_sub_C _),
    (monic_X_sub_C _).natDegree_mul (monic_X_sub_C _)]
  simp

theorem sourceCubicDeleted_derivative (a : Fin 3 → FunctionAlgebra) (z : FunctionAlgebra) :
    (sourceCubicPolynomial a).derivative.eval z = sourceCubicDeleted a z := by
  simp [sourceCubicPolynomial, sourceCubicDeleted, derivative_mul]
  ring

theorem sourceCubicDeleted_roots (z : FunctionAlgebra) :
    sourceCubicDeleted roots z = sourceDeleted z := rfl

theorem sourceCubicPolynomial_roots : sourceCubicPolynomial roots = sourcePolynomial := rfl

theorem source_roots_in_exact_disc (j : Fin 3) : sourceClosedDisc 0 1 (roots j) :=
  (sourceUnitDisc_eq_radius_one _ _).mp (roots_in_source_disc j)

theorem source_criticals_in_exact_disc (k : Fin 2) : sourceClosedDisc 0 1 (criticals k) :=
  (sourceUnitDisc_eq_radius_one _ _).mp (criticals_in_source_disc k)

theorem source_criticals_deleted (k : Fin 2) : sourceCubicDeleted roots (criticals k) = 0 :=
  criticals_are_zeros k

theorem source_criticals_complete_split :
    (sourceCubicPolynomial roots).derivative =
      C 3 * (X - C (criticals 0)) * (X - C (criticals 1)) :=
  sourcePolynomial_derivative_split

theorem source_positive_convex_from_real_weights
    (a : Fin 3 → FunctionAlgebra) (b : FunctionAlgebra)
    (w : Fin 3 → C(Time, ℝ))
    (hpos : ∀ j t, 0 ≤ w j t)
    (hsum : ∀ t, ∑ j, w j t = 1)
    (hconv : ∀ t, b t = ∑ j, (w j t : ℂ) * a j t) :
    sourcePositiveConvex a b := by
  let W : Fin 3 → FunctionAlgebra := fun j =>
    ⟨fun t => (w j t : ℂ), Complex.continuous_ofReal.comp (w j).continuous⟩
  refine ⟨W, ?_, ?_, ?_⟩
  · intro j
    apply ContinuousMap.le_def.mpr
    intro t
    exact Complex.zero_le_real.mpr (hpos j t)
  · apply ContinuousMap.ext
    intro t
    change (∑ j, W j) t = (1 : ℂ)
    simp only [ContinuousMap.sum_apply]
    change (∑ j, (w j t : ℂ)) = (1 : ℂ)
    rw [← Complex.ofReal_sum, hsum t]
    rfl
  · apply ContinuousMap.ext
    intro t
    change b t = (∑ j, W j * a j) t
    simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply]
    exact hconv t

end CStarSendov
