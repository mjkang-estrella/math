import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Tactic

noncomputable section
open MvPolynomial
open scoped BigOperators

namespace MultiplicativeBasisObstruction

theorem no_polynomial_parametrization
    {I P K : Type} [Fintype I] [Fintype P] [Field K] [Algebra ℚ K]
    (hcard : Fintype.card P < Fintype.card I)
    (t : I → K) (ht : AlgebraicIndependent ℚ t)
    (s : P → K) (f : I → MvPolynomial P ℚ) :
    ¬ (∀ i, aeval s (f i) = t i) := by
  intro he
  have hc : AlgebraicIndependent ℚ ((aeval s) ∘ f) := by
    simpa only [Function.comp_def, he] using ht
  have hf : AlgebraicIndependent ℚ f := hc.of_comp (aeval s)
  have h := hf.cardinalMk_le_trdeg
  rw [MvPolynomial.trdeg_of_isDomain] at h
  have hle : Fintype.card I ≤ Fintype.card P := by simpa using h
  exact (Nat.not_le_of_lt hcard) hle

abbrev Edge (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}
abbrev CoefficientIndex := Fin 4 × Edge 8
abbrev ParameterIndex := (Fin 8 × Fin 8) ⊕ ((Fin 4 × Fin 4) ⊕ Edge 8)

theorem parameter_card : Fintype.card ParameterIndex = 108 := by decide
theorem coefficient_card : Fintype.card CoefficientIndex = 112 := by decide

def chart (δ : Edge 8 → Fin 4) (o : CoefficientIndex) :
    MvPolynomial ParameterIndex ℚ :=
  ∑ e : Edge 8,
    X (.inr (.inl (o.1, δ e))) * X (.inr (.inr e)) *
      (X (.inl (e.val.1, o.2.val.1)) * X (.inl (e.val.2, o.2.val.2)) -
       X (.inl (e.val.2, o.2.val.1)) * X (.inl (e.val.1, o.2.val.2)))

theorem chart_evaluation {K : Type} [Field K] [Algebra ℚ K]
    (δ : Edge 8 → Fin 4) (s : ParameterIndex → K) (o : CoefficientIndex) :
    aeval s (chart δ o) =
      ∑ e : Edge 8,
        s (.inr (.inl (o.1, δ e))) * s (.inr (.inr e)) *
          (s (.inl (e.val.1, o.2.val.1)) * s (.inl (e.val.2, o.2.val.2)) -
           s (.inl (e.val.2, o.2.val.1)) * s (.inl (e.val.1, o.2.val.2))) := by
  simp [chart]

theorem generic_coefficients_not_in_any_chart
    {K : Type} [Field K] [Algebra ℚ K]
    (t : CoefficientIndex → K) (ht : AlgebraicIndependent ℚ t) :
    ¬ ∃ (δ : Edge 8 → Fin 4) (s : ParameterIndex → K),
      ∀ o, aeval s (chart δ o) = t o := by
  rintro ⟨δ, s, hs⟩
  exact no_polynomial_parametrization
    (by rw [parameter_card, coefficient_card]; omega) t ht s (chart δ) hs

end MultiplicativeBasisObstruction
