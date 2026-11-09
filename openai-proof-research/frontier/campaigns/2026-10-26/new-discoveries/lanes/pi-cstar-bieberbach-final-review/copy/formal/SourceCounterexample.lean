import FunctionMap

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace CStarBieberbach

open scoped ComplexOrder

abbrev sourceCStarStructure : CommCStarAlgebra FunctionAlgebra := inferInstance

def SourceClaim : Prop :=
  ∀ (a : ℕ → FunctionAlgebra) (F : FunctionAlgebra → FunctionAlgebra),
    (∀ u, ‖u‖ < 1 → HasSum (fun n => a (n + 2) * u ^ (n + 2)) (F u - u)) →
    Set.InjOn F {u | ‖u‖ < 1} →
    ∀ n : ℕ, 2 ≤ n →
      a n * star (a n) ≤ (n : FunctionAlgebra) ^ 2 ∧
      star (a n) * a n ≤ (n : FunctionAlgebra) ^ 2

theorem coefficient_two_at_one : coefficient parameter 2 timeOne = 4 := by
  norm_num [coefficient, parameter, timeOne]

theorem coefficient_two_order_failure :
    ¬coefficient parameter 2 * star (coefficient parameter 2) ≤
      (2 : FunctionAlgebra) ^ 2 := by
  intro h
  have ht := ContinuousMap.le_def.mp h timeOne
  change coefficient parameter 2 timeOne * star (coefficient parameter 2 timeOne) ≤
    (2 : ℂ) ^ 2 at ht
  rw [coefficient_two_at_one] at ht
  norm_num [Complex.le_def] at ht

theorem source_counterexample : ¬SourceClaim := by
  intro h
  have hs : ∀ u : FunctionAlgebra, ‖u‖ < 1 →
      HasSum (fun n => coefficient parameter (n + 2) * u ^ (n + 2)) (witnessMap u - u) := by
    intro u _
    exact source_series_hasSum parameter u
  have hc := h (coefficient parameter) witnessMap hs witnessMap_injective.injOn 2 (by norm_num)
  exact coefficient_two_order_failure hc.1

def SourceStrongClaim : Prop :=
  ∀ (a : ℕ → FunctionAlgebra) (F : FunctionAlgebra → FunctionAlgebra),
    (∀ u, ‖u‖ < 1 → HasSum (fun n => a (n + 2) * u ^ (n + 2)) (F u - u)) →
    (∀ u, ‖u‖ < 1 → Summable (fun n : ℕ => (n + 2 : ℂ) • (a (n + 2) * u ^ (n + 1)))) →
    Set.InjOn F {u | ‖u‖ < 1} →
    ∀ n : ℕ, 2 ≤ n →
      a n * star (a n) ≤ (n : FunctionAlgebra) ^ 2 ∧
      star (a n) * a n ≤ (n : FunctionAlgebra) ^ 2

theorem source_strong_counterexample : ¬SourceStrongClaim := by
  intro h
  have hs : ∀ u : FunctionAlgebra, ‖u‖ < 1 →
      HasSum (fun n => coefficient parameter (n + 2) * u ^ (n + 2)) (witnessMap u - u) := by
    intro u _
    exact source_series_hasSum parameter u
  have hd : ∀ u : FunctionAlgebra, ‖u‖ < 1 →
      Summable (fun n : ℕ => (n + 2 : ℂ) • (coefficient parameter (n + 2) * u ^ (n + 1))) := by
    intro u _
    exact derivative_series_summable parameter u
  have hc := h (coefficient parameter) witnessMap hs hd witnessMap_injective.injOn 2 (by norm_num)
  exact coefficient_two_order_failure hc.1

end CStarBieberbach
