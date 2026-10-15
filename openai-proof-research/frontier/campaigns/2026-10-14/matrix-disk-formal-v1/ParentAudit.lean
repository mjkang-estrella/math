import FiniteVariance
#check @tripleSum_column
#check @bistochastic_variance
#check @variance_deficit_nonneg
#print axioms tripleSum_column
#print axioms bistochastic_variance
#print axioms variance_deficit_nonneg
open Finset
example {I : Type*} [Fintype I] [DecidableEq I] (K : I → I → ℝ) (u : I → ℝ)
  (hr : ∀ i, ∑ j, K i j = 1) (hc : ∀ j, ∑ i, K i j = 1) :
  (∑ j, ∑ i, ∑ k, K i j * K k j * (u i - u k)^2) =
    2 * ((∑ i, u i^2) - ∑ j, (∑ i, K i j * u i)^2) :=
  bistochastic_variance hr hc
example {I : Type*} [Fintype I] [DecidableEq I] (K : I → I → ℝ) (u : I → ℝ)
  (hr : ∀ i, ∑ j, K i j = 1) (hc : ∀ j, ∑ i, K i j = 1)
  (hK : ∀ i j, 0 ≤ K i j) :
  0 ≤ (∑ i, u i^2) - ∑ j, (∑ i, K i j * u i)^2 :=
  variance_deficit_nonneg hr hc hK
