import EndpointAssembly
import Selection
import ConvexWeights

namespace CStarSendov

open scoped ComplexOrder BigOperators

noncomputable abbrev sourceCStarPositiveOrder : StarOrderedRing FunctionAlgebra :=
  inferInstance

theorem source_critical_classification (z : FunctionAlgebra)
    (hz : sourceDeleted z = 0) :
    z = criticalPlusMap ∨ z = criticalMinusMap := by
  apply selection_rigidity_cmap z criticalPlusMap criticalMinusMap
    (fun t => critical_branches_ne t)
  intro t
  apply (pointwise_critical_classification t (z t)).mp
  have ht := congrArg (fun f : FunctionAlgebra => f t) hz
  exact ht

theorem source_critical_ne_roots (z : FunctionAlgebra)
    (hz : sourceDeleted z = 0) (t : Time) (j : Fin 3) : z t ≠ roots j t := by
  have ht : cubicDeleted t (z t) = 0 := congrArg (fun f : FunctionAlgebra => f t) hz
  have hne := critical_ne_roots ht
  fin_cases j
  · exact hne.1
  · exact hne.2.1
  · exact hne.2.2

theorem source_critical_deletedProductDeriv (z : FunctionAlgebra)
    (hz : sourceDeleted z = 0) (t : Time) :
    deletedProductDeriv (fun s : Time => z s) (fun j s => roots j s) t = 0 := by
  have ht : cubicDeleted t (z t) = 0 := congrArg (fun f : FunctionAlgebra => f t) hz
  have h0 : (Finset.univ : Finset (Fin 3)).erase 0 = {1, 2} := by decide
  have h1 : (Finset.univ : Finset (Fin 3)).erase 1 = {0, 2} := by decide
  have h2 : (Finset.univ : Finset (Fin 3)).erase 2 = {0, 1} := by decide
  have hid : deletedProductDeriv (fun s : Time => z s) (fun j s => roots j s) t =
      cubicDeleted t (z t) := by
    simp [deletedProductDeriv, Fin.sum_univ_three, h0, h1, h2,
      cubicDeleted, roots]
    rfl
  exact hid.trans ht

theorem source_critical_strict_real_weights (z : FunctionAlgebra)
    (hz : sourceDeleted z = 0) :
    ∃ w : Fin 3 → C(Time, ℝ),
      (∀ j t, 0 < w j t) ∧ (∀ t, ∑ j, w j t = 1) ∧
      (∀ t, z t = ∑ j, (w j t : ℂ) * roots j t) := by
  obtain ⟨w, hwcont, hwpos, hwsum, hwconv⟩ := exists_convex_weights z.continuous
    (fun j => (roots j).continuous) (source_critical_ne_roots z hz)
    (source_critical_deletedProductDeriv z hz)
  let W : Fin 3 → C(Time, ℝ) := fun j => ⟨w j, hwcont j⟩
  refine ⟨W, fun j t => hwpos t j, hwsum, ?_⟩
  intro t
  have ht := congrFun hwconv t
  simpa [W, Finset.sum_apply] using ht

theorem source_critical_positive_convex (z : FunctionAlgebra)
    (hz : sourceDeleted z = 0) : sourcePositiveConvex roots z := by
  obtain ⟨w, hpos, hsum, hconv⟩ := source_critical_strict_real_weights z hz
  exact source_positive_convex_from_real_weights roots z w
    (fun j t => (hpos j t).le) hsum hconv

theorem source_all_critical_distance_gt (z : FunctionAlgebra)
    (hz : sourceCubicDeleted roots z = 0) : (21 : ℝ) / 20 < ‖roots 0 - z‖ := by
  rcases source_critical_classification z hz with rfl | rfl
  · exact plus_sup_distance_gt
  · exact minus_sup_distance_gt

theorem source_counterexample_353909 : ¬ sourceCubicConjecture353909 :=
  source_refutation353909_of_classification_and_weights source_critical_classification
    (fun k => source_critical_positive_convex (criticals k) (criticals_are_zeros k))

theorem source_counterexample_published_conjecture4 : ¬ sourceSplitCubicConjecture4 :=
  source_refutation_split_of_classification source_critical_classification

theorem source_complete_counterexample :
    sourcePolynomial.Monic ∧ sourcePolynomial.natDegree = 3 ∧
    (∀ j, ‖roots j‖ ≤ (9 : ℝ) / 10) ∧
    (∀ k, ‖criticals k‖ < (9 : ℝ) / 10) ∧
    (∀ k, sourcePositiveConvex roots (criticals k)) ∧
    (∀ t, Function.Injective (fun k : Fin 2 => criticals k t)) ∧
    sourcePolynomial.derivative =
      Polynomial.C 3 * (Polynomial.X - Polynomial.C (criticals 0)) *
        (Polynomial.X - Polynomial.C (criticals 1)) ∧
    (∀ z, sourceCubicDeleted roots z = 0 → (21 : ℝ) / 20 < ‖roots 0 - z‖) ∧
    ¬ sourceCubicConjecture353909 ∧ ¬ sourceSplitCubicConjecture4 := by
  exact ⟨sourcePolynomial_monic, sourcePolynomial_degree, roots_norm_le,
    criticals_norm_lt,
    fun k => source_critical_positive_convex (criticals k) (criticals_are_zeros k),
    criticals_pointwise_injective, sourcePolynomial_derivative_split,
    source_all_critical_distance_gt, source_counterexample_353909,
    source_counterexample_published_conjecture4⟩

end CStarSendov
