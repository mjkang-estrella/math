import SourceStatement

namespace CStarSendov

open scoped ComplexOrder BigOperators

theorem source_root_zero_obstruction_of_classification
    (hclass : ∀ z : FunctionAlgebra, sourceDeleted z = 0 →
      z = criticalPlusMap ∨ z = criticalMinusMap) :
    ¬ ∃ z : FunctionAlgebra,
      sourceCubicDeleted roots z = 0 ∧ sourceClosedDisc (roots 0) 1 z := by
  rintro ⟨z, hz, hdisc⟩
  have hu : sourceUnitDisc (roots 0) z :=
    (sourceUnitDisc_eq_radius_one _ _).mpr hdisc
  rcases hclass z hz with rfl | rfl
  · exact plus_fails_source_disc hu
  · exact minus_fails_source_disc hu

theorem source_refutation353909_of_classification_and_weights
    (hclass : ∀ z : FunctionAlgebra, sourceDeleted z = 0 →
      z = criticalPlusMap ∨ z = criticalMinusMap)
    (hconv : ∀ k, sourcePositiveConvex roots (criticals k)) :
    ¬ sourceCubicConjecture353909 := by
  intro h
  exact source_root_zero_obstruction_of_classification hclass
    (h roots source_roots_in_exact_disc criticals source_criticals_deleted
      source_criticals_in_exact_disc hconv 0)

theorem source_refutation_split_of_classification
    (hclass : ∀ z : FunctionAlgebra, sourceDeleted z = 0 →
      z = criticalPlusMap ∨ z = criticalMinusMap) :
    ¬ sourceSplitCubicConjecture4 := by
  intro h
  exact source_root_zero_obstruction_of_classification hclass
    (h roots source_roots_in_exact_disc criticals source_criticals_complete_split 0)

end CStarSendov
