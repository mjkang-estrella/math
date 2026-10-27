import FullMinors
import Sharpness

namespace PermanentalThree

theorem source_universal_bounds {A : Mat3} (hA : AllMinorsPositive A) :
    (2:ℝ)/3 < sourceRatio A ∧ sourceRatio A < (9:ℝ)/8 := by
  rw [← ratio_eq_sourceRatio]
  exact source_universal_strict_bounds ((strictTP3_iff_allMinors A).mpr hA)

theorem source_lower_approach {c : ℝ} (hc : (2:ℝ)/3 < c) :
    ∃ A : Mat3, AllMinorsPositive A ∧ sourceRatio A < c := by
  obtain ⟨A, hA, hR⟩ := lower_approach hc
  refine ⟨A, (strictTP3_iff_allMinors A).mp hA, ?_⟩
  rwa [← ratio_eq_sourceRatio]

theorem source_upper_approach {c : ℝ} (hc : c < (9:ℝ)/8) :
    ∃ A : Mat3, AllMinorsPositive A ∧ c < sourceRatio A := by
  obtain ⟨A, hA, hR⟩ := upper_approach hc
  refine ⟨A, (strictTP3_iff_allMinors A).mp hA, ?_⟩
  rwa [← ratio_eq_sourceRatio]

theorem source_lower_constant_iff (c : ℝ) :
    (∀ A : Mat3, AllMinorsPositive A → c ≤ sourceRatio A) ↔ c ≤ (2:ℝ)/3 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨A, hA, hR⟩ := source_lower_approach (lt_of_not_ge hn)
    exact (not_lt_of_ge (h A hA)) hR
  · intro hc A hA
    exact hc.trans (source_universal_bounds hA).1.le

theorem source_upper_constant_iff (c : ℝ) :
    (∀ A : Mat3, AllMinorsPositive A → sourceRatio A ≤ c) ↔ (9:ℝ)/8 ≤ c := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨A, hA, hR⟩ := source_upper_approach (lt_of_not_ge hn)
    exact (not_lt_of_ge (h A hA)) hR
  · intro hc A hA
    exact (source_universal_bounds hA).2.le.trans hc

/-- Full source ratio, all minors, strict bounds and optimal constants in one endpoint. -/
theorem source_sharp_permanental_bounds :
    (∀ A : Mat3, AllMinorsPositive A →
      (2:ℝ)/3 < sourceRatio A ∧ sourceRatio A < (9:ℝ)/8) ∧
    (∀ c : ℝ, (∀ A : Mat3, AllMinorsPositive A → c ≤ sourceRatio A) ↔ c ≤ (2:ℝ)/3) ∧
    (∀ c : ℝ, (∀ A : Mat3, AllMinorsPositive A → sourceRatio A ≤ c) ↔ (9:ℝ)/8 ≤ c) :=
  ⟨fun _ hA => source_universal_bounds hA,
    source_lower_constant_iff, source_upper_constant_iff⟩

end PermanentalThree
