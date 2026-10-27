import BoundedDuality

open MeasureTheory Set
open scoped BigOperators

namespace RepeatedIntegrals

noncomputable section

theorem atomless_measure_mem_smoothMomentSet {n : ℕ}
    (hc : Convex ℝ (smoothMomentSet n)) (ho : IsOpen (smoothMomentSet n))
    {μ : Measure ℝ} [IsFiniteMeasure μ] [NullSingletonClass μ]
    (hs : μ (Icc (0 : ℝ) 1)ᶜ = 0) (hm : 0 < μ.real univ) :
    measureMoments n μ ∈ smoothMomentSet n := by
  classical
  by_contra hy
  obtain ⟨L, hL⟩ := geometric_hahn_banach_open_point hc ho hy
  let y := measureMoments n μ
  have hb : ∀ z ∈ smoothMomentSet n, L z ≤ L y := fun z hz => (hL z hz).le
  have hzero := zero_le_bound_of_smooth_functional L (L y) hb
  have hcurve := bounded_functional_nonpos L (L y) hb
  have hne : -dualCoefficients L ≠ 0 := by
    intro h
    have hcoef : dualCoefficients L = 0 := neg_eq_zero.mp h
    have hLzero (z : MomentSpace n) : L z = 0 := by
      rw [dualCoefficients_pairing, hcoef]
      simp [momentPairing]
    obtain ⟨z, hz⟩ := smoothMomentSet_nonempty n
    have hlt := hL z hz
    rw [hLzero z, hLzero y] at hlt
    exact lt_irrefl _ hlt
  have hp := atomless_moment_strict_positive (-dualCoefficients L) hne hs hm
    (fun t ht => by
      have h := hcurve t ht
      rw [dualCoefficients_pairing] at h
      simpa only [momentPairing, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib,
        neg_nonneg] using h)
  have hpair : momentPairing (-dualCoefficients L) y = -L y := by
    rw [dualCoefficients_pairing]
    simp [momentPairing]
  change 0 < momentPairing (-dualCoefficients L) y at hp
  rw [hpair] at hp
  linarith

end

end RepeatedIntegrals
