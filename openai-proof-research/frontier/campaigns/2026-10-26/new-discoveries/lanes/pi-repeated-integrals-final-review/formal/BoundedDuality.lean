import MomentDuality
import TestBumps

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace RepeatedIntegrals

noncomputable section

theorem bounded_smooth_pairing_nonpos {n : ℕ} (a : MomentSpace n) (C : ℝ)
    (hb : ∀ y ∈ smoothMomentSet n, momentPairing a y ≤ C) :
    ∀ t ∈ Icc (0 : ℝ) 1, momentPairing a (momentCurve n t) ≤ 0 := by
  let p := fun t : ℝ => (momentPolynomial a).eval t
  have hp : Continuous p := by
    dsimp [p]
    fun_prop
  have hIoo : Ioo (0 : ℝ) 1 ⊆ {t | p t ≤ 0} := by
    intro t ht
    change p t ≤ 0
    by_contra! hpt
    obtain ⟨ψ, hψ, hn, h0, h1, hI⟩ := exists_positive_test_bump hp ht hpt
    let I := ∫ x in (0 : ℝ)..1, p x * ψ x
    let s := ∫ x in (0 : ℝ)..1, p x
    have hs : s ≤ C := by
      have h := hb (densityMoments n (fun _ => 1))
        ⟨fun _ => 1, goodDensity_one, rfl⟩
      rw [momentPairing_density a continuous_const] at h
      simpa only [mul_one] using h
    let c := (C - s + 1) / I
    have hc : 0 ≤ c := div_nonneg (by linarith) hI.le
    have hd := goodDensity_add_nonnegative_test goodDensity_one hψ hn h0 h1 hc
    have h := hb (densityMoments n (fun x => 1 + c * ψ x))
      ⟨fun x => 1 + c * ψ x, hd, rfl⟩
    have hcont : Continuous (fun x : ℝ => 1 + c * ψ x) := by fun_prop
    rw [momentPairing_density a hcont] at h
    have he : (∫ x in (0 : ℝ)..1, p x * (1 + c * ψ x)) = s + c * I := by
      calc
        (∫ x in (0 : ℝ)..1, p x * (1 + c * ψ x)) =
            ∫ x in (0 : ℝ)..1, p x + c * (p x * ψ x) := by
          apply intervalIntegral.integral_congr
          intro x _
          change p x * (1 + c * ψ x) = p x + c * (p x * ψ x)
          ring
        _ = s + c * I := by
          have hi : IntervalIntegrable (fun x : ℝ => p x * ψ x) volume 0 1 :=
            (hp.mul hψ.continuous).intervalIntegrable _ _
          rw [intervalIntegral.integral_add (hp.intervalIntegrable _ _)
            (hi.const_mul c),
            intervalIntegral.integral_const_mul]
    change (∫ x in (0 : ℝ)..1, p x * (1 + c * ψ x)) ≤ C at h
    rw [he] at h
    have hci : c * I = C - s + 1 := div_mul_cancel₀ _ hI.ne'
    linarith
  have hcl := closure_minimal hIoo (isClosed_le hp continuous_const)
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hcl
  intro t ht
  rw [← momentPolynomial_eval]
  exact hcl ht

theorem bounded_functional_nonpos {n : ℕ} (L : MomentSpace n →L[ℝ] ℝ) (C : ℝ)
    (hb : ∀ y ∈ smoothMomentSet n, L y ≤ C) :
    ∀ t ∈ Icc (0 : ℝ) 1, L (momentCurve n t) ≤ 0 := by
  intro t ht
  rw [dualCoefficients_pairing]
  exact bounded_smooth_pairing_nonpos (dualCoefficients L) C
    (fun y hy => by rw [← dualCoefficients_pairing]; exact hb y hy) t ht

theorem zero_le_bound_of_smooth_functional {n : ℕ} (L : MomentSpace n →L[ℝ] ℝ) (C : ℝ)
    (hb : ∀ y ∈ smoothMomentSet n, L y ≤ C) : 0 ≤ C := by
  have hcl := closure_minimal (t := {y | L y ≤ C}) hb
    (isClosed_le L.continuous continuous_const)
  have hz := hcl (zero_mem_closure_smoothMomentSet n)
  simpa using hz

end

end RepeatedIntegrals
