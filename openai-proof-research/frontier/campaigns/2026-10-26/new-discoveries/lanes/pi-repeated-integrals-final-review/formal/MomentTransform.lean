import MomentDefs

set_option maxRecDepth 4000

open MeasureTheory Set
open scoped BigOperators

namespace RepeatedIntegrals

noncomputable section

def kernelMomentMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun r i => (r.val.choose i.val : ℝ) * (-1) ^ i.val / (r.val.factorial : ℝ)

theorem kernelMomentMatrix_lower (n : ℕ) : (kernelMomentMatrix n).IsLowerTriangular := by
  intro i j hij
  have h : i.val < j.val := hij
  simp [kernelMomentMatrix, Nat.choose_eq_zero_of_lt h]

theorem kernelMomentMatrix_det_ne_zero (n : ℕ) : (kernelMomentMatrix n).det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular _ (kernelMomentMatrix_lower n)]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  simp [kernelMomentMatrix, Nat.factorial_ne_zero]

def kernelMomentEquiv (n : ℕ) : MomentSpace n ≃L[ℝ] MomentSpace n :=
  (LinearEquiv.ofBijective (kernelMomentMatrix n).mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr
          (isUnit_iff_ne_zero.mpr (kernelMomentMatrix_det_ne_zero n))),
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr
          (isUnit_iff_ne_zero.mpr (kernelMomentMatrix_det_ne_zero n)))⟩).toContinuousLinearEquiv

def endpointMomentTransform (n : ℕ) : MomentSpace n ≃L[ℝ] MomentSpace n :=
  (kernelMomentEquiv n).trans
    (LinearEquiv.funCongrLeft ℝ ℝ (Fin.revPerm : Equiv.Perm (Fin (n + 1)))).toContinuousLinearEquiv

theorem endpointMomentTransform_apply (n : ℕ) (y : MomentSpace n) (j : Fin (n + 1)) :
    endpointMomentTransform n y j =
      ∑ i : Fin (n + 1),
        ((n - j.val).choose i.val : ℝ) * (-1) ^ i.val / ((n - j.val).factorial : ℝ) * y i := by
  change (kernelMomentMatrix n).mulVec y j.rev = _
  simp [Matrix.mulVec, dotProduct, kernelMomentMatrix, Fin.rev]

theorem finite_binomial_kernel (n k : ℕ) (hk : k ≤ n) (t : ℝ) :
    (∑ i : Fin (n + 1), (k.choose i.val : ℝ) * (-1) ^ i.val * t ^ i.val) =
      (1 - t) ^ k := by
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => (k.choose i : ℝ) * (-1) ^ i * t ^ i) (n + 1)]
  have hs : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (-1) ^ i * t ^ i) =
      ∑ i ∈ Finset.range (n + 1), (k.choose i : ℝ) * (-1) ^ i * t ^ i := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro i hi hki
    have hik : k < i := by simp only [Finset.mem_range] at hi hki; omega
    simp [Nat.choose_eq_zero_of_lt hik]
  rw [← hs]
  have hb := add_pow (-t) (1 : ℝ) k
  simp only [one_pow, mul_one] at hb
  rw [show -t + (1 : ℝ) = 1 - t by ring] at hb
  rw [hb]
  apply Finset.sum_congr rfl
  intro i _
  rw [neg_pow]
  ring

theorem endpointMomentTransform_density (n : ℕ) {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (j : Fin (n + 1)) :
    endpointMomentTransform n (densityMoments n ρ) j =
      (∫ t in (0 : ℝ)..1, (1 - t) ^ (n - j.val) * ρ t) /
        ((n - j.val).factorial : ℝ) := by
  rw [endpointMomentTransform_apply]
  simp only [densityMoments]
  have hi (i : Fin (n + 1)) : IntervalIntegrable (fun t : ℝ =>
      (((n - j.val).choose i.val : ℝ) * (-1) ^ i.val /
        ((n - j.val).factorial : ℝ)) * (t ^ i.val * ρ t)) volume 0 1 :=
    (continuous_const.mul ((continuous_id.pow _).mul hρ)).intervalIntegrable _ _
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro t _
  change (∑ i : Fin (n + 1),
    ((n - j.val).choose i.val : ℝ) * (-1) ^ i.val /
      ((n - j.val).factorial : ℝ) * (t ^ i.val * ρ t)) =
    (1 - t) ^ (n - j.val) * ρ t / ((n - j.val).factorial : ℝ)
  rw [← finite_binomial_kernel n (n - j.val) (Nat.sub_le _ _) t]
  rw [Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

end

end RepeatedIntegrals
