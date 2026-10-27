import SpectralMoments

open Finset
open scoped RealInnerProductSpace
namespace FlatBernoulli
section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem negative_eigenvector_center_ne_zero (T : E →ₗ[ℝ] E)
    (f : E →ₗ[ℝ] ℝ) (hPSD : ∀ z, f z = 0 → 0 ≤ ⟪z,T z⟫)
    (x : E) (μ : ℝ) (hx : T x = μ • x) (hμ : μ < 0) (hnorm : ‖x‖ = 1) :
    f x ≠ 0 := by
  intro hf
  have h := hPSD x hf
  rw [hx, real_inner_smul_right, real_inner_self_eq_norm_sq, hnorm] at h
  norm_num at h
  linarith

theorem negative_eigenindex_unique [DecidableEq ι] (T : E →ₗ[ℝ] E)
    (f : E →ₗ[ℝ] ℝ) (hPSD : ∀ z, f z = 0 → 0 ≤ ⟪z,T z⟫)
    (b : OrthonormalBasis ι ℝ E) (μ : ι → ℝ)
    (he : ∀ i, T (b i) = μ i • b i)
    (i j : ι) (hi : μ i < 0) (hj : μ j < 0) : i = j := by
  by_contra hij
  have hfi := negative_eigenvector_center_ne_zero T f hPSD (b i) (μ i)
    (he i) hi (b.orthonormal.norm_eq_one i)
  let z := f (b j) • b i - f (b i) • b j
  have hfz : f z = 0 := by
    simp only [z, map_sub, map_smul, smul_eq_mul]
    ring
  have h := hPSD z hfz
  have hz : ⟪z,T z⟫ = μ i * (f (b j))^2 + μ j * (f (b i))^2 := by
    simp only [z, map_sub, map_smul, he, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right]
    have hii : ⟪b i,b i⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one]
      norm_num
    have hjj : ⟪b j,b j⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one]
      norm_num
    simp only [hii, hjj, b.orthonormal.2 hij, b.orthonormal.2 (Ne.symm hij)]
    ring
  rw [hz] at h
  have h1 : μ i * (f (b j))^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hi.le (sq_nonneg _)
  have h2 : μ j * (f (b i))^2 < 0 := mul_neg_of_neg_of_pos hj (sq_pos_of_ne_zero hfi)
  linarith

end
end FlatBernoulli
