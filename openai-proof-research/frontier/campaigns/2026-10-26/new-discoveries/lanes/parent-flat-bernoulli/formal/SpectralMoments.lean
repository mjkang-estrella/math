import Mathlib

open Finset
open scoped RealInnerProductSpace
namespace FlatBernoulli

section General
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem basis_power_eigenvector (T : E →ₗ[ℝ] E)
    (b : OrthonormalBasis ι ℝ E) (μ : ι → ℝ)
    (he : ∀ i, T (b i) = μ i • b i) (n : ℕ) (i : ι) :
    (T^n) (b i) = μ i^n • b i := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ', Module.End.mul_apply, hn, map_smul, he, smul_smul, pow_succ']
    rw [mul_comm]

theorem basis_moment_expansion (T : E →ₗ[ℝ] E)
    (b : OrthonormalBasis ι ℝ E) (μ : ι → ℝ)
    (he : ∀ i, T (b i) = μ i • b i) (n : ℕ) (x : E) :
    ⟪x, (T^n) x⟫ = ∑ i, ⟪b i, x⟫^2 * μ i^n := by
  have hT : (T^n) x = ∑ i, ⟪b i, x⟫ • (μ i^n • b i) := by
    nth_rw 1 [← b.sum_repr' x]
    simp only [map_sum, map_smul, basis_power_eigenvector T b μ he]
  rw [hT, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [real_inner_smul_right, real_inner_comm x (b i)]
  ring

end General
end FlatBernoulli
