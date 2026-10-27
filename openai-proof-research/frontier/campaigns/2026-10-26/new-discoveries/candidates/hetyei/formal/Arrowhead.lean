import SpectralMoments

open Finset Matrix
open scoped RealInnerProductSpace
namespace FlatBernoulli
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The center is `none`; the remaining coordinates carry the diagonal. -/
def arrowhead (t v : ι → ℝ) : Matrix (Option ι) (Option ι) ℝ
  | none, none => 0
  | none, some j => v j
  | some i, none => v i
  | some i, some j => if i=j then t i else 0

omit [Fintype ι] in
theorem arrowhead_isHermitian (t v : ι → ℝ) : (arrowhead t v).IsHermitian := by
  ext i j
  cases i <;> cases j <;> simp [arrowhead, Matrix.conjTranspose_apply, eq_comm]
  split_ifs <;> simp_all

theorem arrowhead_mulVec_none (t v : ι → ℝ) (x : Option ι → ℝ) :
    ((arrowhead t v) *ᵥ x) none = ∑ i, v i*x (some i) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_option, arrowhead]

theorem arrowhead_mulVec_some (t v : ι → ℝ) (x : Option ι → ℝ) (i : ι) :
    ((arrowhead t v) *ᵥ x) (some i) = v i*x none+t i*x (some i) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_option, arrowhead]

theorem arrowhead_quadratic (t v : ι → ℝ) (x : Option ι → ℝ) :
    x ⬝ᵥ ((arrowhead t v) *ᵥ x) =
      2*x none*(∑ i, v i*x (some i)) + ∑ i, t i*x (some i)^2 := by
  simp only [dotProduct, Fintype.sum_option, arrowhead_mulVec_none,
    arrowhead_mulVec_some]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hcross : (∑ i, x (some i)*(v i*x none)) =
      x none*(∑ i, v i*x (some i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcross]
  have hdiag : (∑ i, x (some i)*(t i*x (some i))) =
      ∑ i, t i*x (some i)^2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdiag]
  ring

omit [DecidableEq ι] in
theorem option_dot_self (x : Option ι → ℝ) :
    x ⬝ᵥ x = x none^2 + ∑ i, x (some i)^2 := by
  simp only [dotProduct, Fintype.sum_option, pow_two]

theorem arrowhead_zero_center_nonneg (t v : ι → ℝ) (ht : ∀ i, 0 ≤ t i)
    (x : Option ι → ℝ) (hx : x none = 0) :
    0 ≤ x ⬝ᵥ ((arrowhead t v) *ᵥ x) := by
  rw [arrowhead_quadratic, hx]
  simp only [mul_zero, zero_mul, zero_add]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (ht i) (sq_nonneg _)

theorem arrowhead_upper_sos (t r s : ι → ℝ)
    (hr : ∑ i, r i^2 = 1) (hs : ∀ i, s i^2 = 1-t i)
    (x : Option ι → ℝ) :
    x ⬝ᵥ x - x ⬝ᵥ ((arrowhead t (fun i => s i*r i)) *ᵥ x) =
      ∑ i, (s i*x (some i)-r i*x none)^2 := by
  rw [option_dot_self, arrowhead_quadratic]
  have he : ∀ i, (s i*x (some i)-r i*x none)^2 =
      x (some i)^2-t i*x (some i)^2 -
      2*x none*(s i*r i*x (some i))+r i^2*x none^2 := by
    intro i
    rw [sub_sq, mul_pow, mul_pow, hs i]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, hr]
  ring

theorem arrowhead_lower_sos (t r s : ι → ℝ)
    (hr : ∑ i, r i^2 = 1) (hs : ∀ i, s i^2 = 1-t i)
    (x : Option ι → ℝ) :
    x ⬝ᵥ x + x ⬝ᵥ ((arrowhead t (fun i => s i*r i)) *ᵥ x) =
      (∑ i, (s i*x (some i)+r i*x none)^2) +
      2*(∑ i, t i*x (some i)^2) := by
  rw [option_dot_self, arrowhead_quadratic]
  have he : ∀ i, (s i*x (some i)+r i*x none)^2 =
      x (some i)^2-t i*x (some i)^2 +
      2*x none*(s i*r i*x (some i))+r i^2*x none^2 := by
    intro i
    rw [add_sq, mul_pow, mul_pow, hs i]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, hr]
  ring

end
end FlatBernoulli
