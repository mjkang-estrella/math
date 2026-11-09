import PolynomialConvexity.Identification
set_option Elab.async false
namespace PolynomialConvexity
noncomputable section
open MeasureTheory Finset

/-- Exact factorial normalization for every signed real weight vector. -/
theorem moment_identity {n L : ℕ} (hL : 0 < L) (d : ℕ) (x : Edge n L → ℝ) :
    (∫ ω, linearForm (fun e => lifetime hL e ω) x ^ d ∂clockMeasure n) =
      (Nat.factorial d : ℝ) * sourcePolynomial n L d x := by
  rw [integrated_expansion]
  simp_rw [mixed_moment hL]
  exact symmetrized_sum x

theorem simplex_convex (n L : ℕ) : Convex ℝ (simplex n L) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun e => add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
  rw [hx.2, hy.2, mul_one, mul_one]
  exact hab

/-- In fact the literal source polynomial is convex on the entire nonnegative orthant. -/
theorem sourcePolynomial_convex_orthant {n L : ℕ} (hL : 0 < L) (d : ℕ) :
    ConvexOn ℝ (orthant n L) (sourcePolynomial n L d) := by
  have hf : (Nat.factorial d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  have hc := (concrete_integral_convex (n := n) hL d).smul
    (inv_nonneg.mpr (show (0 : ℝ) ≤ Nat.factorial d from Nat.cast_nonneg _))
  have heq : (fun x => (Nat.factorial d : ℝ)⁻¹ •
      ∫ ω, linearForm (fun e => lifetime hL e ω) x ^ d ∂clockMeasure n) =
      sourcePolynomial n L d := by
    funext x
    rw [moment_identity hL]
    simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hf, one_mul]
  rw [heq] at hc
  exact hc

/-- Full literal MathDB 347913 / arXiv Eq. (2), Section 3 Conjecture 1;
SIAM Eq. (1.1), Section 4 Conjecture 1. No L ≤ n or degree bound. -/
theorem source_conjecture : SourceConjecture := by
  intro n L d _ hL _
  exact (sourcePolynomial_convex_orthant (by omega : 0 < L) d).subset
    (fun _ hx => hx.1) (simplex_convex n L)

end
end PolynomialConvexity
