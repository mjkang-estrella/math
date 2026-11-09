import PolynomialConvexity.Reindex
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace PolynomialConvexity
noncomputable section
open Finset MeasureTheory

def orthant (n L : ℕ) : Set (Edge n L → ℝ) := {x | ∀ e, 0 ≤ x e}

theorem orthant_convex (n L : ℕ) : Convex ℝ (orthant n L) := by
  intro x hx y hy a b ha hb _ e
  exact add_nonneg (mul_nonneg ha (hx e)) (mul_nonneg hb (hy e))

def linearForm {n L : ℕ} (z x : Edge n L → ℝ) : ℝ := ∑ e, x e * z e

theorem linearForm_nonneg {n L : ℕ} {z x : Edge n L → ℝ}
    (hz : ∀ e, 0 ≤ z e) (hx : x ∈ orthant n L) : 0 ≤ linearForm z x :=
  sum_nonneg fun e _ => mul_nonneg (hx e) (hz e)

theorem linearForm_mix {n L : ℕ} (z x y : Edge n L → ℝ) (a b : ℝ) :
    linearForm z (a • x + b • y) = a * linearForm z x + b * linearForm z y := by
  simp [linearForm, add_mul, mul_assoc, sum_add_distrib, mul_sum]

/-- Pointwise convexity in the weight vector; no probability hypotheses. -/
theorem power_linearForm_convex {n L : ℕ} (d : ℕ) (z : Edge n L → ℝ)
    (hz : ∀ e, 0 ≤ z e) :
    ConvexOn ℝ (orthant n L) (fun x => linearForm z x ^ d) := by
  refine ⟨orthant_convex n L, ?_⟩
  intro x hx y hy a b ha hb hab
  dsimp only
  rw [linearForm_mix]
  exact (convexOn_pow d).2 (linearForm_nonneg hz hx) (linearForm_nonneg hz hy)
    ha hb hab

/-- Ordered-tuple expansion of the actual linear form, with repetition. -/
theorem power_linearForm_expand {n L : ℕ} (d : ℕ) (z x : Edge n L → ℝ) :
    linearForm z x ^ d =
      ∑ e : Fin d → Edge n L, weight x e * ∏ i, z (e i) := by
  rw [linearForm, Fintype.sum_pow]
  apply sum_congr rfl
  intro e _
  exact prod_mul_distrib

/-- General integration helper. Integrability remains an explicit obligation;
this theorem is not a source conjecture endpoint or a moment identity. -/
theorem integral_power_convex {n L : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (d : ℕ) (z : Ω → Edge n L → ℝ)
    (hz : ∀ ω e, 0 ≤ z ω e)
    (hint : ∀ x ∈ orthant n L, Integrable (fun ω => linearForm (z ω) x ^ d) μ) :
    ConvexOn ℝ (orthant n L) (fun x => ∫ ω, linearForm (z ω) x ^ d ∂μ) := by
  refine ⟨orthant_convex n L, ?_⟩
  intro x hx y hy a b ha hb hab
  have hi := hint (a • x + b • y) ((orthant_convex n L) hx hy ha hb hab)
  have hj := ((hint x hx).const_mul a).add ((hint y hy).const_mul b)
  have hle := integral_mono hi hj (fun ω =>
    (power_linearForm_convex d (z ω) (hz ω)).2 hx hy ha hb hab)
  simpa only [Pi.add_apply, integral_add ((hint x hx).const_mul a) ((hint y hy).const_mul b),
    integral_const_mul, smul_eq_mul] using hle

end
end PolynomialConvexity
