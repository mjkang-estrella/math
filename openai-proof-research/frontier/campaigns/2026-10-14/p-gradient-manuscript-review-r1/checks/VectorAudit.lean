import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Dimension-free ellipticity of the actual zero-jet vector quadratic form.
This avoids choosing a parallel/perpendicular coordinate decomposition.
It certifies no viscosity, compactness, regularity, or novelty statement.
-/

namespace FrontierSupport.VectorEllipticity

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def form (a h : E) (b t s : ℝ) : ℝ :=
  ‖h‖^2 + (1 + t^2) * s^2 - (⟪a, h⟫_ℝ + b*t*s)^2

theorem norm_smul_sub_sq (a h : E) (u v : ℝ) :
    ‖u • h - v • a‖^2 = u^2 * ‖h‖^2 -
      2*u*v*⟪a, h⟫_ℝ + v^2 * ‖a‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm h a]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem gram_nonneg (a h : E) :
    0 ≤ ‖a‖^2 * ‖h‖^2 - ⟪a, h⟫_ℝ^2 := by
  have hc := real_inner_mul_inner_self_le a h
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hc
  nlinarith only [hc]

theorem square_decomposition (a h : E) (b t s : ℝ)
    (hunit : ‖a‖^2 + b^2 = 1) :
    form a h b t s = ‖b • h - (t*s) • a‖^2 + s^2 +
      (‖a‖^2 * ‖h‖^2 - ⟪a, h⟫_ℝ^2) := by
  rw [norm_smul_sub_sq]
  unfold form
  nlinarith only [congrArg (fun z : ℝ => z * ‖h‖^2) hunit,
    congrArg (fun z : ℝ => z * (t^2*s^2)) hunit]

theorem lower_certificate (a h : E) (b t s : ℝ)
    (hunit : ‖a‖^2 + b^2 = 1) :
    3 * form a h b t s - b^2 * (‖h‖^2 + s^2) =
      ‖b • h - (2*t*s) • a‖^2 + ‖b • h - (t*s) • a‖^2 +
      3 * (‖a‖^2 * ‖h‖^2 - ⟪a, h⟫_ℝ^2) +
      (3-b^2-2*t^2*‖a‖^2)*s^2 := by
  rw [norm_smul_sub_sq, norm_smul_sub_sq]
  unfold form
  nlinarith only [congrArg (fun z : ℝ => z * ‖h‖^2) hunit,
    congrArg (fun z : ℝ => z * (t^2*s^2)) hunit]

theorem bounds (a h : E) (b t s : ℝ)
    (hunit : ‖a‖^2 + b^2 = 1) (ht : t^2 ≤ 1) :
    b^2/3 * (‖h‖^2 + s^2) ≤ form a h b t s ∧
    form a h b t s ≤ 2 * (‖h‖^2 + s^2) := by
  have hb : b^2 ≤ 1 := by nlinarith [sq_nonneg ‖a‖]
  have hat : 0 ≤ ‖a‖^2 * (1-t^2) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hcoeff : 0 ≤ 3-b^2-2*t^2*‖a‖^2 := by nlinarith
  have hss := mul_nonneg hcoeff (sq_nonneg s)
  have hg := gram_nonneg a h
  have hc := lower_certificate a h b t s hunit
  constructor
  · nlinarith only [hc, hss, hg,
      sq_nonneg ‖b • h - (2*t*s) • a‖,
      sq_nonneg ‖b • h - (t*s) • a‖]
  · unfold form
    have hts := mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg s)
    nlinarith only [hts, sq_nonneg ‖h‖, sq_nonneg (⟪a, h⟫_ℝ + b*t*s)]

theorem uniform_bounds (a h : E) (b t s b0 : ℝ)
    (hunit : ‖a‖^2 + b^2 = 1) (ht : t^2 ≤ 1)
    (hb0 : b0^2 ≤ b^2) :
    b0^2/3 * (‖h‖^2 + s^2) ≤ form a h b t s ∧
    form a h b t s ≤ 2 * (‖h‖^2 + s^2) := by
  have hbounds := bounds a h b t s hunit ht
  have hm := mul_nonneg (sub_nonneg.mpr hb0)
    (add_nonneg (sq_nonneg ‖h‖) (sq_nonneg s))
  exact ⟨by nlinarith [hbounds.1], hbounds.2⟩

noncomputable def physicalForm (a h : E) (b e s : ℝ) : ℝ :=
  ‖h‖^2 + (1+e)*s^2 - (⟪a, h⟫_ℝ + b*Real.sqrt e*s)^2

theorem physical_uniform_bounds (a h : E) (b e s b0 : ℝ)
    (hunit : ‖a‖^2 + b^2 = 1) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hb0 : b0^2 ≤ b^2) :
    b0^2/3 * (‖h‖^2 + s^2) ≤ physicalForm a h b e s ∧
    physicalForm a h b e s ≤ 2 * (‖h‖^2 + s^2) := by
  have ht : (Real.sqrt e)^2 ≤ 1 := by
    rw [Real.sq_sqrt he0]
    exact he1
  simpa only [physicalForm, form, Real.sq_sqrt he0] using
    uniform_bounds a h b (Real.sqrt e) s b0 hunit ht hb0

end FrontierSupport.VectorEllipticity

#print axioms FrontierSupport.VectorEllipticity.norm_smul_sub_sq
#print axioms FrontierSupport.VectorEllipticity.gram_nonneg
#print axioms FrontierSupport.VectorEllipticity.square_decomposition
#print axioms FrontierSupport.VectorEllipticity.lower_certificate
#print axioms FrontierSupport.VectorEllipticity.bounds
#print axioms FrontierSupport.VectorEllipticity.uniform_bounds
#print axioms FrontierSupport.VectorEllipticity.physical_uniform_bounds
