import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

open Filter Topology
namespace ContactPilot

/-- A local analytic square root with the specified initial value, constructed
from the inverse function theorem, without a global square-root branch. -/
theorem local_sqrt_one : ∃ s : ℂ → ℂ, AnalyticAt ℂ s 1 ∧ s 1 = 1 ∧
    ∀ᶠ z in 𝓝 (1 : ℂ), s z ^ 2 = z := by
  let f : ℂ → ℂ := fun z => z ^ 2
  have ha : AnalyticAt ℂ f 1 := by dsimp [f]; fun_prop
  have hd : deriv f 1 ≠ 0 := by dsimp [f]; norm_num
  let s := ha.hasStrictDerivAt.localInverse f (deriv f 1) 1 hd
  refine ⟨s, ?_, ?_, ?_⟩
  · simpa [f] using ha.analyticAt_localInverse hd
  · have h := HasStrictFDerivAt.localInverse_apply_image
        (ha.hasStrictDerivAt.hasStrictFDerivAt_equiv hd)
    simpa [s, f] using h
  · simpa [s, f] using ha.hasStrictDerivAt.eventually_right_inverse hd

end ContactPilot

namespace ContactPilot
noncomputable section

def A (x : ℂ) : ℂ := 1 - Complex.I * x - 2*x^2 + Complex.I*x^3
def B (x : ℂ) : ℂ := 4 - (2+2*Complex.I)*x - x^2
def C (x : ℂ) : ℂ := 3 - Complex.I*x
def D (x : ℂ) : ℂ := (B x ^ 2 - 4*A x*C x)/4

theorem D_zero : D 0 = 1 := by norm_num [D, A, B, C]
theorem A_zero : A 0 = 1 := by norm_num [A]

theorem quadratic_factor (a b c d u : ℂ) (ha : a ≠ 0)
    (hd : d^2 = b^2 - 4*a*c) :
    a*u^2+b*u+c =
      a*(u-((-b+d)/(2*a)))*(u-((-b-d)/(2*a))) := by
  field_simp
  linear_combination hd

/-- Actual analytic, exhaustive branches of the desingularized stable
polynomial at L = -i, in the upper-half-plane chart x = -1/z. -/
theorem analytic_exhaustive_branches :
    ∃ u₁ u₃ : ℂ → ℂ,
      AnalyticAt ℂ u₁ 0 ∧ AnalyticAt ℂ u₃ 0 ∧ u₁ 0 = -1 ∧ u₃ 0 = -3 ∧
      ∀ᶠ x in 𝓝 (0 : ℂ), A x ≠ 0 ∧
        (∀ u : ℂ, A x*u^2+B x*u+C x = A x*(u-u₁ x)*(u-u₃ x)) ∧
        (∀ u : ℂ, A x*u^2+B x*u+C x = 0 ↔ u = u₁ x ∨ u = u₃ x) := by
  obtain ⟨s, hs, hs₀, hsq⟩ := local_sqrt_one
  have hA : AnalyticAt ℂ A 0 := by unfold A; fun_prop
  have hB : AnalyticAt ℂ B 0 := by unfold B; fun_prop
  have hC : AnalyticAt ℂ C 0 := by unfold C; fun_prop
  have hD : AnalyticAt ℂ D 0 := by unfold D; fun_prop
  have hsD : AnalyticAt ℂ (fun x => s (D x)) 0 :=
    hs.comp_of_eq hD D_zero
  let d : ℂ → ℂ := fun x => 2*s (D x)
  let u₁ : ℂ → ℂ := fun x => (-B x+d x)/(2*A x)
  let u₃ : ℂ → ℂ := fun x => (-B x-d x)/(2*A x)
  have hden : (2:ℂ)*A 0 ≠ 0 := by rw [A_zero]; norm_num
  refine ⟨u₁, u₃, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hB.neg.add (analyticAt_const.mul hsD)).div (analyticAt_const.mul hA) hden
  · exact (hB.neg.sub (analyticAt_const.mul hsD)).div (analyticAt_const.mul hA) hden
  · norm_num [u₁, d, D_zero, hs₀, B, A]
  · simp [u₃, d, D_zero, hs₀, B, A]; ring
  · have hsqD : ∀ᶠ x in 𝓝 (0:ℂ), s (D x)^2 = D x :=
      hD.continuousAt.tendsto.eventually (by simpa only [D_zero] using hsq)
    have hn : ∀ᶠ x in 𝓝 (0:ℂ), A x ≠ 0 :=
      hA.continuousAt.eventually_ne (by rw [A_zero]; norm_num)
    filter_upwards [hsqD, hn] with x hx hax
    have hd : d x ^ 2 = B x ^ 2 - 4*A x*C x := by
      dsimp [d]; rw [mul_pow, hx]; dsimp [D]; ring
    have hf := fun u => quadratic_factor (A x) (B x) (C x) (d x) u hax hd
    refine ⟨hax, hf, fun u => ?_⟩
    rw [hf u]
    simp only [mul_eq_zero, hax, false_or, sub_eq_zero, u₁, u₃]
end
end ContactPilot
