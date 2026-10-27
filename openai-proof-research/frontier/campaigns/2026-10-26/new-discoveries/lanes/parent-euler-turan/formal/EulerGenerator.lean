import AffineDerivative
noncomputable section
open Filter Set
open scoped Topology
namespace EulerTuran
def eulerGenerator (z : ℂ) : ℂ := 1 / Complex.cos z + Complex.tan z
def normalizedEuler (n : ℕ) : ℝ := (iteratedDeriv n eulerGenerator 0).re / n.factorial
lemma eulerGenerator_analyticAt_zero : AnalyticAt ℂ eulerGenerator 0 := by
  change AnalyticAt ℂ (fun z : ℂ => 1 / Complex.cos z + Complex.sin z / Complex.cos z) 0
  apply AnalyticAt.add
  · exact AnalyticAt.div (by fun_prop) (by fun_prop) (by simp)
  · exact AnalyticAt.div (by fun_prop) (by fun_prop) (by simp)
lemma eulerGenerator_cot {z : ℂ} (hz : Complex.cos z ≠ 0) :
    eulerGenerator z = Complex.cot ((Real.pi:ℂ)/4-z/2) := by
  let u : ℂ := (Real.pi:ℂ)/4-z/2
  have hsin : Complex.sin (2*u) = Complex.cos z := by
    rw [show 2*u = (Real.pi:ℂ)/2-z by dsimp [u]; ring]
    exact Complex.sin_pi_div_two_sub z
  have hcos : Complex.cos (2*u) = Complex.sin z := by
    rw [show 2*u = (Real.pi:ℂ)/2-z by dsimp [u]; ring]
    exact Complex.cos_pi_div_two_sub z
  have hu : Complex.sin u ≠ 0 := by
    intro h
    rw [Complex.sin_two_mul, h, mul_zero, zero_mul] at hsin
    exact hz hsin.symm
  rw [Complex.sin_two_mul] at hsin
  rw [Complex.cos_two_mul] at hcos
  dsimp [eulerGenerator, Complex.tan, Complex.cot]
  change 1 / Complex.cos z + Complex.sin z / Complex.cos z = Complex.cos u / Complex.sin u
  field_simp
  linear_combination -Complex.sin u * hcos + Complex.cos u * hsin
lemma eulerGenerator_eventually_cot :
    eulerGenerator =ᶠ[𝓝 (0:ℂ)]
      (fun z => Complex.cot ((Real.pi:ℂ)/4-z/2)) := by
  have h : ∀ᶠ z : ℂ in 𝓝 0, Complex.cos z ≠ 0 :=
    (Complex.continuous_cos.continuousAt (x := 0)).eventually_ne (by simp)
  filter_upwards [h] with z hz
  exact eulerGenerator_cot hz
lemma normalizedEuler_zero : normalizedEuler 0 = 1 := by
  simp [normalizedEuler, eulerGenerator]
end EulerTuran
