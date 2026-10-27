import EulerGenerator
noncomputable section
open Filter Set
open scoped Topology
namespace EulerTuran
lemma quarter_integerComplement : (1/4:ℂ) ∈ Complex.integerComplement := by
  rintro ⟨m, hm⟩
  have hr := congrArg Complex.re hm
  norm_num at hr
  have h1 : (0:ℝ) < m := by linarith
  have h2 : (m:ℝ) < 1 := by linarith
  have : (0:ℤ) < m := by exact_mod_cast h1
  have : m < (1:ℤ) := by exact_mod_cast h2
  omega
lemma coefficient_factor (n : ℕ) (S : ℂ) :
    ((-1/(2*(Real.pi:ℂ)))^n * ((-1:ℂ)^n * (n.factorial:ℂ) * S) /
      (Real.pi:ℂ)) / (n.factorial:ℂ) = S / ((2:ℂ)^n * (Real.pi:ℂ)^(n+1)) := by
  have hf : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  calc
    _ = ((-1/(2*(Real.pi:ℂ)))^n * (-1:ℂ)^n) * S / (Real.pi:ℂ) := by field
    _ = (1/(2*(Real.pi:ℂ)))^n * S / (Real.pi:ℂ) := by
      rw [← mul_pow]
      congr 3
      ring
    _ = _ := by rw [div_pow, one_pow, mul_pow, pow_succ]; field
lemma euler_derivative_series {n : ℕ} (hn : 1 ≤ n) :
    iteratedDeriv n eulerGenerator 0 / (n.factorial:ℂ) =
      (∑' m : ℤ, 1 / ((1/4:ℂ)+m)^(n+1)) /
        ((2:ℂ)^n * (Real.pi:ℂ)^(n+1)) := by
  let F : ℂ → ℂ := fun z => (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*z)
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have heq : (fun z : ℂ => Complex.cot ((Real.pi:ℂ)/4-z/2)) =
      (fun z => F ((1/4:ℂ)+(-1/(2*(Real.pi:ℂ)))*z) / (Real.pi:ℂ)) := by
    funext z
    dsimp [F]
    have hh : (Real.pi:ℂ) * (1/4+(-1/(2*(Real.pi:ℂ)))*z) =
      (Real.pi:ℂ)/4-z/2 := by field
    rw [hh]
    field
  have hsame := (eulerGenerator_eventually_cot.iteratedDeriv n).eq_of_nhds
  rw [heq, iteratedDeriv_div_const,
    iteratedDeriv_affine F (1/4) (-1/(2*(Real.pi:ℂ)))
      (div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) hp)), mul_zero,
    add_zero] at hsame
  have hcot := cot_derivative_at_real (a := (1/4:ℝ)) (by simpa using quarter_integerComplement) hn
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hcot
  change iteratedDeriv n F (1/4) = _ at hcot
  rw [hsame, hcot]
  exact coefficient_factor n _
lemma normalizedEuler_shifted_series {n : ℕ} (hn : 1 ≤ n) :
    normalizedEuler n = (∑' m : ℤ, 1 / ((1/4:ℝ)+m)^(n+1)) /
      ((2:ℝ)^n * Real.pi^(n+1)) := by
  have h := euler_derivative_series hn
  have hc : (∑' m : ℤ, 1 / ((1/4:ℂ)+m)^(n+1)) =
      ((∑' m : ℤ, 1 / ((1/4:ℝ)+m)^(n+1)):ℝ) := by
    rw [Complex.ofReal_tsum]
    congr 1
    ext m
    push_cast
    rfl
  rw [hc] at h
  have hh := congrArg Complex.re h
  have hden : (2:ℂ)^n * (Real.pi:ℂ)^(n+1) = (((2:ℝ)^n * Real.pi^(n+1):ℝ):ℂ) := by push_cast; rfl
  rw [hden, ← Complex.ofReal_div, Complex.ofReal_re] at hh
  simpa [normalizedEuler, Complex.div_ofReal_re] using hh
lemma euler_coefficient_eq_real (n : ℕ) :
    iteratedDeriv n eulerGenerator 0 / (n.factorial:ℂ) = (normalizedEuler n : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp [normalizedEuler, eulerGenerator]
  · have hn1 : 1 ≤ n := by omega
    rw [euler_derivative_series hn1, normalizedEuler_shifted_series hn1]
    push_cast
    congr 1
/-- These are genuine coefficients of the source's analytic generating function. -/
theorem eulerGenerator_hasFPowerSeriesAt :
    HasFPowerSeriesAt eulerGenerator
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (normalizedEuler n : ℂ))) 0 := by
  have h := eulerGenerator_analyticAt_zero.hasFPowerSeriesAt
  simpa only [euler_coefficient_eq_real] using h
end EulerTuran
