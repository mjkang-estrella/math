import Mathlib

open Filter Set
open scoped Topology ContDiff

namespace DeTemple

noncomputable def sourcePsi (x : ℝ) : ℝ := deriv Real.Gamma x / Real.Gamma x

noncomputable def sourceH (x : ℝ) : ℝ := sourcePsi (x + 1 / 2)

noncomputable def sourceR (x : ℝ) : ℝ := sourceH x - Real.log x

noncomputable def sourceG (a x : ℝ) : ℝ :=
  24 * (x ^ 4 + a * x ^ 2 + 7 * a / 40 - 31 / 336) * sourceR x -
    (x ^ 2 - 7 / 40 + a)

def SourceCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ioi (0 : ℝ)) ∧
    ∀ (n : ℕ) (x : ℝ), 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n f x

def SourceConjecture328867ii : Prop :=
  ∀ a : ℝ, SourceCompletelyMonotone (fun x => -sourceG a x) ↔ a ≤ 155 / 294

theorem realGamma_deriv_eq_complex {x : ℝ} (hx : 0 < x) :
    deriv Real.Gamma x = (deriv Complex.Gamma (x : ℂ)).re := by
  have hs (m : ℕ) : (x : ℂ) ≠ -(m : ℂ) := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hr
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  exact (Complex.differentiableAt_Gamma (x : ℂ) hs).hasDerivAt.real_of_complex.deriv

theorem gamma_analyticAt_half : AnalyticAt ℂ Complex.Gamma (1 / 2 : ℂ) := by
  have hu : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply Complex.differentiableAt_Gamma
    intro m he
    have hr := congrArg Complex.re he
    simp only [Complex.neg_re, Complex.natCast_re] at hr
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    dsimp at hz
    linarith
  exact hd.analyticOnNhd hu _ (by norm_num)

theorem sourcePsi_continuousAt_half : ContinuousAt sourcePsi (1 / 2 : ℝ) := by
  have hc : ContinuousAt (fun x : ℝ => (deriv Complex.Gamma (x : ℂ)).re) (1 / 2) := by
    have hh := gamma_analyticAt_half.deriv.continuousAt
    have he : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
    rw [← he] at hh
    exact Complex.continuous_re.continuousAt.comp
      (hh.comp Complex.continuous_ofReal.continuousAt)
  have hg : ContinuousAt Real.Gamma (1 / 2 : ℝ) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.continuousAt
      (isOpen_Ioi.mem_nhds (by norm_num))
  have hq := hc.div hg (ne_of_gt (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)))
  apply hq.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
  simp [sourcePsi, realGamma_deriv_eq_complex hx]

theorem sourceH_continuousAt_zero : ContinuousAt sourceH 0 := by
  exact sourcePsi_continuousAt_half.comp_of_eq
    (f := fun x : ℝ => x + 1 / 2) (by fun_prop) (by simp)

end DeTemple
