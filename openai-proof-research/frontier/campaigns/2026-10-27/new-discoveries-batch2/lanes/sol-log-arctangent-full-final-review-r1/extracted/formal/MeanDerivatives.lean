import MeanAnalyticDefs
import Mathlib.Tactic.FunProp
set_option autoImplicit false
set_option warningAsError true
namespace LogArctangentMean
noncomputable def Ap (t : ℝ) : ℝ :=
  (4*Real.sinh (4*t) -
    (Real.sinh t*Real.cosh (d*t) + Real.cosh t*(d*Real.sinh (d*t))) +
    (5/d)*(Real.cosh t*Real.sinh (d*t)+Real.sinh t*(d*Real.cosh (d*t))))/2
noncomputable def Bp (t : ℝ) : ℝ :=
  (Real.cosh t*(Real.cosh (5*t)-Real.cosh (d*t))+
    Real.sinh t*(5*Real.sinh (5*t)-d*Real.sinh (d*t)))/2
theorem hasDerivAt_A (t : ℝ) : HasDerivAt A (Ap t) t := by
  have h1 := (hasDerivAt_id t)
  have h4 := ((hasDerivAt_id t).const_mul 4)
  have hd := ((hasDerivAt_id t).const_mul d)
  convert (((h4.cosh.sub (h1.cosh.mul hd.cosh)).add
    ((h1.sinh.mul hd.sinh).const_mul (5/d))).div_const 2) using 1
  · funext x; dsimp [A, id]; ring
  · dsimp [Ap, id]; ring
theorem hasDerivAt_B (t : ℝ) : HasDerivAt B (Bp t) t := by
  have h1 := (hasDerivAt_id t)
  have h5 := ((hasDerivAt_id t).const_mul 5)
  have hd := ((hasDerivAt_id t).const_mul d)
  convert ((h1.sinh.mul (h5.cosh.sub hd.cosh)).div_const 2) using 1
  · rfl
  · dsimp [Bp, id]; ring
theorem deriv_A : deriv A = Ap := funext fun t => (hasDerivAt_A t).deriv
theorem deriv_B : deriv B = Bp := funext fun t => (hasDerivAt_B t).deriv
theorem contDiff_A : ContDiff ℝ ⊤ A := by unfold A; fun_prop
theorem contDiff_B : ContDiff ℝ ⊤ B := by unfold B; fun_prop
theorem contDiff_Ap : ContDiff ℝ ⊤ Ap := by unfold Ap; fun_prop
theorem contDiff_Bp : ContDiff ℝ ⊤ Bp := by unfold Bp; fun_prop
theorem contDiff_U : ContDiff ℝ ⊤ U := by
  unfold U
  simp only [deriv_A, deriv_B]
  exact ((contDiff_Bp.mul contDiff_A).sub (contDiff_B.mul contDiff_Ap)).sub
    (contDiff_A.pow 2)
theorem contDiff_V : ContDiff ℝ ⊤ V := by
  unfold V
  exact ((contDiff_const.mul contDiff_B).mul contDiff_A)
theorem contDiff_E : ContDiff ℝ ⊤ E := by
  unfold E
  exact ((contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2))).mul
    contDiff_U).add (contDiff_id.mul contDiff_V)
end LogArctangentMean
