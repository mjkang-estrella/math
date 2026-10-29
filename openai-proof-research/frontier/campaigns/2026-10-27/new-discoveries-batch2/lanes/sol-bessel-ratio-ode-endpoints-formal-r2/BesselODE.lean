module
public import BesselSeriesODE
public import BesselEndpoints
public section
noncomputable section
open scoped Topology
open Filter
namespace BesselRatio

theorem euler_hasDerivAt {ν t : ℝ} (hν : -1 < ν) :
    HasDerivAt (euler ν)
      (ν * deriv (S ν) t + 2 * deriv (S ν) t + 2*t*deriv (deriv (S ν)) t) t := by
  have hd := (S_analytic hν t).deriv.differentiableAt.hasDerivAt
  convert ((S_hasDerivAt hν t).const_mul ν).add
    (((hasDerivAt_id t).const_mul 2).mul hd) using 1
  · funext y; dsimp [euler]
  · dsimp; ring

theorem scaledODE : ScaledODE := by
  intro ν a x hν ha hx
  have hz : 0 < a*x/2 := by positivity
  have hr : (a*x/2)^(ν-1) * (a*x/2) = (a*x/2)^ν := by
    rw [← Real.rpow_add_one hz.ne']; congr 1; ring
  have hp : HasDerivAt (fun y : ℝ => (a*y/2)^ν) ((a*x/2)^ν * ν / x) x := by
    convert (((hasDerivAt_id x).const_mul a).div_const 2).rpow_const
      (Or.inl hz.ne') (p := ν) using 1
    dsimp
    field_simp
    calc
      _ = ν * ((a*x/2)^(ν-1) * (a*x/2)) * 2 := by rw [hr]; ring
      _ = _ := by simp only [id_eq]; ring
  have hd := hp.mul ((euler_hasDerivAt hν).comp x (((hasDerivAt_id x).const_mul a).pow 2))
  have heq : (fun y => y * deriv (scaled ν a) y) =ᶠ[𝓝 x]
      (fun y => (a*y/2)^ν * euler ν ((a*y)^2)) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact scaled_euler hν ha hy
  apply (hd.congr_of_eventuallyEq heq).congr_deriv
  dsimp
  rw [scaled, I_eq_rpow_mul_S (mul_pos ha hx)]
  have ho := S_ode (t := (a*x)^2) hν
  dsimp [euler]
  field_simp
  calc
    _ = ν^2 * S ν ((a*x)^2) + (a*x)^2 *
        (4*(a*x)^2*deriv (deriv (S ν)) ((a*x)^2) + 4*(ν+1)*deriv (S ν) ((a*x)^2)) := by ring
    _ = _ := by rw [ho]; ring
end BesselRatio
