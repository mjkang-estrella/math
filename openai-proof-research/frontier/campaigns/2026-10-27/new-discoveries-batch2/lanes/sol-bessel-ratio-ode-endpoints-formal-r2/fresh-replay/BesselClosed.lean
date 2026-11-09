module
public import BesselODE
public section
noncomputable section
open scoped Topology
open Filter
namespace BesselRatio

theorem wDerivative : WDerivative := by
  intro u v a b x hu hv ha hb hx
  have hf := scaled_hasDerivAt hu ha hx
  have hg := scaled_hasDerivAt hv hb hx
  have hd := ((scaledODE u a x hu ha hx).mul hg).sub
    (hf.mul (scaledODE v b x hv hb hx))
  have heq : W u v a b =ᶠ[𝓝 x] (fun y =>
      (y * deriv (scaled u a) y) * scaled v b y -
      scaled u a y * (y * deriv (scaled v b) y)) := by
    apply Filter.Eventually.of_forall
    intro y
    dsimp [W]
    ring
  apply (hd.congr_of_eventuallyEq heq).congr_deriv
  field_simp
  ring

theorem scaled_second_hasDerivAt {ν a x : ℝ} (hν : -1 < ν) (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (deriv (scaled ν a))
      (((a^2*x + ν^2/x)*scaled ν a x*x - x*deriv (scaled ν a) x) / x^2) x := by
  have hd := (scaledODE ν a x hν ha hx).div (hasDerivAt_id x) hx.ne'
  have he : deriv (scaled ν a) =ᶠ[𝓝 x] (fun y => (y*deriv (scaled ν a) y)/y) := by
    filter_upwards [eventually_ne_nhds hx.ne'] with y hy
    field_simp
  convert hd.congr_of_eventuallyEq he using 1; simp only [id_eq, mul_one]
end BesselRatio
