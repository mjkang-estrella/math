module
public import Tail
public import LogConcavity
public import Profile
public section
set_option autoImplicit false
set_option warningAsError true
open Real Filter MeasureTheory Set
namespace Renyi
theorem finite_tail_cutoff {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∃ a : ℝ, 0 < a ∧ tail p a < J p := by
  obtain ⟨a, ha, ht⟩ := ((eventually_gt_atTop (0:ℝ)).and (eventually_tail_lt_J hp hp1)).exists
  exact ⟨a, ha, ht⟩

theorem truncated_density_properties {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    LogConcaveDensity (density a) ∧ Integrable (density a) ∧
    (∫ x : ℝ, density a x) = 1 ∧
    Integrable (fun x => (density a x)^p) ∧ 0 < moment p (density a) ∧
    (∀ s, Integrable (fun t => density a t*density a (s-t))) ∧
    Integrable (fun s => (convolution (density a) (density a) s)^p) ∧
    0 < moment p (convolution (density a) (density a)) :=
  ⟨density_logConcave ha, density_integrable a, density_integral ha,
    density_power_integrable ha hp, density_moment_pos ha hp,
    convolution_integrable a, convolution_power_integrable ha hp,
    convolution_moment_pos ha hp⟩
end Renyi
