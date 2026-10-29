module
public import Baseline
public section
set_option autoImplicit false
set_option warningAsError true
open Real MeasureTheory Set
namespace Renyi
theorem normalizer_ge_one {a : ℝ} (ha : 0 < a) : 1 ≤ normalizer a := by
  have hn := normalizer_pos ha
  have hd : 0 < 1-exp (-a) := inv_pos.mp hn
  change 1 ≤ (1-exp (-a))⁻¹
  rw [inv_eq_one_div, le_div_iff₀ hd]
  linarith [exp_pos (-a)]

theorem strict_ratio {a p : ℝ} (ha : 0 < a) (hp : 0 < p)
    (ht : tail p a < J p) :
    p*J p < moment p (convolution (density a) (density a)) / moment p (density a) := by
  have hd := deficit_identity ha hp
  have he : 0 < exp (-p*a) := exp_pos _
  have hja : (1-exp (-p*a))*J p < Ja p a := by nlinarith
  have he1 : exp (-p*a) < 1 := by
    have hh : -p*a < 0 := by nlinarith
    simpa using exp_lt_exp.mpr hh
  have hja0 : 0 < Ja p a := lt_trans (mul_pos (sub_pos.mpr he1) (J_pos hp)) hja
  have hn : 1 ≤ normalizer a^p := one_le_rpow (normalizer_ge_one ha) hp.le
  have hc : (1-exp (-p*a))*J p < normalizer a^p * Ja p a :=
    hja.trans_le (le_mul_of_one_le_left hja0.le hn)
  rw [lt_div_iff₀ (density_moment_pos ha hp)]
  calc
    p*J p * moment p (density a) = normalizer a^p * ((1-exp (-p*a))*J p) := by
      rw [density_moment ha hp]
      field_simp
    _ < normalizer a^p * (normalizer a^p * Ja p a) :=
      mul_lt_mul_of_pos_left hc (rpow_pos_of_pos (normalizer_pos ha) p)
    _ = moment p (convolution (density a) (density a)) := by
      rw [convolution_moment ha hp, show 2*p=p+p by ring_nf,
        rpow_add (normalizer_pos ha)]
      ring_nf

theorem entropy_increment_ratio {p : ℝ} {f : ℝ → ℝ}
    (hi : 0 < moment p f) (ho : 0 < moment p (convolution f f)) :
    entropy p (convolution f f) - entropy p f =
      log (moment p (convolution f f) / moment p f) / (1-p) := by
  rw [entropy, entropy, log_div ho.ne' hi.ne', sub_div]

-- All analytic requirements here are facts of the literal real density.
@[expose] def Admissible (p : ℝ) (f : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ LogConcaveDensity f ∧ Integrable f ∧ (∫ x : ℝ, f x) = 1 ∧
  Integrable (fun x => (f x)^p) ∧ 0 < moment p f ∧
  (∀ s, Integrable (fun t => f t*f (s-t))) ∧
  (∀ s, 0 ≤ convolution f f s) ∧
  Integrable (fun s => (convolution f f s)^p) ∧ 0 < moment p (convolution f f)

theorem density_admissible {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    Admissible p (density a) :=
  ⟨density_nonneg ha, density_logConcave ha, density_integrable a, density_integral ha,
    density_power_integrable ha hp, density_moment_pos ha hp, convolution_integrable a,
    convolution_nonneg a, convolution_power_integrable ha hp, convolution_moment_pos ha hp⟩

theorem exponential_admissible {p : ℝ} (hp : 0 < p) : Admissible p exponential := by
  refine ⟨exponential_nonneg, exponential_logConcave, exponential_integrable,
    exponential_integral, exponential_power_integrable hp, ?_,
    exponential_convolution_integrable, exponential_convolution_nonneg,
    exponential_convolution_power_integrable hp, ?_⟩
  · rw [exponential_moment hp]; exact div_pos zero_lt_one hp
  · rw [exponential_convolution_moment hp]; exact J_pos hp

theorem every_order_counterexample {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∃ a : ℝ, 0 < a ∧ Admissible p (density a) ∧ Admissible p exponential ∧
      entropy p (convolution exponential exponential) - entropy p exponential <
        entropy p (convolution (density a) (density a)) - entropy p (density a) := by
  obtain ⟨a,ha,ht⟩ := finite_tail_cutoff hp hp1
  refine ⟨a,ha,density_admissible ha hp,exponential_admissible hp,?_⟩
  have hbi : 0 < moment p exponential := by rw [exponential_moment hp]; positivity
  have hbo : 0 < moment p (convolution exponential exponential) := by
    rw [exponential_convolution_moment hp]; exact J_pos hp
  rw [entropy_increment_ratio hbi hbo,
    entropy_increment_ratio (density_moment_pos ha hp) (convolution_moment_pos ha hp),
    exponential_ratio hp]
  apply (div_lt_div_iff_of_pos_right (sub_pos.mpr hp1)).mpr
  exact log_lt_log (mul_pos hp (J_pos hp)) (strict_ratio ha hp ht)

-- Necessary density-level consequence of Fu–Li 2510.09206v3 p.2,
-- unnumbered paragraph after (1.2). This is not Shannon Conjecture 1.1.
@[expose] def SourceThresholdConsequence : Prop :=
  ∃ p0 : ℝ, 0 < p0 ∧ p0 < 1 ∧ ∀ p : ℝ, p0 < p → p < 1 →
    ∀ f : ℝ → ℝ, Admissible p f →
      entropy p (convolution f f) - entropy p f ≤
        entropy p (convolution exponential exponential) - entropy p exponential

theorem not_source_threshold : ¬ SourceThresholdConsequence := by
  rintro ⟨p0,hp0,hp01,h⟩
  have hp : 0 < (p0+1)/2 := by linarith
  have hp1 : (p0+1)/2 < 1 := by linarith
  obtain ⟨a,_ha,had,_hb,hlt⟩ := every_order_counterexample hp hp1
  exact (not_le_of_gt hlt) (h ((p0+1)/2) (by linarith) hp1 (density a) had)
end Renyi
