module
public import Result
public section
set_option autoImplicit false
set_option warningAsError true
open Real MeasureTheory Set
namespace Renyi
@[expose] noncomputable def Ja (p a : ℝ) : ℝ :=
  ∫ s in Ioi (0:ℝ), exp (-p*s) * (tent a s)^p

theorem profile_integrable {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    Integrable (fun s => exp (-p*s) * (tent a s)^p) := by
  have he : (fun s => exp (-p*s) * (tent a s)^p) =
      (Icc 0 (2*a)).indicator (fun s => exp (-p*s) * (tent a s)^p) := by
    funext s
    by_cases hs : s ∈ Icc 0 (2*a)
    · simp [hs]
    · simp [hs, tent_zero_off ha hs, zero_rpow hp.ne']
  rw [he]
  apply IntegrableOn.integrable_indicator _ measurableSet_Icc
  apply Continuous.integrableOn_Icc
  have hp0 := hp.le
  unfold tent
  fun_prop

theorem convolution_power_profile {a p : ℝ} (ha : 0 < a) (s : ℝ) :
    (convolution (density a) (density a) s)^p =
      (normalizer a)^(2*p) * (exp (-p*s) * (tent a s)^p) := by
  rw [convolution_tent, mul_rpow (show 0 ≤ tent a s from le_max_right _ _) (mul_nonneg (sq_nonneg _) (exp_pos _).le),
    mul_rpow (sq_nonneg _) (exp_pos _).le, ← rpow_natCast_mul (normalizer_pos ha).le,
    ← exp_mul]
  rw [show -s*p = -p*s by ring_nf]
  ring_nf

theorem profile_integral {a p : ℝ} (_ha : 0 < a) (hp : 0 < p) :
    (∫ s : ℝ, exp (-p*s) * (tent a s)^p) = Ja p a := by
  rw [Ja, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  by_cases hs : s ∈ Ioi (0:ℝ)
  · simp [hs]
  · have ht : tent a s = 0 := by
      unfold tent
      apply max_eq_right
      have h1 := min_le_right a s
      have h2 := le_max_left (0:ℝ) (s-a)
      have h3 : s ≤ 0 := le_of_not_gt hs
      linarith
    simp [hs, ht, zero_rpow hp.ne']

theorem convolution_moment {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    moment p (convolution (density a) (density a)) = normalizer a^(2*p) * Ja p a := by
  unfold moment
  simp_rw [convolution_power_profile ha]
  rw [integral_const_mul, profile_integral ha hp]

theorem shift_Ioi (f : ℝ → ℝ) (a : ℝ) :
    (∫ s in Ioi a, f s) = ∫ u in Ioi (0:ℝ), f (a+u) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_left_eq_self ((Ioi a).indicator f) a]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  by_cases hu : 0 < u
  · simp [hu, show a < a+u by linarith]
  · simp [hu, show ¬ a < a+u by linarith]

theorem deficit_identity {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    J p - Ja p a = exp (-p*a) * tail p a := by
  rw [J, Ja, ← integral_sub (moment_integrable hp) (profile_integrable ha hp).integrableOn]
  have hs : (∫ s in Ioi (0:ℝ), exp (-p*s)*s^p - exp (-p*s)*(tent a s)^p) =
      ∫ s in Ioi a, exp (-p*s)*s^p - exp (-p*s)*(tent a s)^p := by
    apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
      (Ioi_subset_Ioi ha.le)
    apply Filter.Eventually.of_forall
    intro s hs
    have hsa : s ≤ a := le_of_not_gt hs.2
    rw [tent_first ⟨hs.1.le,hsa⟩, sub_self]
  rw [hs, shift_Ioi, tail, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  have hu0 : 0 < u := hu
  have ht : tent a (a+u) = max (a-u) 0 := by
    unfold tent
    rw [min_eq_left (by linarith : a ≤ a+u),
      max_eq_right (by linarith : 0 ≤ a+u-a)]
    congr 1
    ring_nf
  rw [ht, bracket, show -p*(a+u) = -p*a + -p*u by ring_nf, exp_add]
  ring_nf
end Renyi
