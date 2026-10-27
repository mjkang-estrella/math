import Normalization

namespace PermanentalThree

noncomputable def upperFamily (t : ℝ) : Mat3 :=
  !![1,1,1; 1,2,t+2; 1,t+2,t^2+2*t+3]

noncomputable def lowerFamily (e : ℝ) : Mat3 :=
  !![1,1,1; 1,1+e,1+2*e; 1,1+2*e,1+5*e]

theorem upperFamily_tp {t : ℝ} (ht : 0 < t) : StrictTP3 (upperFamily t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [upperFamily] <;> positivity
  · intro i j k l hij hkl
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [upperFamily] at * <;> nlinarith [sq_nonneg t]
  · norm_num [upperFamily, Matrix.det_fin_three]
    ring_nf
    norm_num

theorem lowerFamily_tp {e : ℝ} (he : 0 < e) : StrictTP3 (lowerFamily e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [lowerFamily] <;> positivity
  · intro i j k l hij hkl
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [lowerFamily] at * <;> nlinarith [sq_pos_of_pos he]
  · norm_num [lowerFamily, Matrix.det_fin_three]
    nlinarith [sq_pos_of_pos he]

theorem upperFamily_ratio (t : ℝ) :
    ratio (upperFamily t) = (9*t^2+24*t+30)/(8*t^2+24*t+38) := by
  unfold ratio numerator denominator per2 per3 upperFamily
  norm_num
  congr 1 <;> ring

theorem lowerFamily_ratio (e : ℝ) :
    ratio (lowerFamily e) =
      (2+e)*(2+10*e+9*e^2)/((1+e)*(6+20*e+9*e^2)) := by
  unfold ratio numerator denominator per2 per3 lowerFamily
  norm_num
  congr 1 <;> ring

open Filter Topology

theorem lower_ratio_tendsto :
    Tendsto (fun e : ℝ => ratio (lowerFamily e)) (𝓝[>] 0) (𝓝 ((2:ℝ)/3)) := by
  simp_rw [lowerFamily_ratio]
  have hc : ContinuousAt (fun e : ℝ =>
      (2+e)*(2+10*e+9*e^2)/((1+e)*(6+20*e+9*e^2))) 0 := by
    fun_prop (disch := norm_num)
  convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1; norm_num

theorem upper_rescaled_ratio {s : ℝ} (hs : 0 < s) :
    ratio (upperFamily s⁻¹) = (9+24*s+30*s^2)/(8+24*s+38*s^2) := by
  rw [upperFamily_ratio]
  have hD : 0 < 8*(s⁻¹)^2+24*s⁻¹+38 := by positivity
  have hD' : 0 < 8+24*s+38*s^2 := by positivity
  apply (div_eq_div_iff (ne_of_gt hD) (ne_of_gt hD')).2
  field_simp

theorem lower_approach {c : ℝ} (hc : (2:ℝ)/3 < c) :
    ∃ A : Mat3, StrictTP3 A ∧ ratio A < c := by
  have he := (tendsto_order.1 lower_ratio_tendsto).2 c hc
  have hex : ∀ᶠ e in 𝓝[>] (0:ℝ), 0 < e ∧ ratio (lowerFamily e) < c := by
    filter_upwards [he, self_mem_nhdsWithin] with e her hep
    exact ⟨hep, her⟩
  obtain ⟨e, hep, her⟩ := hex.exists
  exact ⟨lowerFamily e, lowerFamily_tp hep, her⟩

theorem upper_approach {c : ℝ} (hc : c < (9:ℝ)/8) :
    ∃ A : Mat3, StrictTP3 A ∧ c < ratio A := by
  have hcont : ContinuousAt (fun s : ℝ =>
      (9+24*s+30*s^2)/(8+24*s+38*s^2)) 0 := by
    fun_prop (disch := norm_num)
  have ht : Tendsto (fun s : ℝ => (9+24*s+30*s^2)/(8+24*s+38*s^2))
      (𝓝[>] 0) (𝓝 ((9:ℝ)/8)) := by
    convert hcont.tendsto.mono_left nhdsWithin_le_nhds using 1; norm_num
  have he := (tendsto_order.1 ht).1 c hc
  have hex : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s ∧ c < ratio (upperFamily s⁻¹) := by
    filter_upwards [he, self_mem_nhdsWithin] with s her hsp
    exact ⟨hsp, (upper_rescaled_ratio hsp).symm ▸ her⟩
  obtain ⟨s, hsp, her⟩ := hex.exists
  exact ⟨upperFamily s⁻¹, upperFamily_tp (inv_pos.mpr hsp), her⟩

end PermanentalThree
