import Envelope
noncomputable section
open Set Real Filter
open scoped Topology
namespace SimonThreshold
lemma envelope_rescale (γ : ℝ) {α t : ℝ} (hα : 0 < α) (ht : 0 < t) :
    envelope γ α (α * t) =
      α + (log γ + log (1 - exp (-α * t)) - log (1 - exp (-t))) / t := by
  have hr : α * t / α = t := mul_div_cancel_left₀ t (ne_of_gt hα)
  simp only [envelope, kernel, hr]
  field_simp [ne_of_gt hα, ne_of_gt ht]
  ring
lemma criterion_envelope_iff {γ α β : ℝ} (hγ : 0 < γ) (hα : 0 < α) :
    SourceCriterion γ α β ↔ ∀ s : ℝ, 0 < s → envelope γ α s ≤ β := by
  rw [criterion_exp_iff]
  constructor
  · intro h s hs
    have ht := div_pos hs hα
    have hh := (exp_constraint_iff hγ hα ht).mp (h (s / α) ht)
    rw [← envelope_rescale γ hα ht] at hh
    simpa only [mul_div_cancel₀ s (ne_of_gt hα)] using hh
  · intro h t ht
    apply (exp_constraint_iff hγ hα ht).mpr
    rw [← envelope_rescale γ hα ht]
    exact h (α * t) (mul_pos hα ht)
lemma criterion_simple_bound {γ α : ℝ} (hγ : 0 < γ) (_hα : 0 < α) (haγ : γ * α ≤ 1) :
    SourceCriterion γ α (α + 1) := by
  rw [criterion_exp_iff]
  intro t ht
  have ha : 1 - exp (-α * t) ≤ α * t := by
    have hh := add_one_le_exp (-α * t)
    linarith
  have hb : t * exp (-t) ≤ 1 - exp (-t) := by
    have hh := mul_le_mul_of_nonneg_right (add_one_le_exp t) (exp_pos (-t)).le
    rw [add_mul, one_mul, ← exp_add, add_neg_cancel, exp_zero] at hh
    linarith
  have ht0 : 0 ≤ t * exp (-t) := mul_nonneg ht.le (exp_pos _).le
  have hm := mul_le_mul_of_nonneg_right haγ ht0
  have hm2 := mul_le_mul_of_nonneg_left ha (mul_nonneg hγ.le (exp_pos (-t)).le)
  have he : -(α + 1 - α) * t = -t := by ring
  rw [he]
  nlinarith
lemma envelope_upper {γ α s : ℝ} (hγ : 0 < γ) (hα : 0 < α) (haγ : γ * α ≤ 1)
    (hs : 0 < s) : envelope γ α s ≤ α + 1 :=
  (criterion_envelope_iff hγ hα).mp (criterion_simple_bound hγ hα haγ) s hs
lemma kernel_pos {t : ℝ} (ht : 0 < t) : 0 < kernel t := by
  have he : exp (-t) < 1 := exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  exact neg_pos.mpr (log_neg (sub_pos.mpr he) (by linarith [exp_pos (-t)]))
lemma kernel_tendsto : Tendsto kernel atTop (nhds 0) := by
  have hh := (tendsto_const_nhds.sub tendsto_exp_neg_atTop_nhds_zero).log (by norm_num : (1 : ℝ) - 0 ≠ 0)
  change Tendsto (fun t : ℝ => -log (1 - exp (-t))) atTop (nhds 0)
  simpa using hh.neg
lemma exists_envelope_gt {γ α : ℝ} (hγ : 1 < γ) (hα : 0 < α) :
    ∃ s : ℝ, 0 < s ∧ α < envelope γ α s := by
  have hlog := log_pos hγ
  have hh := kernel_tendsto.eventually (gt_mem_nhds hlog)
  obtain ⟨s, hs, hk⟩ := ((eventually_gt_atTop (0 : ℝ)).and hh).exists
  refine ⟨s, hs, ?_⟩
  have hk2 := kernel_pos (div_pos hs hα)
  dsimp [envelope]
  have hp : 0 < α / s * (log γ - kernel s + kernel (s / α)) :=
    mul_pos (div_pos hα hs) (by linarith)
  linarith
end SimonThreshold
