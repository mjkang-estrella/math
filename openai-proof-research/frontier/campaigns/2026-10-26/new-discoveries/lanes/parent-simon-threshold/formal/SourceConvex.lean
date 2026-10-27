import Bounds
noncomputable section
open Set Real
namespace SimonThreshold
def envelopeSet (γ α : ℝ) : Set ℝ := (fun s => envelope γ α s) '' Ioi (0 : ℝ)
def thresholdSup (γ α : ℝ) : ℝ := sSup (envelopeSet γ α)
lemma envelopeSet_nonempty (γ α : ℝ) : (envelopeSet γ α).Nonempty :=
  ⟨envelope γ α 1, 1, by norm_num, rfl⟩
lemma envelopeSet_bddAbove {γ α : ℝ} (hγ : 0 < γ) (hα : 0 < α) (haγ : γ * α ≤ 1) :
    BddAbove (envelopeSet γ α) := by
  refine ⟨α + 1, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact envelope_upper hγ hα haγ hs
lemma envelope_le_sup {γ α s : ℝ} (hγ : 0 < γ) (hα : 0 < α) (haγ : γ * α ≤ 1)
    (hs : 0 < s) : envelope γ α s ≤ thresholdSup γ α :=
  le_csSup (envelopeSet_bddAbove hγ hα haγ) ⟨s, hs, rfl⟩
lemma thresholdSup_pos {γ α : ℝ} (hγ : 1 < γ) (hα : 0 < α) (haγ : γ * α ≤ 1) :
    0 < thresholdSup γ α := by
  obtain ⟨s, hs, hb⟩ := exists_envelope_gt hγ hα
  exact hα.trans (hb.trans_le (envelope_le_sup (by linarith) hα haγ hs))
lemma thresholdSup_criterion {γ α : ℝ} (hγ : 0 < γ) (hα : 0 < α) (haγ : γ * α ≤ 1) :
    SourceCriterion γ α (thresholdSup γ α) := by
  rw [criterion_envelope_iff hγ hα]
  exact fun _ hs => envelope_le_sup hγ hα haγ hs
lemma sourceThreshold_eq_sup {γ α : ℝ} (hγ : 1 < γ) (hα : 0 < α) (haγ : γ * α ≤ 1) :
    sourceThreshold γ α = thresholdSup γ α := by
  have hg : 0 < γ := by linarith
  have hmem : thresholdSup γ α ∈ {β : ℝ | 0 < β ∧ SourceCriterion γ α β} :=
    ⟨thresholdSup_pos hγ hα haγ, thresholdSup_criterion hg hα haγ⟩
  apply le_antisymm
  · exact csInf_le ⟨0, fun _ hb => hb.1.le⟩ hmem
  · apply le_csInf ⟨_, hmem⟩
    intro β hβ
    apply csSup_le (envelopeSet_nonempty γ α)
    rintro _ ⟨s, hs, rfl⟩
    exact (criterion_envelope_iff hg hα).mp hβ.2 s hs
/-- The literal source threshold's convexity, with no residual optimizer or regularity premise.
The different main complete-monotonicity conjecture is not asserted. -/
theorem source_threshold_convex {γ : ℝ} (hγ : 1 < γ) :
    ConvexOn ℝ (Ioo (0 : ℝ) (1 / γ)) (sourceThreshold γ) := by
  have hg : 0 < γ := by linarith
  have hprod : ∀ a ∈ Ioo (0 : ℝ) (1 / γ), γ * a ≤ 1 := by
    intro a ha
    have hh := (lt_div_iff₀ hg).mp ha.2
    nlinarith
  refine ⟨convex_Ioo 0 (1 / γ), ?_⟩
  intro x hx y hy a b ha hb hab
  have hc := (convex_Ioo (0 : ℝ) (1 / γ)) hx hy ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  rw [sourceThreshold_eq_sup hγ hc.1 (hprod _ hc),
    sourceThreshold_eq_sup hγ hx.1 (hprod _ hx),
    sourceThreshold_eq_sup hγ hy.1 (hprod _ hy)]
  apply csSup_le (envelopeSet_nonempty γ _)
  rintro _ ⟨s, hs, rfl⟩
  have hh := (envelope_convex γ hs).2 hx.1 hy.1 ha hb hab
  simp only [smul_eq_mul] at hh
  exact hh.trans (add_le_add
    (mul_le_mul_of_nonneg_left (envelope_le_sup hg hx.1 (hprod _ hx) hs) ha)
    (mul_le_mul_of_nonneg_left (envelope_le_sup hg hy.1 (hprod _ hy) hs) hb))
end SimonThreshold
