import ParameterMaximum333569

namespace MathDB333569
noncomputable section
open Set Filter

def inverseParameters (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1+z.2-1,(z.1-z.2)/(2-z.1-z.2))

theorem inverseParameters_chart {l : ℝ} (hl : l ≠ 1) (t : ℝ) :
    inverseParameters (chart l t) = (l,t) := by
  have hd : 2-(chart l t).1-(chart l t).2 = 1-l := by dsimp [chart]; ring
  apply Prod.ext
  · dsimp [inverseParameters,chart]; ring
  · change ((chart l t).1-(chart l t).2)/(2-(chart l t).1-(chart l t).2) = t
    rw [hd]
    dsimp [chart]
    field_simp
    have h : 1-l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl)
    field_simp [h]
    ring

theorem source_parameter_claim_chart :
    ∃ l ∈ Ioo (0:ℝ) 1, IsLocalMaxOn sourceIntricacy interior (chart l 0) ∧
      Tendsto (finiteIntricacy (chart l 0)) atTop (nhds (sourceIntricacy (chart l 0))) := by
  obtain ⟨l,hl,hmax⟩ := entropySeries_has_local_max
  let z := chart l 0
  have hinv : inverseParameters z = (l,0) := inverseParameters_chart (ne_of_lt hl.2) 0
  have hden : 2-z.1-z.2 ≠ 0 := by
    have he : 2-z.1-z.2 = 1-l := by dsimp [z,chart]; ring
    rw [he]; linarith [hl.2]
  have hcont : ContinuousAt inverseParameters z := by
    unfold inverseParameters
    fun_prop (disch := exact hden)
  have hcomp : IsLocalMax (fun w => entropySeries (inverseParameters w).1 (inverseParameters w).2) z := by
    have hmax' : IsLocalMax (fun p : ℝ × ℝ => entropySeries p.1 p.2) (inverseParameters z) := by
      rw [hinv]; exact hmax
    exact hmax'.comp_continuous hcont
  have hparam : {w : ℝ × ℝ | 0 < w.1 ∧ w.1 < 1 ∧ -1 < w.2 ∧ w.2 < 1} ∈ nhds (l,0) := by
    have h := prod_mem_nhds (Ioo_mem_nhds hl.1 hl.2)
      (Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0) (by norm_num : (0:ℝ) < 1))
    filter_upwards [h] with w hw
    exact ⟨hw.1.1,hw.1.2,hw.2.1,hw.2.2⟩
  have heq : (fun w => entropySeries (inverseParameters w).1 (inverseParameters w).2) =ᶠ[nhds z] sourceIntricacy := by
    have hevent := hcont.eventually (hinv ▸ hparam)
    filter_upwards [hevent, (by
      have hc : ContinuousAt (fun w : ℝ × ℝ => 2-w.1-w.2) z := by fun_prop
      exact hc.eventually_ne hden : ∀ᶠ w in nhds z, 2-w.1-w.2 ≠ 0)] with w hw hd
    have hchart : chart (inverseParameters w).1 (inverseParameters w).2 = w := inverse_chart hd
    calc
      _ = sourceIntricacy (chart (inverseParameters w).1 (inverseParameters w).2) :=
        (sourceIntricacy_eq_series hw.1 hw.2.1 hw.2.2.1 hw.2.2.2).symm
      _ = _ := congrArg sourceIntricacy hchart
  refine ⟨l,hl,(hcomp.congr heq).isLocalMaxOn _,?_⟩
  rw [sourceIntricacy_eq_series hl.1 hl.2 (by norm_num) (by norm_num)]
  exact finiteIntricacy_tendsto_series hl.1 hl.2 (by norm_num) (by norm_num)


theorem source_parameter_claim : SourceClaim := by
  obtain ⟨l,hl,hmax,hconv⟩ := source_parameter_claim_chart
  exact ⟨chart l 0,chart_mem_interior hl.1 hl.2 (by norm_num) (by norm_num),hmax,hconv⟩

end
end MathDB333569
