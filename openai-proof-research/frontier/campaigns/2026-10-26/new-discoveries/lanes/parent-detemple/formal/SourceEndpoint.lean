import SourceDefs
import LogObstruction

open Filter Set
open scoped Topology ContDiff

namespace DeTemple

theorem sourceG_boundary (x : ℝ) :
    sourceG (155 / 294) x = boundaryModel sourceH (155 / 294) x + 7 / 40 - 155 / 294 := by
  unfold sourceG sourceR boundaryModel
  ring

theorem source_boundary_midpoint :
    ∃ x : ℝ, 0 < x ∧ sourceG (155 / 294) (2 * x) <
      (sourceG (155 / 294) x + sourceG (155 / 294) (3 * x)) / 2 := by
  obtain ⟨x, hx, hd⟩ := exists_boundary_midpoint sourceH sourceH_continuousAt_zero
    (by norm_num : (0 : ℝ) < 155 / 294)
  refine ⟨x, hx, ?_⟩
  simp only [sourceG_boundary]
  linarith

theorem source_interior_midpoint :
    ∃ a x : ℝ, 0 < a ∧ a < 155 / 294 ∧ 0 < x ∧
      sourceG a (2 * x) < (sourceG a x + sourceG a (3 * x)) / 2 := by
  obtain ⟨x, hx, hd⟩ := source_boundary_midpoint
  let F : ℝ → ℝ := fun a => (sourceG a x + sourceG a (3 * x)) / 2 - sourceG a (2 * x)
  have hc : ContinuousAt F (155 / 294) := by
    unfold F sourceG
    fun_prop
  have hp : 0 < F (155 / 294) := sub_pos.mpr hd
  have he : ∀ᶠ a in 𝓝 (155 / 294 : ℝ), 0 < F a :=
    hc.tendsto.eventually (Ioi_mem_nhds hp)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp he
  let r : ℝ := min (δ / 2) ((155 / 294) / 2)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hra : r ≤ (155 / 294) / 2 := min_le_right _ _
  let a : ℝ := 155 / 294 - r
  have ha : 0 < a := by dsimp [a]; linarith
  have haa : a < 155 / 294 := by dsimp [a]; linarith
  have hab : dist a (155 / 294) < δ := by
    rw [Real.dist_eq, show a - 155 / 294 = -r by dsimp [a]; ring, abs_neg,
      abs_of_pos hr]
    exact hrδ
  have hf := hball hab
  exact ⟨a, x, ha, haa, hx, sub_pos.mp hf⟩

theorem completelyMonotone_convex {f : ℝ → ℝ} (hf : SourceCompletelyMonotone f) :
    ConvexOn ℝ (Ioi (0 : ℝ)) f := by
  have h1 := (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp hf.1
  have h2 := (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp h1.2
  apply convexOn_of_deriv2_nonneg' (convex_Ioi 0) h1.1 h2.1
  intro x hx
  have hn := hf.2 2 x hx
  simpa [iteratedDeriv_eq_iterate] using hn

theorem source_interior_not_completelyMonotone :
    ∃ a : ℝ, 0 < a ∧ a < 155 / 294 ∧
      ¬ SourceCompletelyMonotone (fun x => -sourceG a x) := by
  obtain ⟨a, x, ha, haa, hx, hd⟩ := source_interior_midpoint
  refine ⟨a, ha, haa, ?_⟩
  intro hc
  have hv := completelyMonotone_convex hc
  have hh := hv.2 hx (show 0 < 3 * x by positivity)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at hh
  rw [show (1 / 2 : ℝ) * x + 1 / 2 * (3 * x) = 2 * x by ring] at hh
  linarith

theorem source_counterexample_328867ii : ¬ SourceConjecture328867ii := by
  obtain ⟨a, _ha, haa, hn⟩ := source_interior_not_completelyMonotone
  intro hc
  exact hn ((hc a).mpr haa.le)

end DeTemple
