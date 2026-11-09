import SeriesDerivatives333569
import Mathlib.Analysis.Convex.Deriv

namespace MathDB333569
noncomputable section
open Set Filter

theorem entropySeries_even (l t : ℝ) : entropySeries l (-t) = entropySeries l t := by
  simp only [entropySeries, conditionalEntropy_even]

theorem entropySeries_diagonal {l : ℝ} (hl : l ∈ Icc 0 1) :
    entropySeries l 0 = diagonal l := by
  have hr := conditionalEntropySeries_summable hl (t := 0) (by constructor <;> norm_num)
  simp only [conditionalEntropy_zero] at hr
  unfold entropySeries diagonal
  simp only [conditionalEntropy_zero]
  rw [show diagonalTerm l = (fun n : ℕ => (1/2:ℝ)^(n+1)*gapEntropy (l^(n+1)) -
      (1/2:ℝ)^(n+1)*gapEntropy l) by funext n; dsimp [diagonalTerm]; ring]
  rw [Summable.tsum_sub hr (geometricBound_summable (gapEntropy l)),
    tsum_mul_right, geometricWeight_sum, one_mul]

theorem entropySeries_slice_max {l δ t : ℝ} (hl : 0 ≤ l) (hl1 : l < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (ht : t ∈ Ioo (-δ) δ)
    (hcurv : ∀ y ∈ Ioo (-δ) δ, seriesCurvature l y ≤ 0) :
    entropySeries l t ≤ entropySeries l 0 := by
  have hc : ConcaveOn ℝ (Ioo (-δ) δ) (entropySeries l) := by
    apply concaveOn_of_deriv2_nonpos' (convex_Ioo (-δ) δ)
    · intro y hy
      exact (entropySeries_hasDerivAt hl hl1 hδ hδ1 hy).1.differentiableAt.differentiableWithinAt
    · intro y hy
      exact (entropySeries_second_derivative hl hl1 hδ hδ1 hy).differentiableAt.differentiableWithinAt
    · intro y hy
      change deriv (fun x => deriv (entropySeries l) x) y ≤ 0
      rw [(entropySeries_second_derivative hl hl1 hδ hδ1 hy).deriv]
      exact hcurv y hy
  have hneg : -t ∈ Ioo (-δ) δ := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have h := hc.2 ht hneg (show 0 ≤ (1/2:ℝ) by norm_num)
    (show 0 ≤ (1/2:ℝ) by norm_num) (by norm_num : (1/2:ℝ)+(1/2:ℝ)=1)
  have he : (1/2:ℝ) • t + (1/2:ℝ) • (-t) = 0 := by simp [smul_eq_mul]
  rw [he,entropySeries_even] at h
  simp only [smul_eq_mul] at h
  linarith

/-- A full two-dimensional local maximum of the entropy series, not merely
maximality restricted to the symmetric line. The measure-topology transfer is
not asserted by this parameter-space theorem. -/
theorem entropySeries_has_local_max :
    ∃ l ∈ Ioo (0:ℝ) 1, IsLocalMax (fun z : ℝ × ℝ => entropySeries z.1 z.2) (l,0) := by
  obtain ⟨l,hl,hm⟩ := diagonal_has_interior_max
  let b := (l+1)/2
  have hb : 0 ≤ b := by dsimp [b]; linarith [hl.1]
  have hb1 : b < 1 := by dsimp [b]; linarith [hl.2]
  have hlb : l < b := by dsimp [b]; linarith [hl.2]
  have hcont : ContinuousAt (fun z : ℝ × ℝ => seriesCurvature z.1 z.2) (l,0) :=
    (seriesCurvature_continuousOn hb hb1 (δ := 1/2) (by norm_num) (by norm_num)).continuousAt
      (prod_mem_nhds (Icc_mem_nhds hl.1 hlb) (Icc_mem_nhds (by norm_num) (by norm_num)))
  have hnegative : {z : ℝ × ℝ | seriesCurvature z.1 z.2 < 0} ∈ nhds (l,0) :=
    hcont.preimage_mem_nhds (isOpen_Iio.mem_nhds (seriesCurvature_zero_neg hl.1 hl.2))
  have hchart : Ioo (0:ℝ) 1 ×ˢ Ioo (-(1/2:ℝ)) (1/2) ∈ nhds (l,0) :=
    prod_mem_nhds (Ioo_mem_nhds hl.1 hl.2) (Ioo_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp (inter_mem hnegative hchart)
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp hV
  let δ := min ε (1/2:ℝ)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hVδ (y : ℝ) (hy : y ∈ Ioo (-δ) δ) : y ∈ V := by
    apply hεV
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨lt_of_le_of_lt (by dsimp [δ]; linarith [min_le_left ε (1/2:ℝ)]) hy.1,
      lt_of_lt_of_le hy.2 (min_le_left _ _)⟩
  have hV0 : (0:ℝ) ∈ V := mem_of_mem_nhds hV
  refine ⟨l,hl,?_⟩
  change ∀ᶠ z : ℝ × ℝ in nhds (l,0), entropySeries z.1 z.2 ≤ entropySeries l 0
  filter_upwards [prod_mem_nhds hU (Ioo_mem_nhds (by linarith : -δ < 0) hδ)] with z hz
  have hzchart := (hUV (show (z.1,(0:ℝ)) ∈ U ×ˢ V from ⟨hz.1,hV0⟩)).2.1
  have hslice := entropySeries_slice_max hzchart.1.le hzchart.2 hδ hδ1 hz.2
    (fun y hy => (hUV (show (z.1,y) ∈ U ×ˢ V from ⟨hz.1,hVδ y hy⟩)).1.le)
  apply hslice.trans
  rw [entropySeries_diagonal ⟨hzchart.1.le,hzchart.2.le⟩,entropySeries_diagonal ⟨hl.1.le,hl.2.le⟩]
  exact hm _ ⟨hzchart.1.le,hzchart.2.le⟩

end
end MathDB333569
