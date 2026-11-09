import TransverseEntropy333569
import Mathlib.Analysis.Calculus.SmoothSeries

namespace MathDB333569
noncomputable section
open Set

def seriesSlope (l t : ℝ) : ℝ :=
  (∑' n : ℕ, (1/2:ℝ)^(n+1)*entropySlope (l^(n+1)) t)-entropySlope l t

def seriesCurvature (l t : ℝ) : ℝ :=
  (∑' n : ℕ, (1/2:ℝ)^(n+1)*entropyCurvature (l^(n+1)) t)-entropyCurvature l t

theorem geometricBound_summable (C : ℝ) :
    Summable (fun n : ℕ => (1/2:ℝ)^(n+1)*C) := by
  have h : Summable (fun n : ℕ => (1/2:ℝ)^n) := summable_geometric_of_norm_lt_one (by norm_num)
  simpa only [pow_succ, mul_assoc] using (h.mul_right (1/2)).mul_right C

/-- Two successive termwise differentiations on every fixed transverse interval
strictly inside the chart. The derivative bounds are proved, not assumed. -/
theorem entropySeries_hasDerivAt {l δ t : ℝ} (hl : 0 ≤ l) (hl1 : l < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (ht : t ∈ Ioo (-δ) δ) :
    HasDerivAt (entropySeries l) (seriesSlope l t) t ∧
      HasDerivAt (seriesSlope l) (seriesCurvature l t) t := by
  obtain ⟨C₁,C₂,hC₁,hC₂⟩ := entropy_transverse_uniform_bounds hl hl1 hδ hδ1
  have hp (n : ℕ) : l^(n+1) ∈ Icc (0:ℝ) l :=
    ⟨pow_nonneg hl _, pow_le_base ⟨hl,hl1.le⟩ n⟩
  have hD₁ (n : ℕ) (y : ℝ) (hy : y ∈ Ioo (-δ) δ) :
      HasDerivAt (fun y => (1/2:ℝ)^(n+1)*conditionalEntropy (l^(n+1)) y)
        ((1/2:ℝ)^(n+1)*entropySlope (l^(n+1)) y) y :=
    (conditionalEntropy_hasDerivAt (hp n).1 (lt_of_le_of_lt (hp n).2 hl1)
      (by linarith [hy.1]) (by linarith [hy.2])).const_mul _
  have hD₂ (n : ℕ) (y : ℝ) (hy : y ∈ Ioo (-δ) δ) :
      HasDerivAt (fun y => (1/2:ℝ)^(n+1)*entropySlope (l^(n+1)) y)
        ((1/2:ℝ)^(n+1)*entropyCurvature (l^(n+1)) y) y :=
    (entropySlope_hasDerivAt (hp n).1 (lt_of_le_of_lt (hp n).2 hl1)
      (by linarith [hy.1]) (by linarith [hy.2])).const_mul _
  have hB₁ (n : ℕ) (y : ℝ) (hy : y ∈ Ioo (-δ) δ) :
      ‖(1/2:ℝ)^(n+1)*entropySlope (l^(n+1)) y‖ ≤ (1/2:ℝ)^(n+1)*C₁ := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hC₁ _ (hp n) y ⟨hy.1.le,hy.2.le⟩) (by positivity)
  have hB₂ (n : ℕ) (y : ℝ) (hy : y ∈ Ioo (-δ) δ) :
      ‖(1/2:ℝ)^(n+1)*entropyCurvature (l^(n+1)) y‖ ≤ (1/2:ℝ)^(n+1)*C₂ := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hC₂ _ (hp n) y ⟨hy.1.le,hy.2.le⟩) (by positivity)
  have hzero : (0:ℝ) ∈ Ioo (-δ) δ := ⟨by linarith,hδ⟩
  have h₁ := hasDerivAt_tsum_of_isPreconnected (geometricBound_summable C₁) isOpen_Ioo
    (convex_Ioo (-δ) δ).isPreconnected hD₁ hB₁ hzero
    (conditionalEntropySeries_summable ⟨hl,hl1.le⟩ (by constructor <;> norm_num)) ht
  have h₂ := hasDerivAt_tsum_of_isPreconnected (geometricBound_summable C₂) isOpen_Ioo
    (convex_Ioo (-δ) δ).isPreconnected hD₂ hB₂ hzero
    (by simp [entropySlope_zero] : Summable (fun n : ℕ => (1/2:ℝ)^(n+1)*entropySlope (l^(n+1)) 0)) ht
  exact ⟨h₁.sub (conditionalEntropy_hasDerivAt hl hl1 (by linarith [ht.1]) (by linarith [ht.2])),
    h₂.sub (entropySlope_hasDerivAt hl hl1 (by linarith [ht.1]) (by linarith [ht.2]))⟩

theorem seriesCurvature_zero {l : ℝ} (hl : 0 ≤ l) (hl1 : l < 1) :
    seriesCurvature l 0 = 2 * (∑' n : ℕ, (1/2:ℝ)^(n+1)*transverseCoeff (l^(n+1)) - transverseCoeff l) := by
  unfold seriesCurvature
  have hp (n : ℕ) : entropyCurvature (l^(n+1)) 0 = 2*transverseCoeff (l^(n+1)) :=
    entropyCurvature_zero (pow_nonneg hl _) (pow_lt_one₀ hl hl1 (by omega))
  simp_rw [hp, entropyCurvature_zero hl hl1]
  simp_rw [show ∀ n : ℕ, (1/2:ℝ)^(n+1)*(2*transverseCoeff (l^(n+1))) =
    2*((1/2:ℝ)^(n+1)*transverseCoeff (l^(n+1))) by intro n; ring]
  rw [tsum_mul_left]
  ring


theorem geometricWeight_sum : (∑' n : ℕ, (1/2:ℝ)^(n+1)) = 1 := by
  have h := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).mul_right (1/2:ℝ)
  have he : (1-(1/2:ℝ))⁻¹ * (1/2:ℝ) = 1 := by norm_num
  simpa only [pow_succ, he] using h.tsum_eq

theorem seriesCurvature_zero_neg {l : ℝ} (hl : 0 < l) (hl1 : l < 1) :
    seriesCurvature l 0 < 0 := by
  have hconst := geometricBound_summable (transverseCoeff l)
  have hraw : Summable (fun n : ℕ => (1/2:ℝ)^(n+1)*transverseCoeff (l^(n+1))) := by
    convert (coefficientTerm_summable ⟨hl,hl1⟩).add hconst using 1
    funext n
    simp only [coefficientTerm]
    ring
  have he : (∑' n, coefficientTerm l n) =
      (∑' n : ℕ, (1/2:ℝ)^(n+1)*transverseCoeff (l^(n+1))) - transverseCoeff l := by
    rw [show coefficientTerm l = (fun n : ℕ => (1/2:ℝ)^(n+1)*transverseCoeff (l^(n+1)) -
      (1/2:ℝ)^(n+1)*transverseCoeff l) by funext n; dsimp [coefficientTerm]; ring]
    rw [Summable.tsum_sub hraw hconst, tsum_mul_right, geometricWeight_sum, one_mul]
  rw [seriesCurvature_zero hl.le hl1, ← he]
  exact mul_neg_of_pos_of_neg (by norm_num) (coefficientSeries_neg ⟨hl,hl1⟩)

/-- Joint continuity of the second transverse derivative series on a rectangle;
this includes the uniform gap estimates needed for analytic promotion. -/
theorem seriesCurvature_continuousOn {b δ : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ContinuousOn (fun z : ℝ × ℝ => seriesCurvature z.1 z.2)
      (Icc (0:ℝ) b ×ˢ Icc (-δ) δ) := by
  obtain ⟨C₁,C₂,hC₁,hC₂⟩ := entropy_transverse_uniform_bounds hb hb1 hδ hδ1
  have hp (z : ℝ × ℝ) (hz : z ∈ Icc (0:ℝ) b ×ˢ Icc (-δ) δ) (n : ℕ) :
      z.1^(n+1) ∈ Icc (0:ℝ) b :=
    ⟨pow_nonneg hz.1.1 _, (pow_le_base ⟨hz.1.1,hz.1.2.trans hb1.le⟩ n).trans hz.1.2⟩
  have hsum : ContinuousOn (fun z : ℝ × ℝ =>
      ∑' n : ℕ, (1/2:ℝ)^(n+1)*entropyCurvature (z.1^(n+1)) z.2)
      (Icc (0:ℝ) b ×ˢ Icc (-δ) δ) := by
    apply continuousOn_tsum (u := fun n : ℕ => (1/2:ℝ)^(n+1)*C₂)
    · intro n z hz
      apply ContinuousWithinAt.const_mul
      apply ContinuousAt.continuousWithinAt
      exact (entropyCurvature_continuousAt (r := z.1^(n+1)) (t := z.2) (hp z hz n).1 (lt_of_le_of_lt (hp z hz n).2 hb1)
        (by linarith [hz.2.1]) (by linarith [hz.2.2])).comp (f := fun w : ℝ × ℝ => (w.1^(n+1),w.2)) (x := z)
          (by fun_prop : ContinuousAt (fun w : ℝ × ℝ => (w.1^(n+1),w.2)) z)
    · exact geometricBound_summable C₂
    · intro n z hz
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hC₂ _ (hp z hz n) _ hz.2) (by positivity)
  apply hsum.sub
  intro z hz
  exact (entropyCurvature_continuousAt hz.1.1 (lt_of_le_of_lt hz.1.2 hb1)
    (by linarith [hz.2.1]) (by linarith [hz.2.2])).continuousWithinAt


theorem entropySeries_second_derivative {l δ t : ℝ} (hl : 0 ≤ l) (hl1 : l < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (ht : t ∈ Ioo (-δ) δ) :
    HasDerivAt (fun y => deriv (entropySeries l) y) (seriesCurvature l t) t := by
  have he : (fun y => deriv (entropySeries l) y) =ᶠ[nhds t] seriesSlope l := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with y hy
    exact (entropySeries_hasDerivAt hl hl1 hδ hδ1 hy).1.deriv
  exact (entropySeries_hasDerivAt hl hl1 hδ hδ1 ht).2.congr_of_eventuallyEq he

theorem entropySeries_second_derivative_zero_neg {l : ℝ} (hl : 0 < l) (hl1 : l < 1) :
    deriv (fun t => deriv (entropySeries l) t) 0 < 0 := by
  rw [(entropySeries_second_derivative hl.le hl1 (δ := 1/2)
    (by norm_num) (by norm_num) (by constructor <;> norm_num)).deriv]
  exact seriesCurvature_zero_neg hl hl1

end
end MathDB333569
