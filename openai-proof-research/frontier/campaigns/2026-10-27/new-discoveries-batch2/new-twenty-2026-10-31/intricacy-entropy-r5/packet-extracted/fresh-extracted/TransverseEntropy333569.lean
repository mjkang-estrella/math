import EntropyLimit333569
import SeriesCurvature333569

namespace MathDB333569
noncomputable section
open Set Filter

def binarySlope (x : ℝ) : ℝ := Real.log (1-x)-Real.log x
def binaryCurvature (x : ℝ) : ℝ := -1/(1-x)-1/x

theorem binarySlope_hasDerivAt {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    HasDerivAt binarySlope (binaryCurvature x) x := by
  convert ((((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).log
    (sub_ne_zero.mpr (Ne.symm h1))).sub ((hasDerivAt_id x).log h0)) using 1 <;>
    first | rfl | (dsimp [binaryCurvature]; ring)

def entropySlope (r t : ℝ) : ℝ :=
  (Real.binEntropy ((1-r)/2*(1-t))-Real.binEntropy ((1-r)/2*(1+t)))/2 +
  (1-r)/2 * ((1-t)/2*binarySlope ((1-r)/2*(1+t)) -
    (1+t)/2*binarySlope ((1-r)/2*(1-t)))

def entropyCurvature (r t : ℝ) : ℝ :=
  -(1-r)/2*(binarySlope ((1-r)/2*(1-t))+binarySlope ((1-r)/2*(1+t))) +
  ((1-r)/2)^2 * ((1+t)/2*binaryCurvature ((1-r)/2*(1-t)) +
    (1-t)/2*binaryCurvature ((1-r)/2*(1+t)))

theorem entropyArgs_interior {r t : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (ht : -1 < t) (ht1 : t < 1) :
    (1-r)/2*(1-t) ∈ Ioo (0:ℝ) 1 ∧ (1-r)/2*(1+t) ∈ Ioo (0:ℝ) 1 := by
  have hx : 0 < (1-r)/2 := by linarith
  constructor
  · constructor
    · exact mul_pos hx (by linarith)
    · nlinarith [mul_nonneg hr (by linarith : 0 ≤ 1-t)]
  · constructor
    · exact mul_pos hx (by linarith)
    · nlinarith [mul_nonneg hr (by linarith : 0 ≤ 1+t)]

theorem conditionalEntropy_hasDerivAt {r t : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (ht : -1 < t) (ht1 : t < 1) :
    HasDerivAt (conditionalEntropy r) (entropySlope r t) t := by
  obtain ⟨hu,hv⟩ := entropyArgs_interior hr hr1 ht ht1
  have hd₁ := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).const_mul ((1-r)/2))
  have hd₂ := (((hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)).const_mul ((1-r)/2))
  have hh₁ := (Real.hasDerivAt_binEntropy (ne_of_gt hu.1) (ne_of_lt hu.2)).comp t hd₁
  have hh₂ := (Real.hasDerivAt_binEntropy (ne_of_gt hv.1) (ne_of_lt hv.2)).comp t hd₂
  have hleft := (((hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)).div_const 2).mul hh₁
  have hright := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).div_const 2).mul hh₂
  convert hleft.add hright using 1
  · rfl
  · dsimp [entropySlope,binarySlope]
    ring

theorem entropySlope_hasDerivAt {r t : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (ht : -1 < t) (ht1 : t < 1) :
    HasDerivAt (entropySlope r) (entropyCurvature r t) t := by
  obtain ⟨hu,hv⟩ := entropyArgs_interior hr hr1 ht ht1
  have hd₁ := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).const_mul ((1-r)/2))
  have hd₂ := (((hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)).const_mul ((1-r)/2))
  have hh₁ := (Real.hasDerivAt_binEntropy (ne_of_gt hu.1) (ne_of_lt hu.2)).comp t hd₁
  have hh₂ := (Real.hasDerivAt_binEntropy (ne_of_gt hv.1) (ne_of_lt hv.2)).comp t hd₂
  have hb₁ := (binarySlope_hasDerivAt (ne_of_gt hu.1) (ne_of_lt hu.2)).comp t hd₁
  have hb₂ := (binarySlope_hasDerivAt (ne_of_gt hv.1) (ne_of_lt hv.2)).comp t hd₂
  have hleft := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).div_const 2).mul hb₂
  have hright := (((hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)).div_const 2).mul hb₁
  convert ((hh₁.sub hh₂).div_const 2).add ((hleft.sub hright).const_mul ((1-r)/2)) using 1
  · rfl
  · dsimp [entropyCurvature,binarySlope]
    ring

theorem entropySlope_zero (r : ℝ) : entropySlope r 0 = 0 := by
  simp [entropySlope]

theorem entropyCurvature_zero {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    entropyCurvature r 0 = 2 * transverseCoeff r := by
  have hp : 1+r ≠ 0 := by linarith
  have hm : 1-r ≠ 0 := by linarith
  have he : 1-(1-r)/2 = (1+r)/2 := by ring
  simp only [entropyCurvature, add_zero, sub_zero, mul_one, binarySlope, binaryCurvature, he,
    transverseCoeff, logOdds]
  rw [Real.log_div hp (by norm_num : (2:ℝ) ≠ 0),
    Real.log_div hm (by norm_num : (2:ℝ) ≠ 0)]
  field_simp
  ring

/-- The actual second transverse derivative, not just a formal coefficient. -/
theorem conditionalEntropy_second_derivative_zero {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    HasDerivAt (fun t => deriv (conditionalEntropy r) t) (2 * transverseCoeff r) 0 := by
  have he : (fun t => deriv (conditionalEntropy r) t) =ᶠ[nhds 0] entropySlope r := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0) (by norm_num : (0:ℝ) < 1)] with t ht
    exact (conditionalEntropy_hasDerivAt hr hr1 ht.1 ht.2).deriv
  rw [← entropyCurvature_zero hr hr1]
  exact (entropySlope_hasDerivAt hr hr1 (by norm_num) (by norm_num)).congr_of_eventuallyEq he


theorem entropySlope_continuousAt {r t : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (ht : -1 < t) (ht1 : t < 1) :
    ContinuousAt (fun z : ℝ × ℝ => entropySlope z.1 z.2) (r,t) := by
  obtain ⟨hu,hv⟩ := entropyArgs_interior hr hr1 ht ht1
  unfold entropySlope binarySlope
  fun_prop (disch := first | positivity | linarith [hu.1,hu.2,hv.1,hv.2])

theorem entropyCurvature_continuousAt {r t : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (ht : -1 < t) (ht1 : t < 1) :
    ContinuousAt (fun z : ℝ × ℝ => entropyCurvature z.1 z.2) (r,t) := by
  obtain ⟨hu,hv⟩ := entropyArgs_interior hr hr1 ht ht1
  unfold entropyCurvature binarySlope binaryCurvature
  fun_prop (disch := first | positivity | linarith [hu.1,hu.2,hv.1,hv.2])

/-- Bounds independent of the gap power, obtained on a compact rectangle that
includes r=0. No uniform derivative assumption is introduced. -/
theorem entropy_transverse_uniform_bounds {b δ : ℝ} (_hb : 0 ≤ b) (hb1 : b < 1)
    (_hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C₁ C₂ : ℝ, (∀ r ∈ Icc 0 b, ∀ t ∈ Icc (-δ) δ, ‖entropySlope r t‖ ≤ C₁) ∧
      (∀ r ∈ Icc 0 b, ∀ t ∈ Icc (-δ) δ, ‖entropyCurvature r t‖ ≤ C₂) := by
  have hs : IsCompact (Icc (0:ℝ) b ×ˢ Icc (-δ) δ) := isCompact_Icc.prod isCompact_Icc
  have h₁ : ContinuousOn (fun z : ℝ × ℝ => entropySlope z.1 z.2)
      (Icc (0:ℝ) b ×ˢ Icc (-δ) δ) := by
    intro z hz
    exact (entropySlope_continuousAt hz.1.1 (lt_of_le_of_lt hz.1.2 hb1)
      (by linarith [hz.2.1]) (by linarith [hz.2.2])).continuousWithinAt
  have h₂ : ContinuousOn (fun z : ℝ × ℝ => entropyCurvature z.1 z.2)
      (Icc (0:ℝ) b ×ˢ Icc (-δ) δ) := by
    intro z hz
    exact (entropyCurvature_continuousAt hz.1.1 (lt_of_le_of_lt hz.1.2 hb1)
      (by linarith [hz.2.1]) (by linarith [hz.2.2])).continuousWithinAt
  obtain ⟨C₁,hC₁⟩ := hs.exists_bound_of_continuousOn h₁
  obtain ⟨C₂,hC₂⟩ := hs.exists_bound_of_continuousOn h₂
  exact ⟨C₁,C₂,fun r hr t ht => hC₁ (r,t) ⟨hr,ht⟩,fun r hr t ht => hC₂ (r,t) ⟨hr,ht⟩⟩

end
end MathDB333569
