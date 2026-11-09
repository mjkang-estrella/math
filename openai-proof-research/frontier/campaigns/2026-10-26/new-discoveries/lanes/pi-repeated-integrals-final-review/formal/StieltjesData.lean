import SourceDefs

open MeasureTheory Set Filter
open scoped Topology

namespace RepeatedIntegrals

noncomputable section

def intervalExtension (g : ℝ → ℝ) (x : ℝ) : ℝ := g (max 0 (min 1 x))

theorem intervalExtension_mem (x : ℝ) : max (0 : ℝ) (min 1 x) ∈ Icc (0 : ℝ) 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem intervalExtension_of_mem (g : ℝ → ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    intervalExtension g x = g x := by
  simp [intervalExtension, min_eq_right hx.2, max_eq_right hx.1]

theorem intervalExtension_left (g : ℝ → ℝ) {x : ℝ} (hx : x ≤ 0) :
    intervalExtension g x = g 0 := by
  rw [intervalExtension, max_eq_left ((min_le_right _ _).trans hx)]

theorem intervalExtension_right (g : ℝ → ℝ) {x : ℝ} (hx : 1 ≤ x) :
    intervalExtension g x = g 1 := by
  simp [intervalExtension, min_eq_left hx]

theorem intervalExtension_continuous {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc (0 : ℝ) 1)) : Continuous (intervalExtension g) := by
  exact hg.comp_continuous (continuous_const.max (continuous_const.min continuous_id))
    intervalExtension_mem

theorem intervalExtension_monotone {g : ℝ → ℝ}
    (hg : MonotoneOn g (Icc (0 : ℝ) 1)) : Monotone (intervalExtension g) := by
  intro x y hxy
  exact hg (intervalExtension_mem x) (intervalExtension_mem y)
    (max_le_max le_rfl (min_le_min le_rfl hxy))

def intervalStieltjes (g : ℝ → ℝ) (hm : MonotoneOn g (Icc (0 : ℝ) 1))
    (hc : ContinuousOn g (Icc (0 : ℝ) 1)) : StieltjesFunction ℝ where
  toFun := intervalExtension g
  mono' := intervalExtension_monotone hm
  right_continuous' := fun _ => (intervalExtension_continuous hc).continuousAt.continuousWithinAt

theorem intervalStieltjes_continuous {g : ℝ → ℝ}
    (hm : MonotoneOn g (Icc (0 : ℝ) 1)) (hc : ContinuousOn g (Icc (0 : ℝ) 1)) :
    Continuous (intervalStieltjes g hm hc) := intervalExtension_continuous hc

theorem intervalStieltjes_tendsto_atBot {g : ℝ → ℝ}
    (hm : MonotoneOn g (Icc (0 : ℝ) 1)) (hc : ContinuousOn g (Icc (0 : ℝ) 1)) :
    Tendsto (intervalStieltjes g hm hc) atBot (𝓝 (g 0)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
  exact (intervalExtension_left g hx).symm

theorem intervalStieltjes_tendsto_atTop {g : ℝ → ℝ}
    (hm : MonotoneOn g (Icc (0 : ℝ) 1)) (hc : ContinuousOn g (Icc (0 : ℝ) 1)) :
    Tendsto (intervalStieltjes g hm hc) atTop (𝓝 (g 1)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact (intervalExtension_right g hx).symm

theorem intervalStieltjes_noAtoms {g : ℝ → ℝ}
    (hm : MonotoneOn g (Icc (0 : ℝ) 1)) (hc : ContinuousOn g (Icc (0 : ℝ) 1)) :
    NullSingletonClass (intervalStieltjes g hm hc).measure := by
  constructor
  intro x
  rw [StieltjesFunction.measure_singleton,
    (intervalStieltjes_continuous hm hc).continuousAt.continuousWithinAt.leftLim_eq]
  simp

theorem intervalStieltjes_mass {g : ℝ → ℝ}
    (hm : MonotoneOn g (Icc (0 : ℝ) 1)) (hc : ContinuousOn g (Icc (0 : ℝ) 1)) :
    (intervalStieltjes g hm hc).measure univ = ENNReal.ofReal (g 1 - g 0) := by
  exact StieltjesFunction.measure_univ _ (intervalStieltjes_tendsto_atBot hm hc)
    (intervalStieltjes_tendsto_atTop hm hc)

theorem intervalStieltjes_finite {g : ℝ → ℝ}
    (hm : MonotoneOn g (Icc (0 : ℝ) 1)) (hc : ContinuousOn g (Icc (0 : ℝ) 1)) :
    IsFiniteMeasure (intervalStieltjes g hm hc).measure := by
  constructor
  rw [intervalStieltjes_mass hm hc]
  exact ENNReal.ofReal_lt_top

theorem intervalStieltjes_Icc {g : ℝ → ℝ}
    (hm : MonotoneOn g (Icc (0 : ℝ) 1)) (hc : ContinuousOn g (Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (intervalStieltjes g hm hc).measure (Icc 0 x) = ENNReal.ofReal (g x - g 0) := by
  rw [StieltjesFunction.measure_Icc,
    (intervalStieltjes_continuous hm hc).continuousAt.continuousWithinAt.leftLim_eq]
  change ENNReal.ofReal (intervalExtension g x - intervalExtension g 0) = _
  rw [intervalExtension_of_mem g hx, intervalExtension_left g le_rfl]

theorem intervalStieltjes_compl {g : ℝ → ℝ}
    (hm : MonotoneOn g (Icc (0 : ℝ) 1)) (hc : ContinuousOn g (Icc (0 : ℝ) 1)) :
    (intervalStieltjes g hm hc).measure (Icc (0 : ℝ) 1)ᶜ = 0 := by
  have hl : (intervalStieltjes g hm hc).measure (Iio 0) = 0 := by
    rw [StieltjesFunction.measure_Iio _ (intervalStieltjes_tendsto_atBot hm hc),
      (intervalStieltjes_continuous hm hc).continuousAt.continuousWithinAt.leftLim_eq]
    change ENNReal.ofReal (intervalExtension g 0 - g 0) = 0
    simp [intervalExtension]
  have hr : (intervalStieltjes g hm hc).measure (Ioi 1) = 0 := by
    rw [StieltjesFunction.measure_Ioi _ (intervalStieltjes_tendsto_atTop hm hc)]
    change ENNReal.ofReal (g 1 - intervalExtension g 1) = 0
    simp [intervalExtension]
  have hs : (Icc (0 : ℝ) 1)ᶜ = Iio 0 ∪ Ioi 1 := by
    ext x
    simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi]
    simp only [not_and_or, not_le]
  rw [hs]
  exact measure_union_null hl hr

theorem monotone_nonconstant_terminal_pos {g : ℝ → ℝ}
    (hm : MonotoneOn g (Icc (0 : ℝ) 1)) (h0 : g 0 = 0)
    (hn : ¬ ∃ c : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, g t = c) : 0 < g 1 := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  by_contra h
  apply hn
  refine ⟨0, fun t ht => ?_⟩
  have hlo := hm h01 ht ht.1
  have hhi := hm ht h11 ht.2
  linarith

theorem source_top_derivative_continuous {n : ℕ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ n f (Icc (0 : ℝ) 1)) :
    ContinuousOn (iteratedDerivWithin n f (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) := by
  exact hf.continuousOn_iteratedDerivWithin le_rfl uniqueDiffOn_Icc_zero_one

end

end RepeatedIntegrals
