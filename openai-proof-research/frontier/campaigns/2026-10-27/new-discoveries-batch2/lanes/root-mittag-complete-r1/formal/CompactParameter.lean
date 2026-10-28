import HalfIntegral

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MittagModulus

/-- Continuous derivatives on compact rectangles justify parameter differentiation. -/
theorem hasDerivAt_unitIntegral {F F' : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ x u : ℝ, HasDerivAt (fun y => F y u) (F' x u) x) (x : ℝ) :
    HasDerivAt (fun y => ∫ u in (0 : ℝ)..1, F y u) (∫ u in (0 : ℝ)..1, F' x u) x := by
  have hc : IsCompact (Set.Icc (x - 1) (x + 1) ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hc.bddAbove_image hF'.norm.continuousOn
  have hFx (y : ℝ) : Continuous (F y) := hF.comp (continuous_const.prodMk continuous_id)
  have hF'x (y : ℝ) : Continuous (F' y) := hF'.comp (continuous_const.prodMk continuous_id)
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (s := Set.Ioo (x - 1) (x + 1))
    (bound := fun _ => M)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun y => (hFx y).aestronglyMeasurable))
    ((hFx x).intervalIntegrable 0 1) ((hF'x x).aestronglyMeasurable) _
    (continuous_const.intervalIntegrable 0 1) _).2
  · apply MeasureTheory.ae_of_all
    intro u hu y hy
    rw [Set.uIoc_of_le zero_le_one] at hu
    exact hM (Set.mem_image_of_mem _ (show (y, u) ∈
      Set.Icc (x - 1) (x + 1) ×ˢ Set.Icc (0 : ℝ) 1 from
      ⟨⟨hy.1.le, hy.2.le⟩, ⟨hu.1.le, hu.2⟩⟩))
  · exact MeasureTheory.ae_of_all _ (fun u _ y _ => hd y u)

end MittagModulus
