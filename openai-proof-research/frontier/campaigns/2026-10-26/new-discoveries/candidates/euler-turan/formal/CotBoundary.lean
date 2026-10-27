import Mathlib
noncomputable section
open Filter Set
open scoped Topology UpperHalfPlane
namespace EulerTuran
def vertical (a y : ℝ) : ℂ := (a : ℂ) + (y : ℂ) * Complex.I
lemma vertical_zero (a : ℝ) : vertical a 0 = (a : ℂ) := by simp [vertical]
lemma vertical_re (a y : ℝ) : (vertical a y).re = a := by simp [vertical]
lemma vertical_im (a y : ℝ) : (vertical a y).im = y := by simp [vertical]
lemma continuous_vertical (a : ℝ) : Continuous (vertical a) := by unfold vertical; fun_prop
lemma shifted_reciprocal_summable {a : ℝ} {p : ℕ} (hp : 1 < p) :
    Summable (fun m : ℤ => 1 / |(m:ℝ)+a|^p) := by
  have h := (Real.summable_one_div_int_add_rpow a (p:ℝ)).2 (by exact_mod_cast hp)
  simpa only [Real.rpow_natCast] using h
lemma vertical_reciprocal_bound {a : ℝ} (ha : ∀ m : ℤ, a + m ≠ 0)
    (p : ℕ) (y : ℝ) (m : ℤ) :
    ‖1 / (vertical a y + m)^p‖ ≤ 1 / |(m:ℝ)+a|^p := by
  have hpos : 0 < |(m:ℝ)+a| := abs_pos.mpr (by simpa [add_comm] using ha m)
  have hn : |(m:ℝ)+a| ≤ ‖vertical a y + m‖ := by
    simpa [vertical, add_comm] using Complex.abs_re_le_norm (vertical a y + m)
  simp only [norm_div, norm_one, norm_pow]
  exact one_div_le_one_div_of_le (pow_pos hpos p) (pow_le_pow_left₀ hpos.le hn p)
lemma vertical_reciprocal_tendsto {a : ℝ} (ha : ∀ m : ℤ, a + m ≠ 0)
    {p : ℕ} (hp : 1 < p) :
    Tendsto (fun y : ℝ => ∑' m : ℤ, 1 / (vertical a y + m)^p)
      (𝓝 0) (𝓝 (∑' m : ℤ, 1 / ((a:ℂ)+m)^p)) := by
  apply tendsto_tsum_of_dominated_convergence (shifted_reciprocal_summable hp)
  · intro m
    have hm : (a:ℂ)+(m:ℂ) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      exact ha m (by simpa using this)
    have hc : ContinuousAt (fun y : ℝ => 1 / (vertical a y + m)^p) 0 := by
      apply continuousAt_const.div
      · exact ((continuous_vertical a).continuousAt.add continuousAt_const).pow p
      · simpa [vertical] using pow_ne_zero p hm
    simpa [vertical] using hc.tendsto
  · exact Filter.Eventually.of_forall fun y m => vertical_reciprocal_bound ha p y m
lemma contDiffAt_continuousAt_iteratedDeriv {f : ℂ → ℂ} {z : ℂ} (k : ℕ)
    (hf : ContDiffAt ℂ k f z) : ContinuousAt (iteratedDeriv k f) z := by
  rw [iteratedDeriv_eq_equiv_comp]
  exact (ContinuousMultilinearMap.piFieldEquiv ℂ (Fin k) ℂ).symm.continuous.continuousAt.comp
    (hf.continuousAt_iteratedFDeriv le_rfl)
lemma cot_derivative_at_real {a : ℝ} (ha : (a:ℂ) ∈ Complex.integerComplement)
    {k : ℕ} (hk : 1 ≤ k) :
    iteratedDeriv k (fun z : ℂ => (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*z)) a =
      (-1:ℂ)^k * (k.factorial:ℂ) * ∑' m : ℤ, 1 / ((a:ℂ)+m)^(k+1) := by
  have hanz : ∀ m : ℤ, a + m ≠ 0 := by
    intro m hm
    apply Complex.integerComplement_add_ne_zero ha m
    exact_mod_cast hm
  have hc : ContDiffAt ℂ k
      (fun z : ℂ => (Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*z)) (a:ℂ) := by
    simp only [Complex.cot]
    apply ContDiffAt.mul (by fun_prop)
    exact ContDiffAt.div (by fun_prop) (by fun_prop) (sin_pi_mul_ne_zero ha)
  have hleft := (contDiffAt_continuousAt_iteratedDeriv k hc).tendsto.comp
    (by simpa [vertical] using ((continuous_vertical a).continuousAt (x := 0)).tendsto :
      Tendsto (vertical a) (𝓝 0) (𝓝 (a:ℂ)))
  have hright := ((vertical_reciprocal_tendsto hanz (by omega : 1 < k+1)).const_mul
    ((-1:ℂ)^k * (k.factorial:ℂ)))
  apply tendsto_nhds_unique (hleft.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
  apply (hright.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hypos : 0 < y := hy
  have hmem : vertical a y ∈ UpperHalfPlane.upperHalfPlaneSet := by
    simpa [UpperHalfPlane.upperHalfPlaneSet, vertical] using hypos
  have h := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow hk hmem
  rw [iteratedDerivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hmem] at h
  exact h.symm
end EulerTuran
