import GammaInterpolation

open Filter Topology

namespace Schmidlin

theorem gammaError_tendsto : Tendsto gammaError atTop (nhds 0) := by
  have hnat : Tendsto (fun n : ℕ => gammaError (n:ℝ)) atTop (nhds 0) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    simpa only [Nat.cast_add, Nat.cast_one] using gammaError_nat_tendsto
  have hn : Tendsto (fun x : ℝ => (⌊x⌋₊:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop
  have he : Tendsto (fun x : ℝ => gammaError (⌊x⌋₊:ℝ)) atTop (nhds 0) :=
    hnat.comp tendsto_nat_floor_atTop
  have hu : Tendsto (fun x : ℝ => 1/(⌊x⌋₊:ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hn
  have hl : Tendsto (fun x : ℝ => 2/((⌊x⌋₊:ℝ)-1)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (by
      simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1:ℝ) hn)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using he.sub hl)
    (by simpa using he.add hu)
  all_goals
    filter_upwards [eventually_ge_atTop (2:ℝ)] with x hx
    have hx0 : 0 ≤ x := by linarith
    have hfloor : (2:ℕ) ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 hx
    have hr0 : 0 ≤ x-(⌊x⌋₊:ℝ) := sub_nonneg.mpr (Nat.floor_le hx0)
    have hr1 : x-(⌊x⌋₊:ℝ) ≤ 1 := by linarith [Nat.lt_floor_add_one x]
    have h := gammaError_unit_bounds hfloor hr0 hr1
    simp only [add_sub_cancel] at h
    first | simpa only [one_div] using h.1 | simpa only [one_div] using h.2

end Schmidlin
