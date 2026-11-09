import DepthArithmetic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit false
set_option warningAsError true
open Filter Topology
namespace CascadeRate
theorem depth_atTop : Tendsto depth atTop atTop := by
  exact tendsto_atTop_mono index_le_depth tendsto_id
theorem depth_real_atTop : Tendsto (fun k => (depth k : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp depth_atTop
theorem previous_ratio (k : ℕ) (hk : 1 ≤ k) :
    (depth (k-1) : ℝ) / depth k ≤ 1 / (k : ℝ)^2 := by
  have hp : 0 < depth k := lt_of_lt_of_le (by omega) (index_le_depth k)
  have hkr : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hdr : (0:ℝ) < depth k := by exact_mod_cast hp
  apply (div_le_div_iff₀ hdr (sq_pos_of_pos hkr)).2
  simpa only [one_mul] using (show (depth (k-1):ℝ)*(k:ℝ)^2 ≤ depth k by exact_mod_cast previous_bound k hk)
theorem deficit_ratio_zero :
    Tendsto (fun k => (deficit k : ℝ) / depth k) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun k => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    ?_ (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ))
  filter_upwards [eventually_ge_atTop 3] with k hk
  have hp : 0 < depth k := lt_of_lt_of_le (by omega) (index_le_depth k)
  have hkr : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hdr : (0:ℝ) < depth k := by exact_mod_cast hp
  apply (div_le_div_iff₀ hdr hkr).2
  exact_mod_cast deficit_linear_bound k hk
theorem depth_beats_geometric (C r : ℝ) (hC : 0 < C) (hr : 0 < r)
    (hr1 : r < 1) (n0 : ℕ) :
    ∃ k : ℕ, 3 ≤ k ∧ n0 ≤ depth k ∧ C*r^(depth k) < (1/2:ℝ)^(deficit k) := by
  have hlr : Real.log r < 0 := Real.log_neg hr hr1
  have hlim : Tendsto (fun k => Real.log C / (depth k : ℝ) -
      ((deficit k : ℝ) / depth k) * Real.log (1/2:ℝ)) atTop (𝓝 0) := by
    simpa using (depth_real_atTop.const_div_atTop (Real.log C)).sub
      (deficit_ratio_zero.mul_const (Real.log (1/2:ℝ)))
  have hev : ∀ᶠ k in atTop, Real.log C / (depth k : ℝ) -
      ((deficit k : ℝ) / depth k)*Real.log (1/2:ℝ) < -Real.log r :=
    hlim.eventually (gt_mem_nhds (by linarith))
  obtain ⟨k, hk, hn, he⟩ := ( (eventually_ge_atTop 3).and
    ((depth_atTop.eventually (eventually_ge_atTop n0)).and hev)).exists
  refine ⟨k, hk, hn, ?_⟩
  have hd : (0:ℝ) < depth k := by
    exact_mod_cast lt_of_lt_of_le (show 0 < k by omega) (index_le_depth k)
  have hm := (mul_lt_mul_iff_left₀ hd).2 he
  have hne : (depth k : ℝ) ≠ 0 := ne_of_gt hd
  have heq : (Real.log C / (depth k : ℝ) -
      ((deficit k : ℝ) / depth k)*Real.log (1/2:ℝ)) * (depth k : ℝ) =
      Real.log C - (deficit k : ℝ)*Real.log (1/2:ℝ) := by
    field_simp
  rw [heq] at hm
  apply (Real.log_lt_log_iff (mul_pos hC (pow_pos hr _)) (pow_pos (by norm_num) _)).1
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (pow_pos hr _)), Real.log_pow, Real.log_pow]
  nlinarith
/-- Abstract transfer helper, not the literal source cascade claim. -/
theorem abstract_no_eventual_geometric (f : ℕ → ℝ)
    (hf : ∀ k : ℕ, 3 ≤ k → (1/2:ℝ)^(deficit k) ≤ f (depth k)) :
    ¬ ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < 1 ∧
      ∀ᶠ n in atTop, f n ≤ C*r^n := by
  rintro ⟨C, r, hC, hr, hr1, hbound⟩
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hbound
  obtain ⟨k, hk, hn, hlt⟩ := depth_beats_geometric C r hC hr hr1 n0
  exact (not_lt_of_ge (le_trans (hf k hk) (hn0 _ hn))) hlt
end CascadeRate
