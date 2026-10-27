import SourceDefs

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace HermiteEnvelope

open Filter Topology

/-- The odd-degree initial-energy excess, using Wallis' exact product. -/
def oddEnergyRatio (m : ℕ) : ℝ :=
  Real.pi * ((2 * (m : ℝ) + 1) / (4 * (m : ℝ) + 3)) / Real.Wallis.W m

def correctedOddRatio (m : ℕ) : ℝ :=
  oddEnergyRatio m * (1 - 1 / (2 * (4 * (m : ℝ) + 3) ^ 2))

theorem oddEnergyRatio_pos (m : ℕ) : 0 < oddEnergyRatio m := by
  unfold oddEnergyRatio
  exact div_pos (mul_pos Real.pi_pos (div_pos (by positivity) (by positivity)))
    (Real.Wallis.W_pos m)

theorem oddEnergyRatio_succ (m : ℕ) :
    oddEnergyRatio (m + 1) = oddEnergyRatio m *
      ((2 * (m : ℝ) + 3) ^ 2 * (4 * (m : ℝ) + 3) /
        (4 * ((m : ℝ) + 1) ^ 2 * (4 * (m : ℝ) + 7))) := by
  unfold oddEnergyRatio
  rw [Real.Wallis.W_succ]
  push_cast
  field_simp
  ring

theorem oddEnergyRatio_antitone : Antitone oddEnergyRatio := by
  apply antitone_nat_of_succ_le
  intro m
  rw [oddEnergyRatio_succ]
  have hden : 0 < 4 * ((m : ℝ) + 1) ^ 2 * (4 * (m : ℝ) + 7) := by positivity
  have hr : (2 * (m : ℝ) + 3) ^ 2 * (4 * (m : ℝ) + 3) /
      (4 * ((m : ℝ) + 1) ^ 2 * (4 * (m : ℝ) + 7)) ≤ 1 := by
    apply (div_le_one hden).2
    nlinarith [sq_nonneg (m : ℝ)]
  simpa using mul_le_mul_of_nonneg_left hr (oddEnergyRatio_pos m).le

theorem correctedOddRatio_succ_sub (m : ℕ) :
    correctedOddRatio (m + 1) - correctedOddRatio m = oddEnergyRatio m *
      ((176 * (m : ℝ) ^ 2 + 440 * (m : ℝ) + 247) /
        (8 * ((m : ℝ) + 1) ^ 2 * (4 * (m : ℝ) + 3) ^ 2 *
          (4 * (m : ℝ) + 7) ^ 3)) := by
  unfold correctedOddRatio
  rw [oddEnergyRatio_succ]
  push_cast
  field_simp
  ring

theorem correctedOddRatio_strictMono : StrictMono correctedOddRatio := by
  apply strictMono_nat_of_lt_succ
  intro m
  apply sub_pos.mp
  rw [correctedOddRatio_succ_sub]
  exact mul_pos (oddEnergyRatio_pos m) (div_pos (by positivity) (by positivity))

theorem oddEnergyRatio_tendsto : Tendsto oddEnergyRatio atTop (𝓝 1) := by
  have hE : Tendsto (fun m : ℕ => 4 * (m : ℝ) + 3) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 4)).atTop_add
      tendsto_const_nhds
  have hinv : Tendsto (fun m : ℕ => 1 / (2 * (4 * (m : ℝ) + 3))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hE.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hr : Tendsto (fun m : ℕ => (2 * (m : ℝ) + 1) / (4 * (m : ℝ) + 3))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    have heq : (fun m : ℕ => (2 * (m : ℝ) + 1) / (4 * (m : ℝ) + 3)) =
        (fun m : ℕ => (1 / 2 : ℝ) - 1 / (2 * (4 * (m : ℝ) + 3))) := by
      funext m
      field_simp
      ring
    rw [heq]
    simpa using (tendsto_const_nhds.sub hinv :
      Tendsto (fun m : ℕ => (1 / 2 : ℝ) - 1 / (2 * (4 * (m : ℝ) + 3)))
        atTop (𝓝 ((1 / 2 : ℝ) - 0)))
  have hg := (hr.const_mul Real.pi).div Real.Wallis.tendsto_W_nhds_pi_div_two
    (ne_of_gt (by positivity : (0 : ℝ) < Real.pi / 2))
  have hv : Real.pi * (1 / 2) / (Real.pi / 2) = 1 := by field_simp
  rw [hv] at hg
  exact hg

theorem correctedOddRatio_tendsto : Tendsto correctedOddRatio atTop (𝓝 1) := by
  have hE : Tendsto (fun m : ℕ => 4 * (m : ℝ) + 3) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 4)).atTop_add
      tendsto_const_nhds
  have hi : Tendsto (fun m : ℕ => 1 / (2 * (4 * (m : ℝ) + 3) ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (by
      simpa only [pow_two] using
        (hE.atTop_mul_atTop₀ hE).const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hs : Tendsto (fun m : ℕ => 1 - 1 / (2 * (4 * (m : ℝ) + 3) ^ 2))
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub hi : Tendsto
      (fun m : ℕ => (1 : ℝ) - 1 / (2 * (4 * (m : ℝ) + 3) ^ 2))
      atTop (𝓝 ((1 : ℝ) - 0)))
  change Tendsto (fun m : ℕ => oddEnergyRatio m *
    (1 - 1 / (2 * (4 * (m : ℝ) + 3) ^ 2))) atTop (𝓝 1)
  simpa only [mul_one] using oddEnergyRatio_tendsto.mul hs

theorem correctedOddRatio_lt_one (m : ℕ) : correctedOddRatio m < 1 := by
  have hle (k : ℕ) : correctedOddRatio k ≤ 1 := by
    apply ge_of_tendsto correctedOddRatio_tendsto
    exact eventually_atTop.2 ⟨k, fun j hj => correctedOddRatio_strictMono.monotone hj⟩
  exact (correctedOddRatio_strictMono (Nat.lt_succ_self m)).trans_le (hle (m + 1))

theorem oddEnergyRatio_le_nine_pi (m : ℕ) (hm : 1 ≤ m) :
    oddEnergyRatio m ≤ 9 * Real.pi / 28 := by
  have h := oddEnergyRatio_antitone hm
  convert h using 1
  norm_num [oddEnergyRatio, Real.Wallis.W]
  ring

end HermiteEnvelope
