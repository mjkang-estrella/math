import Obstruction

set_option autoImplicit false
set_option warningAsError true

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section

namespace CStarCorona

def LocalPowerAtZero (g : A → A) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ b : ℕ → A,
    ∀ z : A, ‖z‖ < r → HasSum (fun n => b n * z ^ n) (g z)

theorem square_zero_series (b : ℕ → A) (z v : A) (hz : z ^ 2 = 0)
    (hs : HasSum (fun n => b n * z ^ n) v) : v = b 0 + b 1 * z := by
  have ht : HasSum (fun n => b n * z ^ n)
      (∑ n ∈ Finset.range 2, b n * z ^ n) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    have hn2 : 2 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn2
    rw [pow_add, hz, zero_mul, mul_zero]
  simpa [Finset.sum_range_succ] using hs.unique ht

theorem small_nilpotent_line (r : ℝ) (hr : 0 < r) :
    ∃ t : ℝ, 0 < t ∧ ‖(t : ℂ) • nilpotent‖ < r ∧
      ‖(t : ℂ) • nilpotent‖ < 1 := by
  let u : ℝ := min r 1
  have hu : 0 < u := lt_min hr zero_lt_one
  let t : ℝ := u / (2 * (‖nilpotent‖ + 1))
  have hd : 0 < 2 * (‖nilpotent‖ + 1) := by positivity
  have ht : 0 < t := div_pos hu hd
  have heq : t * (2 * (‖nilpotent‖ + 1)) = u := div_mul_cancel₀ _ hd.ne'
  have hn : ‖(t : ℂ) • nilpotent‖ = t * ‖nilpotent‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  refine ⟨t, ht, ?_, ?_⟩
  · have hle : u ≤ r := min_le_left _ _
    rw [hn]
    nlinarith [norm_nonneg nilpotent]
  · have hle : u ≤ 1 := min_le_right _ _
    rw [hn]
    nlinarith [norm_nonneg nilpotent]

theorem no_local_power_right_inverse (g : A → A) (hloc : LocalPowerAtZero g)
    (hinv : ∀ z : A, ‖z‖ < 1 → witness z * g z = 1) : False := by
  obtain ⟨r, hr, b, hb⟩ := hloc
  have hg0 : g 0 = 1 := by simpa [witness] using hinv 0 (by simp)
  have hb0 : b 0 = 1 := by
    simpa [hg0] using (square_zero_series b 0 (g 0) (by simp) (hb 0 (by simpa using hr))).symm
  obtain ⟨t, ht, htr, ht1⟩ := small_nilpotent_line r hr
  have hsq : ((t : ℂ) • nilpotent) ^ 2 = 0 := by
    simp [smul_pow, nilpotent_sq]
  have hsqneg : ((-(t : ℂ)) • nilpotent) ^ 2 = 0 := by
    simp [smul_pow, nilpotent_sq]
  have hp := square_zero_series b _ _ hsq (hb _ htr)
  have hm := square_zero_series b _ _ hsqneg (hb _ (by simpa using htr))
  rw [hb0, Algebra.mul_smul_comm] at hp hm
  apply no_affine_nilpotent_right_inverse (t : ℂ) (by exact_mod_cast ht.ne') (b 1)
  · rw [← hp]
    exact hinv _ ht1
  · rw [← hm]
    exact hinv _ (by simpa using ht1)

end CStarCorona
