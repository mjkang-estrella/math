import Mathlib

open Finset
namespace FlatBernoulli

variable {ι : Type*} [Fintype ι]

theorem weighted_power_ge_mass (w z : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hz : ∀ i, 0 ≤ z i) (hmean : (∑ i, w i) ≤ ∑ i, w i*z i) (m : ℕ) :
    (∑ i, w i) ≤ ∑ i, w i*z i^m := by
  have ht : ∀ i, 1+(m:ℝ)*(z i-1) ≤ z i^m := fun i =>
    one_add_mul_sub_le_pow (by linarith [hz i]) m
  have hm : 0 ≤ (m:ℝ)*((∑ i, w i*z i)-(∑ i, w i)) :=
    mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hmean)
  calc
    (∑ i, w i) ≤ (∑ i, w i)+(m:ℝ)*((∑ i, w i*z i)-(∑ i, w i)) := by linarith
    _ = ∑ i, (w i+(m:ℝ)*(w i*z i-w i)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    _ = ∑ i, w i*(1+(m:ℝ)*(z i-1)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, w i*z i^m := by
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (ht i) (hw i))

theorem weighted_power_lower (w z : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hz : ∀ i, 0 ≤ z i) (hmass : ∑ i, w i = 1) {c : ℝ} (hc : 0 < c)
    (hmean : c ≤ ∑ i, w i*z i) (m : ℕ) :
    c^m ≤ ∑ i, w i*z i^m := by
  have hnorm : (∑ i, w i) ≤ ∑ i, w i*(z i/c) := by
    rw [hmass]
    simp only [← mul_div_assoc, ← Finset.sum_div]
    exact (le_div_iff₀ hc).mpr (by simpa using hmean)
  have h := weighted_power_ge_mass w (fun i => z i/c) hw
    (fun i => div_nonneg (hz i) hc.le) hnorm m
  simp only [hmass, div_pow, ← mul_div_assoc, ← Finset.sum_div] at h
  simpa only [one_mul] using (le_div_iff₀ (pow_pos hc m)).mp h

end FlatBernoulli
