import Tail
set_option autoImplicit false
set_option warningAsError true
noncomputable section
open scoped BigOperators unitInterval
namespace BesselFejer

def bernsteinSum {d : ℕ} (cs : Fin (d+1) → ℚ) (t : unitInterval) : ℝ :=
  ∑ i, (cs i : ℝ) * bernstein d i t

lemma bernsteinSum_lower {d : ℕ} (cs : Fin (d+1) → ℚ) (b : ℚ)
    (hb : ∀ i, b ≤ cs i) (t : unitInterval) : (b : ℝ) ≤ bernsteinSum cs t := by
  have he : (b : ℝ) = ∑ i : Fin (d+1), (b : ℝ) * bernstein d i t := by
    rw [← Finset.mul_sum, bernstein.probability, mul_one]
  rw [he, bernsteinSum]
  apply Finset.sum_le_sum
  intro i _
  have hbi : (b : ℝ) ≤ cs i := by exact_mod_cast hb i
  exact mul_le_mul_of_nonneg_right hbi bernstein_nonneg

lemma bernsteinSum_upper {d : ℕ} (cs : Fin (d+1) → ℚ) (b : ℚ)
    (hb : ∀ i, cs i ≤ b) (t : unitInterval) : bernsteinSum cs t ≤ (b : ℝ) := by
  have he : (b : ℝ) = ∑ i : Fin (d+1), (b : ℝ) * bernstein d i t := by
    rw [← Finset.mul_sum, bernstein.probability, mul_one]
  rw [he, bernsteinSum]
  apply Finset.sum_le_sum
  intro i _
  have hbi : (cs i : ℝ) ≤ b := by exact_mod_cast hb i
  exact mul_le_mul_of_nonneg_right hbi bernstein_nonneg

lemma bernsteinSum_scaled {d : ℕ} (cs scaled : Fin (d+1) → ℚ)
    (hs : ∀ i, scaled i = cs i * (d.choose i : ℚ)) (t : unitInterval) :
    bernsteinSum cs t = ∑ i : Fin (d+1),
      (scaled i : ℝ) * (t : ℝ)^(i : ℕ) * (1-(t : ℝ))^(d-(i : ℕ)) := by
  unfold bernsteinSum
  apply Finset.sum_congr rfl
  intro i _
  rw [bernstein_apply, hs i]
  push_cast
  ring

end BesselFejer
