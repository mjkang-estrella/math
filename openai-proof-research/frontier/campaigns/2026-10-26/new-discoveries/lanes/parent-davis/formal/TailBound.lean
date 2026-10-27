import Mathlib

namespace Davis

noncomputable section

def varianceTarget (d a : ℝ) : ℝ :=
  d / 4 - (199 / 200 : ℝ) * (d + 1) * (d - 2) / (4 * (a + d - 1))

def momentCoefficient (d a : ℝ) : ℝ := 2 * d * a - d / 2 + 2 * a ^ 2 - 2 * a

def comparisonNumerator (d a : ℝ) : ℝ :=
  800 * a ^ 3 * d ^ 2 - 800 * a ^ 3 * d + 318400 * a ^ 3 +
  1600 * a ^ 2 * d ^ 3 - 3200 * a ^ 2 * d ^ 2 + 638400 * a ^ 2 * d -
  636800 * a ^ 2 + 800 * a * d ^ 4 - 42200 * a * d ^ 3 +
  360600 * a * d ^ 2 - 558000 * a * d + 318400 * a - 199 * d ^ 4 +
  398 * d ^ 3 - 79003 * d ^ 2 + 78804 * d + 158404

theorem comparisonNumerator_pos {d a : ℝ} (hd : 43 ≤ d) (ha : 1 ≤ a)
    (hasq : d + 2 ≤ 4 * a ^ 2) : 0 < comparisonNumerator d a := by
  let t := d - 43
  have ht : 0 ≤ t := sub_nonneg.mpr hd
  let K := d ^ 2 - d + 398
  have hK : 0 < K := by dsimp [K]; nlinarith [sq_nonneg (d - 1)]
  let L := 800 * t ^ 4 + 95600 * t ^ 3 + 3818000 * t ^ 2 +
    51998400 * t + 42755200
  have hL : 0 < L := by dsimp [L]; positivity
  have hC : 0 < 201 * d ^ 2 + 599 * d - 402 := by nlinarith [sq_nonneg d]
  have hA : 0 ≤ 800 * K * (a + 2 * d - 2) * (a ^ 2 - (d + 2) / 4) := by
    apply mul_nonneg
    · apply mul_nonneg
      · positivity
      · linarith
    · linarith
  have hB : 0 < a * L := mul_pos (by linarith) hL
  have hD : 0 < K * (201 * d ^ 2 + 599 * d - 402) := mul_pos hK hC
  have heq : comparisonNumerator d a =
      800 * K * (a + 2 * d - 2) * (a ^ 2 - (d + 2) / 4) + a * L +
        K * (201 * d ^ 2 + 599 * d - 402) := by
    dsimp [comparisonNumerator, K, L, t]
    ring
  rw [heq]
  linarith

theorem target_pos {d a : ℝ} (hd : 43 ≤ d) (ha : 1 ≤ a) :
    0 < varianceTarget d a := by
  have hden : 0 < 4 * (a + d - 1) := by linarith
  have hden0 : a + d - 1 ≠ 0 := by linarith
  have heq : varianceTarget d a =
      (200 * d * a + d ^ 2 - d + 398) / (800 * (a + d - 1)) := by
    dsimp [varianceTarget]
    field_simp [hden0]
    ring
  rw [heq]
  apply div_pos
  · have hda : 0 ≤ d * a := mul_nonneg (by linarith) (by linarith)
    nlinarith [sq_nonneg (d - 1)]
  · linarith

theorem target_quadratic_pos {d a : ℝ} (hd : 43 ≤ d) (ha : 1 ≤ a)
    (hasq : d + 2 ≤ 4 * a ^ 2) :
    0 < 2 * (varianceTarget d a) ^ 2 + momentCoefficient d a * varianceTarget d a -
      d / 2 * a ^ 2 := by
  have hn := comparisonNumerator_pos hd ha hasq
  have hden : a + d - 1 ≠ 0 := by linarith
  have heq : 2 * (varianceTarget d a) ^ 2 +
      momentCoefficient d a * varianceTarget d a - d / 2 * a ^ 2 =
      comparisonNumerator d a / (320000 * (a + d - 1) ^ 2) := by
    dsimp [varianceTarget, momentCoefficient, comparisonNumerator]
    field_simp [hden]
    ring
  rw [heq]
  exact div_pos hn (mul_pos (by norm_num) (sq_pos_of_ne_zero hden))

theorem tail_variance_bound {d a V M : ℝ} (hd : 43 ≤ d) (ha : 1 ≤ a)
    (hasq : d + 2 ≤ 4 * a ^ 2) (hV : 0 ≤ V) (hM : V ^ 2 ≤ M)
    (hmoment : 2 * M + momentCoefficient d a * V = d / 2 * a ^ 2) :
    V < varianceTarget d a := by
  have hB : 0 < momentCoefficient d a := by
    dsimp [momentCoefficient]
    have hda : d ≤ d * a := by nlinarith
    have haa : a ≤ a ^ 2 := by nlinarith
    linarith
  have hT := target_pos hd ha
  have hq := target_quadratic_pos hd ha hasq
  by_contra hnot
  have hTV : varianceTarget d a ≤ V := le_of_not_gt hnot
  have hprod : 0 ≤ momentCoefficient d a * (V - varianceTarget d a) :=
    mul_nonneg hB.le (sub_nonneg.mpr hTV)
  have hsq : (varianceTarget d a) ^ 2 ≤ V ^ 2 := by nlinarith
  nlinarith

end

end Davis
