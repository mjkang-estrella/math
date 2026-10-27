import LowDegrees
import TailMaximum

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace HermiteEnvelope

theorem weightedHermite_two (x : ℝ) :
    weightedHermite 2 x = (4 * x ^ 2 - 2) * Real.exp (-(x ^ 2) / 2) := by
  norm_num [weightedHermite, hermiteValue, hermitePoly]
  ring

theorem degree_two_exp_certificate (u : ℝ) (hu : 0 ≤ u) :
    (4 * u - 2) ^ 2 ≤ (25 / 4 : ℝ) * Real.exp u := by
  let P : ℝ := 5 * u ^ 5 + 25 * u ^ 4 + 100 * u ^ 3 - 1236 * u ^ 2 + 2136 * u + 216
  have hp : 0 ≤ P := by
    by_cases ht : u ≤ 2
    · have hb : 0 ≤ 2 - u := by linarith
      have hid : P * 32 =
          216 * (2 - u) ^ 5 + 5352 * u * (2 - u) ^ 4 +
          14304 * u ^ 2 * (2 - u) ^ 3 + 13760 * u ^ 3 * (2 - u) ^ 2 +
          5336 * u ^ 4 * (2 - u) + 904 * u ^ 5 := by dsimp [P]; ring
      have hn : 0 ≤ 216 * (2 - u) ^ 5 + 5352 * u * (2 - u) ^ 4 +
          14304 * u ^ 2 * (2 - u) ^ 3 + 13760 * u ^ 3 * (2 - u) ^ 2 +
          5336 * u ^ 4 * (2 - u) + 904 * u ^ 5 := by positivity
      linarith
    · have hv : 0 ≤ u - 2 := by linarith
      have hid : P = 5 * (u - 2) ^ 5 + 75 * (u - 2) ^ 4 + 500 * (u - 2) ^ 3 +
          364 * (u - 2) ^ 2 - 408 * (u - 2) + 904 := by dsimp [P]; ring
      have hn : 0 ≤ 5 * (u - 2) ^ 5 + 75 * (u - 2) ^ 4 + 500 * (u - 2) ^ 3 := by positivity
      rw [hid]
      nlinarith [sq_nonneg ((u - 2) - 51 / 91)]
  have he := Real.sum_le_exp_of_nonneg hu 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  dsimp [P] at hp
  nlinarith

theorem degree_two_global_square (x : ℝ) : weightedHermite 2 x ^ 2 ≤ (25 / 4 : ℝ) := by
  have h := mul_le_mul_of_nonneg_right
    (degree_two_exp_certificate (x ^ 2) (sq_nonneg x)) (Real.exp_pos (-(x ^ 2))).le
  have he : Real.exp (x ^ 2) * Real.exp (-(x ^ 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hs : Real.exp (-(x ^ 2) / 2) ^ 2 = Real.exp (-(x ^ 2)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [weightedHermite_two, mul_pow, hs]
  nlinarith

theorem degree_one_global_square (x : ℝ) : weightedHermite 1 x ^ 2 ≤ (3 / 2 : ℝ) := by
  have h := Real.mul_exp_neg_le_exp_neg_one (x ^ 2)
  have he := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hexp : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have hsmall : Real.exp (-1) ≤ (3 / 8 : ℝ) := by
    nlinarith [Real.exp_pos (-1)]
  have hs : Real.exp (-(x ^ 2) / 2) ^ 2 = Real.exp (-(x ^ 2)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [weightedHermite_one, mul_pow, mul_pow, hs]
  nlinarith

theorem source_low_one_global (x : ℝ) :
    |weightedHermite 1 x| ≤ sourceCoefficient 1 * sourceEnvelope 1 (sourceCutoff 1) := by
  let q := 1 - sourceCutoff 1 ^ 2 / 3
  have hq : 0 < q := by
    have hc := sourceCutoff_sq_lt 1 (by omega)
    norm_num at hc
    dsimp [q]
    linarith
  have hqid : q = Real.pi / 3 - Real.pi ^ 2 / 36 := by
    dsimp [q]
    rw [sourceCutoff_sq]
    norm_num
    ring
  have hqu : q ≤ Real.pi / 4 := by
    rw [hqid]
    nlinarith [Real.pi_gt_three, Real.pi_pos]
  have hp : Real.pi ≤ (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
  have hqp : (3 / 2 : ℝ) * q * Real.pi ≤ 4 := by
    have hm := mul_le_mul_of_nonneg_right hqu Real.pi_pos.le
    nlinarith [sq_nonneg (Real.pi - 22 / 7)]
  have hcoeff : (3 / 2 : ℝ) * q ≤ sourceCoefficient 1 ^ 2 := by
    apply (mul_le_mul_iff_right₀ Real.pi_pos).mp
    nlinarith [sourceCoefficient_one_sq]
  have hb := (mul_le_mul_of_nonneg_right (degree_one_global_square x) hq.le).trans hcoeff
  have h := abs_le_envelope_of_sq (sourceCoefficient_pos 1).le hq hb
  simpa only [sourceEnvelope, Nat.cast_one, Nat.cast_ofNat, mul_one, show (2 : ℝ) + 1 = 3 by norm_num]
    using h

theorem sourceCoefficient_two : sourceCoefficient 2 = 2 := by
  simpa [sourceCoefficient_zero] using sourceCoefficient_add_two 0

theorem source_low_two_global (x : ℝ) :
    |weightedHermite 2 x| ≤ sourceCoefficient 2 * sourceEnvelope 2 (sourceCutoff 2) := by
  let q := 1 - sourceCutoff 2 ^ 2 / 5
  have hq : 0 < q := by
    have hc := sourceCutoff_sq_lt 2 (by omega)
    norm_num at hc
    dsimp [q]
    linarith
  have hqid : q = Real.pi / 5 - Real.pi ^ 2 / 100 := by
    dsimp [q]
    rw [sourceCutoff_sq]
    norm_num
    ring
  have hp : Real.pi < (16 / 5 : ℝ) := by linarith [Real.pi_lt_d4]
  have hcoeff : (25 / 4 : ℝ) * q ≤ sourceCoefficient 2 ^ 2 := by
    rw [sourceCoefficient_two, hqid]
    nlinarith [sq_nonneg Real.pi]
  have hb := (mul_le_mul_of_nonneg_right (degree_two_global_square x) hq.le).trans hcoeff
  have h := abs_le_envelope_of_sq (sourceCoefficient_pos 2).le hq hb
  norm_num only [sourceEnvelope, Nat.cast_ofNat, show (2 : ℝ) * 2 + 1 = 5 by norm_num]
    at h ⊢
  exact h

end HermiteEnvelope
