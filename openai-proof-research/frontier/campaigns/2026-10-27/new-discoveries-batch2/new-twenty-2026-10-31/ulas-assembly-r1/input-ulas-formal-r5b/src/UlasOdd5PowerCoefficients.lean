import UlasOdd5Coefficients
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open PowerSeries
namespace Ulas.Round5Odd
theorem power_coeff_0 (m : ℕ) : 1*coeff 0 (C^m) = 1 := by simp
theorem power_coeff_1 (m : ℕ) : 1*coeff 1 (C^m) = (2)*(m:ℤ)^1 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ,coeff_mul]
    norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      C_coeff_0, C_coeff_1]
    linear_combination ih
theorem power_coeff_2 (m : ℕ) : 2*coeff 2 (C^m) = (4)*(m:ℤ)^1 + (4)*(m:ℤ)^2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ,coeff_mul]
    norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      C_coeff_0, C_coeff_1, C_coeff_2]
    linear_combination ih + 4*(power_coeff_1 m)
theorem power_coeff_3 (m : ℕ) : 6*coeff 3 (C^m) = (4)*(m:ℤ)^1 + (24)*(m:ℤ)^2 + (8)*(m:ℤ)^3 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ,coeff_mul]
    norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3]
    linear_combination ih + 24*(power_coeff_1 m) + 6*(power_coeff_2 m)
theorem power_coeff_4 (m : ℕ) : 24*coeff 4 (C^m) = (48)*(m:ℤ)^1 + (80)*(m:ℤ)^2 + (96)*(m:ℤ)^3 + (16)*(m:ℤ)^4 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ,coeff_mul]
    norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4]
    linear_combination ih + 144*(power_coeff_1 m) + 48*(power_coeff_2 m) + 8*(power_coeff_3 m)
theorem power_coeff_5 (m : ℕ) : 120*coeff 5 (C^m) = (48)*(m:ℤ)^1 + (640)*(m:ℤ)^2 + (640)*(m:ℤ)^3 + (320)*(m:ℤ)^4 + (32)*(m:ℤ)^5 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ,coeff_mul]
    norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4, C_coeff_5]
    linear_combination ih + 1200*(power_coeff_1 m) + 360*(power_coeff_2 m) + 80*(power_coeff_3 m) + 10*(power_coeff_4 m)
theorem power_coeff_6 (m : ℕ) : 720*coeff 6 (C^m) = (480)*(m:ℤ)^1 + (3616)*(m:ℤ)^2 + (5760)*(m:ℤ)^3 + (3520)*(m:ℤ)^4 + (960)*(m:ℤ)^5 + (64)*(m:ℤ)^6 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ,coeff_mul]
    norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4, C_coeff_5, C_coeff_6]
    linear_combination ih + 10080*(power_coeff_1 m) + 3600*(power_coeff_2 m) + 720*(power_coeff_3 m) + 120*(power_coeff_4 m) + 12*(power_coeff_5 m)
theorem power_coeff_7 (m : ℕ) : 5040*coeff 7 (C^m) = (1440)*(m:ℤ)^1 + (17472)*(m:ℤ)^2 + (53312)*(m:ℤ)^3 + (40320)*(m:ℤ)^4 + (15680)*(m:ℤ)^5 + (2688)*(m:ℤ)^6 + (128)*(m:ℤ)^7 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ,coeff_mul]
    norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4, C_coeff_5, C_coeff_6, C_coeff_7]
    linear_combination ih + 100800*(power_coeff_1 m) + 35280*(power_coeff_2 m) + 8400*(power_coeff_3 m) + 1260*(power_coeff_4 m) + 168*(power_coeff_5 m) + 14*(power_coeff_6 m)
theorem power_coeff_8 (m : ℕ) : 40320*coeff 8 (C^m) = (80640)*(m:ℤ)^1 + (168192)*(m:ℤ)^2 + (404992)*(m:ℤ)^3 + (496384)*(m:ℤ)^4 + (232960)*(m:ℤ)^5 + (60928)*(m:ℤ)^6 + (7168)*(m:ℤ)^7 + (256)*(m:ℤ)^8 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ,coeff_mul]
    norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4, C_coeff_5, C_coeff_6, C_coeff_7, C_coeff_8]
    linear_combination ih + 1048320*(power_coeff_1 m) + 403200*(power_coeff_2 m) + 94080*(power_coeff_3 m) + 16800*(power_coeff_4 m) + 2016*(power_coeff_5 m) + 224*(power_coeff_6 m) + 16*(power_coeff_7 m)
theorem power_coeff_9 (m : ℕ) : 362880*coeff 9 (C^m) = (80640)*(m:ℤ)^1 + (2110464)*(m:ℤ)^2 + (4096000)*(m:ℤ)^3 + (5419008)*(m:ℤ)^4 + (3591168)*(m:ℤ)^5 + (1161216)*(m:ℤ)^6 + (215040)*(m:ℤ)^7 + (18432)*(m:ℤ)^8 + (512)*(m:ℤ)^9 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ,coeff_mul]
    norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4, C_coeff_5, C_coeff_6, C_coeff_7, C_coeff_8, C_coeff_9]
    linear_combination ih + 13063680*(power_coeff_1 m) + 4717440*(power_coeff_2 m) + 1209600*(power_coeff_3 m) + 211680*(power_coeff_4 m) + 30240*(power_coeff_5 m) + 3024*(power_coeff_6 m) + 288*(power_coeff_7 m) + 18*(power_coeff_8 m)
theorem power_coeff_10 (m : ℕ) : 3628800*coeff 10 (C^m) = (1451520)*(m:ℤ)^1 + (21947904)*(m:ℤ)^2 + (50595840)*(m:ℤ)^3 + (64317440)*(m:ℤ)^4 + (51609600)*(m:ℤ)^5 + (21891072)*(m:ℤ)^6 + (5160960)*(m:ℤ)^7 + (706560)*(m:ℤ)^8 + (46080)*(m:ℤ)^9 + (1024)*(m:ℤ)^10 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ,coeff_mul]
    norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4, C_coeff_5, C_coeff_6, C_coeff_7, C_coeff_8, C_coeff_9, C_coeff_10]
    linear_combination ih + 166924800*(power_coeff_1 m) + 65318400*(power_coeff_2 m) + 15724800*(power_coeff_3 m) + 3024000*(power_coeff_4 m) + 423360*(power_coeff_5 m) + 50400*(power_coeff_6 m) + 4320*(power_coeff_7 m) + 360*(power_coeff_8 m) + 20*(power_coeff_9 m)
theorem power_coeff_11 (m : ℕ) : 39916800*coeff 11 (C^m) = (7257600)*(m:ℤ)^1 + (136350720)*(m:ℤ)^2 + (644041728)*(m:ℤ)^3 + (886927360)*(m:ℤ)^4 + (746014720)*(m:ℤ)^5 + (392663040)*(m:ℤ)^6 + (117325824)*(m:ℤ)^7 + (20951040)*(m:ℤ)^8 + (2196480)*(m:ℤ)^9 + (112640)*(m:ℤ)^10 + (2048)*(m:ℤ)^11 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ,coeff_mul]
    norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4, C_coeff_5, C_coeff_6, C_coeff_7, C_coeff_8, C_coeff_9, C_coeff_10, C_coeff_11]
    linear_combination ih + 2395008000*(power_coeff_1 m) + 918086400*(power_coeff_2 m) + 239500800*(power_coeff_3 m) + 43243200*(power_coeff_4 m) + 6652800*(power_coeff_5 m) + 776160*(power_coeff_6 m) + 79200*(power_coeff_7 m) + 5940*(power_coeff_8 m) + 440*(power_coeff_9 m) + 22*(power_coeff_10 m)
theorem power_coeff_12 (m : ℕ) : 479001600*coeff 12 (C^m) = (319334400)*(m:ℤ)^1 + (2705541120)*(m:ℤ)^2 + (7306776576)*(m:ℤ)^3 + (12831655936)*(m:ℤ)^4 + (11785297920)*(m:ℤ)^5 + (6880501760)*(m:ℤ)^6 + (2543321088)*(m:ℤ)^7 + (567840768)*(m:ℤ)^8 + (79073280)*(m:ℤ)^9 + (6533120)*(m:ℤ)^10 + (270336)*(m:ℤ)^11 + (4096)*(m:ℤ)^12 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [pow_succ,coeff_mul]
    norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4, C_coeff_5, C_coeff_6, C_coeff_7, C_coeff_8, C_coeff_9, C_coeff_10, C_coeff_11, C_coeff_12]
    linear_combination ih + 35446118400*(power_coeff_1 m) + 14370048000*(power_coeff_2 m) + 3672345600*(power_coeff_3 m) + 718502400*(power_coeff_4 m) + 103783680*(power_coeff_5 m) + 13305600*(power_coeff_6 m) + 1330560*(power_coeff_7 m) + 118800*(power_coeff_8 m) + 7920*(power_coeff_9 m) + 528*(power_coeff_10 m) + 24*(power_coeff_11 m)
end Ulas.Round5Odd
