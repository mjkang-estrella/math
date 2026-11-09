import UlasFinal
open PowerSeries
namespace Ulas
noncomputable def Q : PowerSeries ℤ :=
  (1 + 2*Polynomial.X + 4*Polynomial.X^2 + 6*Polynomial.X^3 + 10*Polynomial.X^4 : Polynomial ℤ)
theorem C_low : Agree 4 C Q := by
  have h := C_agree 4 5 (by omega)
  intro i hi
  rw [h i hi]
  interval_cases i <;>
    norm_num [G, Q, geomStep, Finset.prod_range_succ, coeff_mul,
      Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      Polynomial.coeff_coe, coeff_mk, coeff_X, Finset.filter_insert,
      Finset.filter_singleton]

noncomputable def q : Polynomial ℤ := 1 + 2*Polynomial.X + 4*Polynomial.X^2 + 6*Polynomial.X^3 + 10*Polynomial.X^4

theorem c_low (m n : ℕ) (hn : n ≤ 4) : c m n = (q^m).coeff n := by
  have h := agree_pow C_low m n hn
  change coeff n (C^m) = _
  rw [h]
  change coeff n ((q : PowerSeries ℤ)^m) = _
  rw [← Polynomial.coe_pow, Polynomial.coeff_coe]

theorem qc_0 : q.coeff 0 = 1 := by
  norm_num [q, Polynomial.coeff_X, Polynomial.coeff_one]
theorem qc_1 : q.coeff 1 = 2 := by
  norm_num [q, Polynomial.coeff_X, Polynomial.coeff_one]
theorem qc_2 : q.coeff 2 = 4 := by
  norm_num [q, Polynomial.coeff_X, Polynomial.coeff_one]
theorem qc_3 : q.coeff 3 = 6 := by
  norm_num [q, Polynomial.coeff_X, Polynomial.coeff_one]
theorem qc_4 : q.coeff 4 = 10 := by
  norm_num [q, Polynomial.coeff_X, Polynomial.coeff_one]
theorem q_1_0 : (q^1).coeff 0 = 1 := by
  simpa only [pow_one] using qc_0
theorem q_1_1 : (q^1).coeff 1 = 2 := by
  simpa only [pow_one] using qc_1
theorem q_1_2 : (q^1).coeff 2 = 4 := by
  simpa only [pow_one] using qc_2
theorem q_1_3 : (q^1).coeff 3 = 6 := by
  simpa only [pow_one] using qc_3
theorem q_1_4 : (q^1).coeff 4 = 10 := by
  simpa only [pow_one] using qc_4
theorem q_2_0 : (q^2).coeff 0 = 1 := by
  rw [show 2 = 1+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_1_0, q_1_1, q_1_2, q_1_3, q_1_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_2_1 : (q^2).coeff 1 = 4 := by
  rw [show 2 = 1+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_1_0, q_1_1, q_1_2, q_1_3, q_1_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_2_2 : (q^2).coeff 2 = 12 := by
  rw [show 2 = 1+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_1_0, q_1_1, q_1_2, q_1_3, q_1_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_2_3 : (q^2).coeff 3 = 28 := by
  rw [show 2 = 1+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_1_0, q_1_1, q_1_2, q_1_3, q_1_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_2_4 : (q^2).coeff 4 = 60 := by
  rw [show 2 = 1+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_1_0, q_1_1, q_1_2, q_1_3, q_1_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_3_0 : (q^3).coeff 0 = 1 := by
  rw [show 3 = 2+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_2_0, q_2_1, q_2_2, q_2_3, q_2_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_3_1 : (q^3).coeff 1 = 6 := by
  rw [show 3 = 2+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_2_0, q_2_1, q_2_2, q_2_3, q_2_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_3_2 : (q^3).coeff 2 = 24 := by
  rw [show 3 = 2+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_2_0, q_2_1, q_2_2, q_2_3, q_2_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_3_3 : (q^3).coeff 3 = 74 := by
  rw [show 3 = 2+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_2_0, q_2_1, q_2_2, q_2_3, q_2_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_3_4 : (q^3).coeff 4 = 198 := by
  rw [show 3 = 2+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_2_0, q_2_1, q_2_2, q_2_3, q_2_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_4_0 : (q^4).coeff 0 = 1 := by
  rw [show 4 = 3+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_3_0, q_3_1, q_3_2, q_3_3, q_3_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_4_1 : (q^4).coeff 1 = 8 := by
  rw [show 4 = 3+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_3_0, q_3_1, q_3_2, q_3_3, q_3_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_4_2 : (q^4).coeff 2 = 40 := by
  rw [show 4 = 3+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_3_0, q_3_1, q_3_2, q_3_3, q_3_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_4_3 : (q^4).coeff 3 = 152 := by
  rw [show 4 = 3+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_3_0, q_3_1, q_3_2, q_3_3, q_3_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_4_4 : (q^4).coeff 4 = 488 := by
  rw [show 4 = 3+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_3_0, q_3_1, q_3_2, q_3_3, q_3_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_5_0 : (q^5).coeff 0 = 1 := by
  rw [show 5 = 4+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_4_0, q_4_1, q_4_2, q_4_3, q_4_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_5_1 : (q^5).coeff 1 = 10 := by
  rw [show 5 = 4+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_4_0, q_4_1, q_4_2, q_4_3, q_4_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_5_2 : (q^5).coeff 2 = 60 := by
  rw [show 5 = 4+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_4_0, q_4_1, q_4_2, q_4_3, q_4_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_5_3 : (q^5).coeff 3 = 270 := by
  rw [show 5 = 4+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_4_0, q_4_1, q_4_2, q_4_3, q_4_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_5_4 : (q^5).coeff 4 = 1010 := by
  rw [show 5 = 4+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_4_0, q_4_1, q_4_2, q_4_3, q_4_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_6_0 : (q^6).coeff 0 = 1 := by
  rw [show 6 = 5+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_5_0, q_5_1, q_5_2, q_5_3, q_5_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_6_1 : (q^6).coeff 1 = 12 := by
  rw [show 6 = 5+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_5_0, q_5_1, q_5_2, q_5_3, q_5_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_6_2 : (q^6).coeff 2 = 84 := by
  rw [show 6 = 5+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_5_0, q_5_1, q_5_2, q_5_3, q_5_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_6_3 : (q^6).coeff 3 = 436 := by
  rw [show 6 = 5+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_5_0, q_5_1, q_5_2, q_5_3, q_5_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_6_4 : (q^6).coeff 4 = 1860 := by
  rw [show 6 = 5+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_5_0, q_5_1, q_5_2, q_5_3, q_5_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_7_0 : (q^7).coeff 0 = 1 := by
  rw [show 7 = 6+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_6_0, q_6_1, q_6_2, q_6_3, q_6_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_7_1 : (q^7).coeff 1 = 14 := by
  rw [show 7 = 6+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_6_0, q_6_1, q_6_2, q_6_3, q_6_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_7_2 : (q^7).coeff 2 = 112 := by
  rw [show 7 = 6+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_6_0, q_6_1, q_6_2, q_6_3, q_6_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_7_3 : (q^7).coeff 3 = 658 := by
  rw [show 7 = 6+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_6_0, q_6_1, q_6_2, q_6_3, q_6_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_7_4 : (q^7).coeff 4 = 3150 := by
  rw [show 7 = 6+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_6_0, q_6_1, q_6_2, q_6_3, q_6_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_8_0 : (q^8).coeff 0 = 1 := by
  rw [show 8 = 7+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_7_0, q_7_1, q_7_2, q_7_3, q_7_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_8_1 : (q^8).coeff 1 = 16 := by
  rw [show 8 = 7+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_7_0, q_7_1, q_7_2, q_7_3, q_7_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_8_2 : (q^8).coeff 2 = 144 := by
  rw [show 8 = 7+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_7_0, q_7_1, q_7_2, q_7_3, q_7_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_8_3 : (q^8).coeff 3 = 944 := by
  rw [show 8 = 7+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_7_0, q_7_1, q_7_2, q_7_3, q_7_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_8_4 : (q^8).coeff 4 = 5008 := by
  rw [show 8 = 7+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_7_0, q_7_1, q_7_2, q_7_3, q_7_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_9_0 : (q^9).coeff 0 = 1 := by
  rw [show 9 = 8+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_8_0, q_8_1, q_8_2, q_8_3, q_8_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_9_1 : (q^9).coeff 1 = 18 := by
  rw [show 9 = 8+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_8_0, q_8_1, q_8_2, q_8_3, q_8_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_9_2 : (q^9).coeff 2 = 180 := by
  rw [show 9 = 8+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_8_0, q_8_1, q_8_2, q_8_3, q_8_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_9_3 : (q^9).coeff 3 = 1302 := by
  rw [show 9 = 8+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_8_0, q_8_1, q_8_2, q_8_3, q_8_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_9_4 : (q^9).coeff 4 = 7578 := by
  rw [show 9 = 8+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_8_0, q_8_1, q_8_2, q_8_3, q_8_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_10_0 : (q^10).coeff 0 = 1 := by
  rw [show 10 = 9+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_9_0, q_9_1, q_9_2, q_9_3, q_9_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_10_1 : (q^10).coeff 1 = 20 := by
  rw [show 10 = 9+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_9_0, q_9_1, q_9_2, q_9_3, q_9_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_10_2 : (q^10).coeff 2 = 220 := by
  rw [show 10 = 9+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_9_0, q_9_1, q_9_2, q_9_3, q_9_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_10_3 : (q^10).coeff 3 = 1740 := by
  rw [show 10 = 9+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_9_0, q_9_1, q_9_2, q_9_3, q_9_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_10_4 : (q^10).coeff 4 = 11020 := by
  rw [show 10 = 9+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_9_0, q_9_1, q_9_2, q_9_3, q_9_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_11_0 : (q^11).coeff 0 = 1 := by
  rw [show 11 = 10+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_10_0, q_10_1, q_10_2, q_10_3, q_10_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_11_1 : (q^11).coeff 1 = 22 := by
  rw [show 11 = 10+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_10_0, q_10_1, q_10_2, q_10_3, q_10_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_11_2 : (q^11).coeff 2 = 264 := by
  rw [show 11 = 10+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_10_0, q_10_1, q_10_2, q_10_3, q_10_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_11_3 : (q^11).coeff 3 = 2266 := by
  rw [show 11 = 10+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_10_0, q_10_1, q_10_2, q_10_3, q_10_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_11_4 : (q^11).coeff 4 = 15510 := by
  rw [show 11 = 10+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_10_0, q_10_1, q_10_2, q_10_3, q_10_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_12_0 : (q^12).coeff 0 = 1 := by
  rw [show 12 = 11+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_11_0, q_11_1, q_11_2, q_11_3, q_11_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_12_1 : (q^12).coeff 1 = 24 := by
  rw [show 12 = 11+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_11_0, q_11_1, q_11_2, q_11_3, q_11_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_12_2 : (q^12).coeff 2 = 312 := by
  rw [show 12 = 11+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_11_0, q_11_1, q_11_2, q_11_3, q_11_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_12_3 : (q^12).coeff 3 = 2888 := by
  rw [show 12 = 11+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_11_0, q_11_1, q_11_2, q_11_3, q_11_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_12_4 : (q^12).coeff 4 = 21240 := by
  rw [show 12 = 11+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_11_0, q_11_1, q_11_2, q_11_3, q_11_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_13_0 : (q^13).coeff 0 = 1 := by
  rw [show 13 = 12+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_12_0, q_12_1, q_12_2, q_12_3, q_12_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_13_1 : (q^13).coeff 1 = 26 := by
  rw [show 13 = 12+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_12_0, q_12_1, q_12_2, q_12_3, q_12_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_13_2 : (q^13).coeff 2 = 364 := by
  rw [show 13 = 12+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_12_0, q_12_1, q_12_2, q_12_3, q_12_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_13_3 : (q^13).coeff 3 = 3614 := by
  rw [show 13 = 12+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_12_0, q_12_1, q_12_2, q_12_3, q_12_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_13_4 : (q^13).coeff 4 = 28418 := by
  rw [show 13 = 12+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_12_0, q_12_1, q_12_2, q_12_3, q_12_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_14_0 : (q^14).coeff 0 = 1 := by
  rw [show 14 = 13+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_13_0, q_13_1, q_13_2, q_13_3, q_13_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_14_1 : (q^14).coeff 1 = 28 := by
  rw [show 14 = 13+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_13_0, q_13_1, q_13_2, q_13_3, q_13_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_14_2 : (q^14).coeff 2 = 420 := by
  rw [show 14 = 13+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_13_0, q_13_1, q_13_2, q_13_3, q_13_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_14_3 : (q^14).coeff 3 = 4452 := by
  rw [show 14 = 13+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_13_0, q_13_1, q_13_2, q_13_3, q_13_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_14_4 : (q^14).coeff 4 = 37268 := by
  rw [show 14 = 13+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_13_0, q_13_1, q_13_2, q_13_3, q_13_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_15_0 : (q^15).coeff 0 = 1 := by
  rw [show 15 = 14+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_14_0, q_14_1, q_14_2, q_14_3, q_14_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_15_1 : (q^15).coeff 1 = 30 := by
  rw [show 15 = 14+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_14_0, q_14_1, q_14_2, q_14_3, q_14_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_15_2 : (q^15).coeff 2 = 480 := by
  rw [show 15 = 14+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_14_0, q_14_1, q_14_2, q_14_3, q_14_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_15_3 : (q^15).coeff 3 = 5410 := by
  rw [show 15 = 14+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_14_0, q_14_1, q_14_2, q_14_3, q_14_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem q_15_4 : (q^15).coeff 4 = 48030 := by
  rw [show 15 = 14+1 from rfl, pow_succ, Polynomial.coeff_mul]
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, q_14_0, q_14_1, q_14_2, q_14_3, q_14_4, qc_0, qc_1, qc_2, qc_3, qc_4]
theorem fifteen_sample : diff 15 1 = 48000 := by
  unfold diff
  rw [c_low 15 4 (by omega), c_low 15 1 (by omega), q_15_4, q_15_1]
  norm_num

theorem wrong_colour_control : c 1 1 ≠ 1 := by
  rw [c_low 1 1 (by omega), q_1_1]
  decide
theorem c_one_eq_two_mul (m : ℕ) : c m 1 = 2 * (m : ℤ) := by
  have h0 : constantCoeff C = 1 := by
    simpa [coeff_zero_eq_constantCoeff, Q] using C_low 0 (by omega)
  have h1 : coeff 1 C = 2 := by
    have hh := C_low 1 (by omega)
    norm_num [Q, coeff_mul, Finset.Nat.antidiagonal_succ,
      Finset.Nat.antidiagonal_zero, coeff_X] at hh
    exact hh
  simp [c, coeff_one_pow, h0, h1, mul_comm]

theorem false_even_control : ¬ ((4 : ℤ) ∣ diff 2 1 ∧ ¬ (8 : ℤ) ∣ diff 2 1) := by
  have hd : diff 2 1 = 56 := by
    unfold diff
    rw [c_low 2 4 (by omega), c_low 2 1 (by omega), q_2_4, q_2_1]
    norm_num
  norm_num [hd]

theorem false_fifteen_control (h : FifteenBound) :
    ¬ ∃ n, 1 ≤ n ∧ val 15 n = padicValNat 2 n + 6 := by
  rintro ⟨n, hn, he⟩
  exact never_fifteen h 0 n hn he
end Ulas
