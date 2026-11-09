import UlasFinal5
import UlasLow
open Ulas
example : c 15 1 = 30 := by
  simpa using c_one_eq_two_mul 15
example : c 15 4 = 48030 := by
  rw [c_low 15 4 (by decide)]
  have h := (q_pow_low 15).2.2.2.2
  norm_num at h
  omega
example : c 31 4 = 738110 := by
  rw [c_low 31 4 (by decide)]
  have h := (q_pow_low 31).2.2.2.2
  norm_num at h
  omega
-- Actual low coefficient differences and exact valuations; no endpoint use.
example : diff 1 1 = 8 := by
  have h := diff_one_polynomial 1
  norm_num at h
  omega
example : val 1 1 = 3 := by
  have h := diff_one_polynomial 1
  norm_num at h
  have hd : diff 1 1 = 8 := by omega
  unfold val
  rw [hd]
  exact Round4.val_exact_of_divisibility _ 3 (by norm_num) (by norm_num)
example : diff 2 1 = 56 := by
  have h := diff_one_polynomial 2
  norm_num at h
  omega
example : val 2 1 = 3 := by
  have h := diff_one_polynomial 2
  norm_num at h
  have hd : diff 2 1 = 56 := by omega
  unfold val
  rw [hd]
  exact Round4.val_exact_of_divisibility _ 3 (by norm_num) (by norm_num)
example : diff 3 1 = 192 := by
  have h := diff_one_polynomial 3
  norm_num at h
  omega
example : val 3 1 = 6 := by
  have h := diff_one_polynomial 3
  norm_num at h
  have hd : diff 3 1 = 192 := by omega
  unfold val
  rw [hd]
  exact Round4.val_exact_of_divisibility _ 6 (by norm_num) (by norm_num)
example : diff 4 1 = 480 := by
  have h := diff_one_polynomial 4
  norm_num at h
  omega
example : val 4 1 = 5 := by
  have h := diff_one_polynomial 4
  norm_num at h
  have hd : diff 4 1 = 480 := by omega
  unfold val
  rw [hd]
  exact Round4.val_exact_of_divisibility _ 5 (by norm_num) (by norm_num)
example : diff 5 1 = 1000 := by
  have h := diff_one_polynomial 5
  norm_num at h
  omega
example : val 5 1 = 3 := by
  have h := diff_one_polynomial 5
  norm_num at h
  have hd : diff 5 1 = 1000 := by omega
  unfold val
  rw [hd]
  exact Round4.val_exact_of_divisibility _ 3 (by norm_num) (by norm_num)
example : diff 6 1 = 1848 := by
  have h := diff_one_polynomial 6
  norm_num at h
  omega
example : val 6 1 = 3 := by
  have h := diff_one_polynomial 6
  norm_num at h
  have hd : diff 6 1 = 1848 := by omega
  unfold val
  rw [hd]
  exact Round4.val_exact_of_divisibility _ 3 (by norm_num) (by norm_num)
example : diff 7 1 = 3136 := by
  have h := diff_one_polynomial 7
  norm_num at h
  omega
example : val 7 1 = 6 := by
  have h := diff_one_polynomial 7
  norm_num at h
  have hd : diff 7 1 = 3136 := by omega
  unfold val
  rw [hd]
  exact Round4.val_exact_of_divisibility _ 6 (by norm_num) (by norm_num)
example : diff 11 1 = 15488 := by
  have h := diff_one_polynomial 11
  norm_num at h
  omega
example : val 11 1 = 7 := by
  have h := diff_one_polynomial 11
  norm_num at h
  have hd : diff 11 1 = 15488 := by omega
  unfold val
  rw [hd]
  exact Round4.val_exact_of_divisibility _ 7 (by norm_num) (by norm_num)
example : diff 15 1 = 48000 := by
  have h := diff_one_polynomial 15
  norm_num at h
  omega
example : val 15 1 = 7 := by
  have h := diff_one_polynomial 15
  norm_num at h
  have hd : diff 15 1 = 48000 := by omega
  unfold val
  rw [hd]
  exact Round4.val_exact_of_divisibility _ 7 (by norm_num) (by norm_num)
example : diff 31 1 = 738048 := by
  have h := diff_one_polynomial 31
  norm_num at h
  omega
example : val 31 1 = 8 := by
  have h := diff_one_polynomial 31
  norm_num at h
  have hd : diff 31 1 = 738048 := by omega
  unfold val
  rw [hd]
  exact Round4.val_exact_of_divisibility _ 8 (by norm_num) (by norm_num)
-- Exercise universal endpoint families beyond coefficient 4.
example : val 5 3 = padicValNat 2 3 + 3 :=
  Final5.full_theorem_E2.2.2.2.1 1 3 (by decide) (by decide)
example : val 19 3 = padicValNat 2 3 + 6 :=
  Final5.full_theorem_E2.2.2.2.2.1 4 3 (by decide) (by decide)
example : val 23 5 = padicValNat 2 5 + 6 :=
  Final5.full_theorem_E2.2.2.2.2.1 5 5 (by decide) (by decide)
example : val 27 6 = padicValNat 2 6 + 6 :=
  Final5.full_theorem_E2.2.2.2.2.1 6 6 (by decide) (by decide)
example : val 15 6 ≠ padicValNat 2 6 + 6 :=
  Final5.full_theorem_E2.2.2.2.2.2.2 0 6 (by decide)
example : val 31 3 ≠ padicValNat 2 3 + 6 :=
  Final5.full_theorem_E2.2.2.2.2.2.2 1 3 (by decide)
example : diff 8 6 ≠ 0 ∧ val 8 6 = targetEven 4 6 :=
  Final5.full_theorem_E2.1 4 6 (by decide) (by decide)
#print axioms Ulas.Final5.full_theorem_E2
#print axioms Ulas.Final5.mathdb_342364
#print axioms Ulas.Final5.conj61_some
example : diff 4 2 = 19264 := by
  have h4n := Round5Odd.power_coeff_8 4
  have hn := Round5Odd.power_coeff_2 4
  norm_num at h4n hn
  unfold diff c
  norm_num only [Nat.reduceMul]
  omega
example : val 4 2 = 6 := by
  have h4n := Round5Odd.power_coeff_8 4
  have hn := Round5Odd.power_coeff_2 4
  norm_num at h4n hn
  have hd : diff 4 2 = 19264 := by
    unfold diff c
    norm_num only [Nat.reduceMul]
    omega
  unfold val
  rw [hd]
  exact Round4.val_exact_of_divisibility _ 6 (by norm_num) (by norm_num)
example : diff 11 2 = 8626816 := by
  have h4n := Round5Odd.power_coeff_8 11
  have hn := Round5Odd.power_coeff_2 11
  norm_num at h4n hn
  unfold diff c
  norm_num only [Nat.reduceMul]
  omega
example : val 11 2 = 7 := by
  have h4n := Round5Odd.power_coeff_8 11
  have hn := Round5Odd.power_coeff_2 11
  norm_num at h4n hn
  have hd : diff 11 2 = 8626816 := by
    unfold diff c
    norm_num only [Nat.reduceMul]
    omega
  unfold val
  rw [hd]
  exact Round4.val_exact_of_divisibility _ 7 (by norm_num) (by norm_num)
example : diff 3 3 = 42560 := by
  have h4n := Round5Odd.power_coeff_12 3
  have hn := Round5Odd.power_coeff_3 3
  norm_num at h4n hn
  unfold diff c
  norm_num only [Nat.reduceMul]
  omega
example : val 3 3 = 6 := by
  have h4n := Round5Odd.power_coeff_12 3
  have hn := Round5Odd.power_coeff_3 3
  norm_num at h4n hn
  have hd : diff 3 3 = 42560 := by
    unfold diff c
    norm_num only [Nat.reduceMul]
    omega
  unfold val
  rw [hd]
  exact Round4.val_exact_of_divisibility _ 6 (by norm_num) (by norm_num)
example : diff 31 2 = 11824513024 := by
  have h4n := Round5Odd.power_coeff_8 31
  have hn := Round5Odd.power_coeff_2 31
  norm_num at h4n hn
  unfold diff c
  norm_num only [Nat.reduceMul]
  omega
example : val 31 2 = 14 := by
  have h4n := Round5Odd.power_coeff_8 31
  have hn := Round5Odd.power_coeff_2 31
  norm_num at h4n hn
  have hd : diff 31 2 = 11824513024 := by
    unfold diff c
    norm_num only [Nat.reduceMul]
    omega
  unfold val
  rw [hd]
  exact Round4.val_exact_of_divisibility _ 14 (by norm_num) (by norm_num)
