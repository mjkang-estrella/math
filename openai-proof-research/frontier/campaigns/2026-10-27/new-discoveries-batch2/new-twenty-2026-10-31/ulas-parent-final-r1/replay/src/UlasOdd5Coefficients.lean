import UlasOdd5Residues
set_option linter.unusedSimpArgs false
open PowerSeries
namespace Ulas.Round5Odd
open Round4

theorem C_coeff_step (n : ℕ) :
    coeff (n+1) C - coeff n C =
      coeff (n+1) (expand 2 (by decide) C) + coeff n (expand 2 (by decide) C) := by
  have h := congrArg (coeff (n+1)) C_difference
  simpa [sub_mul,add_mul,coeff_succ_X_mul] using h
theorem C_coeff_0 : coeff 0 C = 1 := by simp
theorem C_coeff_1 : coeff 1 C = 2 := by
  have h := C_coeff_step 0
  norm_num [coeff_expand, C_coeff_0] at h
  omega
theorem C_coeff_2 : coeff 2 C = 4 := by
  have h := C_coeff_step 1
  norm_num [coeff_expand, C_coeff_0, C_coeff_1] at h
  omega
theorem C_coeff_3 : coeff 3 C = 6 := by
  have h := C_coeff_step 2
  norm_num [coeff_expand, C_coeff_0, C_coeff_1, C_coeff_2] at h
  omega
theorem C_coeff_4 : coeff 4 C = 10 := by
  have h := C_coeff_step 3
  norm_num [coeff_expand, C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3] at h
  omega
theorem C_coeff_5 : coeff 5 C = 14 := by
  have h := C_coeff_step 4
  norm_num [coeff_expand, C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4] at h
  omega
theorem C_coeff_6 : coeff 6 C = 20 := by
  have h := C_coeff_step 5
  norm_num [coeff_expand, C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4, C_coeff_5] at h
  omega
theorem C_coeff_7 : coeff 7 C = 26 := by
  have h := C_coeff_step 6
  norm_num [coeff_expand, C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4, C_coeff_5, C_coeff_6] at h
  omega
theorem C_coeff_8 : coeff 8 C = 36 := by
  have h := C_coeff_step 7
  norm_num [coeff_expand, C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4, C_coeff_5, C_coeff_6, C_coeff_7] at h
  omega
theorem C_coeff_9 : coeff 9 C = 46 := by
  have h := C_coeff_step 8
  norm_num [coeff_expand, C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4, C_coeff_5, C_coeff_6, C_coeff_7, C_coeff_8] at h
  omega
theorem C_coeff_10 : coeff 10 C = 60 := by
  have h := C_coeff_step 9
  norm_num [coeff_expand, C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4, C_coeff_5, C_coeff_6, C_coeff_7, C_coeff_8, C_coeff_9] at h
  omega
theorem C_coeff_11 : coeff 11 C = 74 := by
  have h := C_coeff_step 10
  norm_num [coeff_expand, C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4, C_coeff_5, C_coeff_6, C_coeff_7, C_coeff_8, C_coeff_9, C_coeff_10] at h
  omega
theorem C_coeff_12 : coeff 12 C = 94 := by
  have h := C_coeff_step 11
  norm_num [coeff_expand, C_coeff_0, C_coeff_1, C_coeff_2, C_coeff_3, C_coeff_4, C_coeff_5, C_coeff_6, C_coeff_7, C_coeff_8, C_coeff_9, C_coeff_10, C_coeff_11] at h
  omega
end Ulas.Round5Odd
