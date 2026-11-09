import Core
namespace Riordan
theorem row6 : ∀ j : Fin 15, entry 6 j = (![0,0,0,0,1,1,0,1,1,1,0,1,0,1,0] : Fin 15 → ℕ) j := by
  intro j
  fin_cases j <;> norm_num [entry, pc_0_0, pc_0_1, pc_0_2, pc_0_3, pc_0_4, pc_0_5, pc_0_6, pc_0_7, pc_0_8, pc_0_9, pc_0_10, pc_0_11, pc_0_12, pc_0_13, pc_1_0, pc_1_1, pc_1_2, pc_1_3, pc_1_4, pc_1_5, pc_1_6, pc_1_7, pc_1_8, pc_1_9, pc_1_10, pc_1_11, pc_1_12, pc_1_13, pc_2_0, pc_2_1, pc_2_2, pc_2_3, pc_2_4, pc_2_5, pc_2_6, pc_2_7, pc_2_8, pc_2_9, pc_2_10, pc_2_11, pc_2_12, pc_3_0, pc_3_1, pc_3_2, pc_3_3, pc_3_4, pc_3_5, pc_3_6, pc_3_7, pc_3_8, pc_3_9, pc_3_10, pc_3_11, pc_4_0, pc_4_1, pc_4_2, pc_4_3, pc_4_4, pc_4_5, pc_4_6, pc_4_7, pc_4_8, pc_4_9, pc_4_10, pc_5_0, pc_5_1, pc_5_2, pc_5_3, pc_5_4, pc_5_5, pc_5_6, pc_5_7, pc_5_8, pc_5_9, pc_6_0, pc_6_1, pc_6_2, pc_6_3, pc_6_4, pc_6_5, pc_6_6, pc_6_7, pc_6_8, pc_7_0, pc_7_1, pc_7_2, pc_7_3, pc_7_4, pc_7_5, pc_7_6, pc_7_7, pc_8_0, pc_8_1, pc_8_2, pc_8_3, pc_8_4, pc_8_5, pc_8_6, pc_9_0, pc_9_1, pc_9_2, pc_9_3, pc_9_4, pc_9_5, pc_10_0, pc_10_1, pc_10_2, pc_10_3, pc_10_4, pc_11_0, pc_11_1, pc_11_2, pc_11_3, pc_12_0, pc_12_1, pc_12_2, pc_13_0, pc_13_1, pc_14_0]
end Riordan
