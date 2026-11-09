import MeanEExpansion
import MeanWeights
import Mathlib.Tactic.Positivity
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
namespace LogArctangentMean
theorem weighted0 {t : ℝ} (ht : 0 ≤ t) : 0 < c0_0*Real.cosh (freq0*t) + c1_0*Real.cosh (freq1*t) + c2_0*Real.cosh (freq2*t) + c3_0*Real.cosh (freq3*t) + c4_0*Real.cosh (freq4*t) + c5_0*Real.cosh (freq5*t) + c6_0*Real.cosh (freq6*t) + c7_0*Real.cosh (freq7*t) + c8_0*Real.cosh (freq8*t) + c9_0*Real.cosh (freq9*t) + c10_0*Real.cosh (freq10*t) + c11_0*Real.cosh (freq11*t) := by
  obtain ⟨ho0, ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, ho10, hp11⟩ := frequencies_ordered
  have hp10 : 0 < freq10 := lt_trans hp11 ho10
  have hp9 : 0 < freq9 := lt_trans hp10 ho9
  have hp8 : 0 < freq8 := lt_trans hp9 ho8
  have hp7 : 0 < freq7 := lt_trans hp8 ho7
  have hp6 : 0 < freq6 := lt_trans hp7 ho6
  have hp5 : 0 < freq5 := lt_trans hp6 ho5
  have hp4 : 0 < freq4 := lt_trans hp5 ho4
  have hp3 : 0 < freq3 := lt_trans hp4 ho3
  have hp2 : 0 < freq2 := lt_trans hp3 ho2
  have hp1 : 0 < freq1 := lt_trans hp2 ho1
  have hp0 : 0 < freq0 := lt_trans hp1 ho0
  have hs0 : 0 < c0_0 := prefix_pos_0_0
  have hs1 : 0 < c0_0 + c1_0 := prefix_pos_1_0
  have hs2 : 0 < c0_0 + c1_0 + c2_0 := prefix_pos_2_0
  have hs3 : 0 < c0_0 + c1_0 + c2_0 + c3_0 := prefix_pos_3_0
  have hs4 : 0 < c0_0 + c1_0 + c2_0 + c3_0 + c4_0 := prefix_pos_4_0
  have hs5 : 0 < c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 := prefix_pos_5_0
  have hs6 : 0 < c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 := prefix_pos_6_0
  have hs7 : 0 < c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 := prefix_pos_7_0
  have hs8 : 0 < c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 := prefix_pos_8_0
  have hs9 : 0 < c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0 := prefix_pos_9_0
  have hs10 : 0 < c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0 + c10_0 := prefix_pos_10_0
  have hs11 : 0 < c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0 + c10_0 + c11_0 := prefix_pos_11_0
  have hw0 : 0 ≤ Real.cosh (freq0*t)-Real.cosh (freq1*t) := sub_nonneg.mpr (cosh_weight_mono (le_of_lt hp1) (le_of_lt ho0) ht)
  have hw1 : 0 ≤ Real.cosh (freq1*t)-Real.cosh (freq2*t) := sub_nonneg.mpr (cosh_weight_mono (le_of_lt hp2) (le_of_lt ho1) ht)
  have hw2 : 0 ≤ Real.cosh (freq2*t)-Real.cosh (freq3*t) := sub_nonneg.mpr (cosh_weight_mono (le_of_lt hp3) (le_of_lt ho2) ht)
  have hw3 : 0 ≤ Real.cosh (freq3*t)-Real.cosh (freq4*t) := sub_nonneg.mpr (cosh_weight_mono (le_of_lt hp4) (le_of_lt ho3) ht)
  have hw4 : 0 ≤ Real.cosh (freq4*t)-Real.cosh (freq5*t) := sub_nonneg.mpr (cosh_weight_mono (le_of_lt hp5) (le_of_lt ho4) ht)
  have hw5 : 0 ≤ Real.cosh (freq5*t)-Real.cosh (freq6*t) := sub_nonneg.mpr (cosh_weight_mono (le_of_lt hp6) (le_of_lt ho5) ht)
  have hw6 : 0 ≤ Real.cosh (freq6*t)-Real.cosh (freq7*t) := sub_nonneg.mpr (cosh_weight_mono (le_of_lt hp7) (le_of_lt ho6) ht)
  have hw7 : 0 ≤ Real.cosh (freq7*t)-Real.cosh (freq8*t) := sub_nonneg.mpr (cosh_weight_mono (le_of_lt hp8) (le_of_lt ho7) ht)
  have hw8 : 0 ≤ Real.cosh (freq8*t)-Real.cosh (freq9*t) := sub_nonneg.mpr (cosh_weight_mono (le_of_lt hp9) (le_of_lt ho8) ht)
  have hw9 : 0 ≤ Real.cosh (freq9*t)-Real.cosh (freq10*t) := sub_nonneg.mpr (cosh_weight_mono (le_of_lt hp10) (le_of_lt ho9) ht)
  have hw10 : 0 ≤ Real.cosh (freq10*t)-Real.cosh (freq11*t) := sub_nonneg.mpr (cosh_weight_mono (le_of_lt hp11) (le_of_lt ho10) ht)
  have hlast := cosh_weight_pos freq11 t
  rw [show c0_0*Real.cosh (freq0*t) + c1_0*Real.cosh (freq1*t) + c2_0*Real.cosh (freq2*t) + c3_0*Real.cosh (freq3*t) + c4_0*Real.cosh (freq4*t) + c5_0*Real.cosh (freq5*t) + c6_0*Real.cosh (freq6*t) + c7_0*Real.cosh (freq7*t) + c8_0*Real.cosh (freq8*t) + c9_0*Real.cosh (freq9*t) + c10_0*Real.cosh (freq10*t) + c11_0*Real.cosh (freq11*t) = (c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0 + c10_0 + c11_0)*Real.cosh (freq11*t) + (c0_0)*(Real.cosh (freq0*t)-Real.cosh (freq1*t)) + (c0_0 + c1_0)*(Real.cosh (freq1*t)-Real.cosh (freq2*t)) + (c0_0 + c1_0 + c2_0)*(Real.cosh (freq2*t)-Real.cosh (freq3*t)) + (c0_0 + c1_0 + c2_0 + c3_0)*(Real.cosh (freq3*t)-Real.cosh (freq4*t)) + (c0_0 + c1_0 + c2_0 + c3_0 + c4_0)*(Real.cosh (freq4*t)-Real.cosh (freq5*t)) + (c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0)*(Real.cosh (freq5*t)-Real.cosh (freq6*t)) + (c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0)*(Real.cosh (freq6*t)-Real.cosh (freq7*t)) + (c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0)*(Real.cosh (freq7*t)-Real.cosh (freq8*t)) + (c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0)*(Real.cosh (freq8*t)-Real.cosh (freq9*t)) + (c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0)*(Real.cosh (freq9*t)-Real.cosh (freq10*t)) + (c0_0 + c1_0 + c2_0 + c3_0 + c4_0 + c5_0 + c6_0 + c7_0 + c8_0 + c9_0 + c10_0)*(Real.cosh (freq10*t)-Real.cosh (freq11*t)) by ring]
  positivity
theorem weighted1 {t : ℝ} (ht : 0 ≤ t) : 0 ≤ (c0_1+c0_2)*(freq0*Real.sinh (freq0*t)) + (c1_1+c1_2)*(freq1*Real.sinh (freq1*t)) + (c2_1+c2_2)*(freq2*Real.sinh (freq2*t)) + (c3_1+c3_2)*(freq3*Real.sinh (freq3*t)) + (c4_1+c4_2)*(freq4*Real.sinh (freq4*t)) + (c5_1+c5_2)*(freq5*Real.sinh (freq5*t)) + (c6_1+c6_2)*(freq6*Real.sinh (freq6*t)) + (c7_1+c7_2)*(freq7*Real.sinh (freq7*t)) + (c8_1+c8_2)*(freq8*Real.sinh (freq8*t)) + (c9_1+c9_2)*(freq9*Real.sinh (freq9*t)) + (c10_1+c10_2)*(freq10*Real.sinh (freq10*t)) + (c11_1+c11_2)*(freq11*Real.sinh (freq11*t)) := by
  obtain ⟨ho0, ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, ho10, hp11⟩ := frequencies_ordered
  have hp10 : 0 < freq10 := lt_trans hp11 ho10
  have hp9 : 0 < freq9 := lt_trans hp10 ho9
  have hp8 : 0 < freq8 := lt_trans hp9 ho8
  have hp7 : 0 < freq7 := lt_trans hp8 ho7
  have hp6 : 0 < freq6 := lt_trans hp7 ho6
  have hp5 : 0 < freq5 := lt_trans hp6 ho5
  have hp4 : 0 < freq4 := lt_trans hp5 ho4
  have hp3 : 0 < freq3 := lt_trans hp4 ho3
  have hp2 : 0 < freq2 := lt_trans hp3 ho2
  have hp1 : 0 < freq1 := lt_trans hp2 ho1
  have hp0 : 0 < freq0 := lt_trans hp1 ho0
  have hs0 : 0 < (c0_1+c0_2) := by linarith [prefix_pos_0_1, prefix_pos_0_2]
  have hs1 : 0 < (c0_1+c0_2) + (c1_1+c1_2) := by linarith [prefix_pos_1_1, prefix_pos_1_2]
  have hs2 : 0 < (c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) := by linarith [prefix_pos_2_1, prefix_pos_2_2]
  have hs3 : 0 < (c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) := by linarith [prefix_pos_3_1, prefix_pos_3_2]
  have hs4 : 0 < (c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) + (c4_1+c4_2) := by linarith [prefix_pos_4_1, prefix_pos_4_2]
  have hs5 : 0 < (c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) + (c4_1+c4_2) + (c5_1+c5_2) := by linarith [prefix_pos_5_1, prefix_pos_5_2]
  have hs6 : 0 < (c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) + (c4_1+c4_2) + (c5_1+c5_2) + (c6_1+c6_2) := by linarith [prefix_pos_6_1, prefix_pos_6_2]
  have hs7 : 0 < (c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) + (c4_1+c4_2) + (c5_1+c5_2) + (c6_1+c6_2) + (c7_1+c7_2) := by linarith [prefix_pos_7_1, prefix_pos_7_2]
  have hs8 : 0 < (c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) + (c4_1+c4_2) + (c5_1+c5_2) + (c6_1+c6_2) + (c7_1+c7_2) + (c8_1+c8_2) := by linarith [prefix_pos_8_1, prefix_pos_8_2]
  have hs9 : 0 < (c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) + (c4_1+c4_2) + (c5_1+c5_2) + (c6_1+c6_2) + (c7_1+c7_2) + (c8_1+c8_2) + (c9_1+c9_2) := by linarith [prefix_pos_9_1, prefix_pos_9_2]
  have hs10 : 0 < (c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) + (c4_1+c4_2) + (c5_1+c5_2) + (c6_1+c6_2) + (c7_1+c7_2) + (c8_1+c8_2) + (c9_1+c9_2) + (c10_1+c10_2) := by linarith [prefix_pos_10_1, prefix_pos_10_2]
  have hs11 : 0 < (c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) + (c4_1+c4_2) + (c5_1+c5_2) + (c6_1+c6_2) + (c7_1+c7_2) + (c8_1+c8_2) + (c9_1+c9_2) + (c10_1+c10_2) + (c11_1+c11_2) := by linarith [prefix_pos_11_1, prefix_pos_11_2]
  have hw0 : 0 ≤ (freq0*Real.sinh (freq0*t))-(freq1*Real.sinh (freq1*t)) := sub_nonneg.mpr (sinh_weight_mono (le_of_lt hp1) (le_of_lt ho0) ht)
  have hw1 : 0 ≤ (freq1*Real.sinh (freq1*t))-(freq2*Real.sinh (freq2*t)) := sub_nonneg.mpr (sinh_weight_mono (le_of_lt hp2) (le_of_lt ho1) ht)
  have hw2 : 0 ≤ (freq2*Real.sinh (freq2*t))-(freq3*Real.sinh (freq3*t)) := sub_nonneg.mpr (sinh_weight_mono (le_of_lt hp3) (le_of_lt ho2) ht)
  have hw3 : 0 ≤ (freq3*Real.sinh (freq3*t))-(freq4*Real.sinh (freq4*t)) := sub_nonneg.mpr (sinh_weight_mono (le_of_lt hp4) (le_of_lt ho3) ht)
  have hw4 : 0 ≤ (freq4*Real.sinh (freq4*t))-(freq5*Real.sinh (freq5*t)) := sub_nonneg.mpr (sinh_weight_mono (le_of_lt hp5) (le_of_lt ho4) ht)
  have hw5 : 0 ≤ (freq5*Real.sinh (freq5*t))-(freq6*Real.sinh (freq6*t)) := sub_nonneg.mpr (sinh_weight_mono (le_of_lt hp6) (le_of_lt ho5) ht)
  have hw6 : 0 ≤ (freq6*Real.sinh (freq6*t))-(freq7*Real.sinh (freq7*t)) := sub_nonneg.mpr (sinh_weight_mono (le_of_lt hp7) (le_of_lt ho6) ht)
  have hw7 : 0 ≤ (freq7*Real.sinh (freq7*t))-(freq8*Real.sinh (freq8*t)) := sub_nonneg.mpr (sinh_weight_mono (le_of_lt hp8) (le_of_lt ho7) ht)
  have hw8 : 0 ≤ (freq8*Real.sinh (freq8*t))-(freq9*Real.sinh (freq9*t)) := sub_nonneg.mpr (sinh_weight_mono (le_of_lt hp9) (le_of_lt ho8) ht)
  have hw9 : 0 ≤ (freq9*Real.sinh (freq9*t))-(freq10*Real.sinh (freq10*t)) := sub_nonneg.mpr (sinh_weight_mono (le_of_lt hp10) (le_of_lt ho9) ht)
  have hw10 : 0 ≤ (freq10*Real.sinh (freq10*t))-(freq11*Real.sinh (freq11*t)) := sub_nonneg.mpr (sinh_weight_mono (le_of_lt hp11) (le_of_lt ho10) ht)
  have hlast := sinh_weight_nonneg (le_of_lt hp11) ht
  rw [show (c0_1+c0_2)*(freq0*Real.sinh (freq0*t)) + (c1_1+c1_2)*(freq1*Real.sinh (freq1*t)) + (c2_1+c2_2)*(freq2*Real.sinh (freq2*t)) + (c3_1+c3_2)*(freq3*Real.sinh (freq3*t)) + (c4_1+c4_2)*(freq4*Real.sinh (freq4*t)) + (c5_1+c5_2)*(freq5*Real.sinh (freq5*t)) + (c6_1+c6_2)*(freq6*Real.sinh (freq6*t)) + (c7_1+c7_2)*(freq7*Real.sinh (freq7*t)) + (c8_1+c8_2)*(freq8*Real.sinh (freq8*t)) + (c9_1+c9_2)*(freq9*Real.sinh (freq9*t)) + (c10_1+c10_2)*(freq10*Real.sinh (freq10*t)) + (c11_1+c11_2)*(freq11*Real.sinh (freq11*t)) = ((c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) + (c4_1+c4_2) + (c5_1+c5_2) + (c6_1+c6_2) + (c7_1+c7_2) + (c8_1+c8_2) + (c9_1+c9_2) + (c10_1+c10_2) + (c11_1+c11_2))*(freq11*Real.sinh (freq11*t)) + ((c0_1+c0_2))*((freq0*Real.sinh (freq0*t))-(freq1*Real.sinh (freq1*t))) + ((c0_1+c0_2) + (c1_1+c1_2))*((freq1*Real.sinh (freq1*t))-(freq2*Real.sinh (freq2*t))) + ((c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2))*((freq2*Real.sinh (freq2*t))-(freq3*Real.sinh (freq3*t))) + ((c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2))*((freq3*Real.sinh (freq3*t))-(freq4*Real.sinh (freq4*t))) + ((c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) + (c4_1+c4_2))*((freq4*Real.sinh (freq4*t))-(freq5*Real.sinh (freq5*t))) + ((c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) + (c4_1+c4_2) + (c5_1+c5_2))*((freq5*Real.sinh (freq5*t))-(freq6*Real.sinh (freq6*t))) + ((c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) + (c4_1+c4_2) + (c5_1+c5_2) + (c6_1+c6_2))*((freq6*Real.sinh (freq6*t))-(freq7*Real.sinh (freq7*t))) + ((c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) + (c4_1+c4_2) + (c5_1+c5_2) + (c6_1+c6_2) + (c7_1+c7_2))*((freq7*Real.sinh (freq7*t))-(freq8*Real.sinh (freq8*t))) + ((c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) + (c4_1+c4_2) + (c5_1+c5_2) + (c6_1+c6_2) + (c7_1+c7_2) + (c8_1+c8_2))*((freq8*Real.sinh (freq8*t))-(freq9*Real.sinh (freq9*t))) + ((c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) + (c4_1+c4_2) + (c5_1+c5_2) + (c6_1+c6_2) + (c7_1+c7_2) + (c8_1+c8_2) + (c9_1+c9_2))*((freq9*Real.sinh (freq9*t))-(freq10*Real.sinh (freq10*t))) + ((c0_1+c0_2) + (c1_1+c1_2) + (c2_1+c2_2) + (c3_1+c3_2) + (c4_1+c4_2) + (c5_1+c5_2) + (c6_1+c6_2) + (c7_1+c7_2) + (c8_1+c8_2) + (c9_1+c9_2) + (c10_1+c10_2))*((freq10*Real.sinh (freq10*t))-(freq11*Real.sinh (freq11*t))) by ring]
  positivity
theorem weighted2 {t : ℝ} (ht : 0 ≤ t) : 0 ≤ c0_2*(freq0^2*Real.cosh (freq0*t)) + c1_2*(freq1^2*Real.cosh (freq1*t)) + c2_2*(freq2^2*Real.cosh (freq2*t)) + c3_2*(freq3^2*Real.cosh (freq3*t)) + c4_2*(freq4^2*Real.cosh (freq4*t)) + c5_2*(freq5^2*Real.cosh (freq5*t)) + c6_2*(freq6^2*Real.cosh (freq6*t)) + c7_2*(freq7^2*Real.cosh (freq7*t)) + c8_2*(freq8^2*Real.cosh (freq8*t)) + c9_2*(freq9^2*Real.cosh (freq9*t)) + c10_2*(freq10^2*Real.cosh (freq10*t)) + c11_2*(freq11^2*Real.cosh (freq11*t)) := by
  obtain ⟨ho0, ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, ho10, hp11⟩ := frequencies_ordered
  have hp10 : 0 < freq10 := lt_trans hp11 ho10
  have hp9 : 0 < freq9 := lt_trans hp10 ho9
  have hp8 : 0 < freq8 := lt_trans hp9 ho8
  have hp7 : 0 < freq7 := lt_trans hp8 ho7
  have hp6 : 0 < freq6 := lt_trans hp7 ho6
  have hp5 : 0 < freq5 := lt_trans hp6 ho5
  have hp4 : 0 < freq4 := lt_trans hp5 ho4
  have hp3 : 0 < freq3 := lt_trans hp4 ho3
  have hp2 : 0 < freq2 := lt_trans hp3 ho2
  have hp1 : 0 < freq1 := lt_trans hp2 ho1
  have hp0 : 0 < freq0 := lt_trans hp1 ho0
  have hs0 : 0 < c0_2 := prefix_pos_0_2
  have hs1 : 0 < c0_2 + c1_2 := prefix_pos_1_2
  have hs2 : 0 < c0_2 + c1_2 + c2_2 := prefix_pos_2_2
  have hs3 : 0 < c0_2 + c1_2 + c2_2 + c3_2 := prefix_pos_3_2
  have hs4 : 0 < c0_2 + c1_2 + c2_2 + c3_2 + c4_2 := prefix_pos_4_2
  have hs5 : 0 < c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 := prefix_pos_5_2
  have hs6 : 0 < c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 := prefix_pos_6_2
  have hs7 : 0 < c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 := prefix_pos_7_2
  have hs8 : 0 < c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 := prefix_pos_8_2
  have hs9 : 0 < c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2 := prefix_pos_9_2
  have hs10 : 0 < c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2 + c10_2 := prefix_pos_10_2
  have hs11 : 0 < c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2 + c10_2 + c11_2 := prefix_pos_11_2
  have hw0 : 0 ≤ (freq0^2*Real.cosh (freq0*t))-(freq1^2*Real.cosh (freq1*t)) := sub_nonneg.mpr (square_cosh_weight_mono (le_of_lt hp1) (le_of_lt ho0) ht)
  have hw1 : 0 ≤ (freq1^2*Real.cosh (freq1*t))-(freq2^2*Real.cosh (freq2*t)) := sub_nonneg.mpr (square_cosh_weight_mono (le_of_lt hp2) (le_of_lt ho1) ht)
  have hw2 : 0 ≤ (freq2^2*Real.cosh (freq2*t))-(freq3^2*Real.cosh (freq3*t)) := sub_nonneg.mpr (square_cosh_weight_mono (le_of_lt hp3) (le_of_lt ho2) ht)
  have hw3 : 0 ≤ (freq3^2*Real.cosh (freq3*t))-(freq4^2*Real.cosh (freq4*t)) := sub_nonneg.mpr (square_cosh_weight_mono (le_of_lt hp4) (le_of_lt ho3) ht)
  have hw4 : 0 ≤ (freq4^2*Real.cosh (freq4*t))-(freq5^2*Real.cosh (freq5*t)) := sub_nonneg.mpr (square_cosh_weight_mono (le_of_lt hp5) (le_of_lt ho4) ht)
  have hw5 : 0 ≤ (freq5^2*Real.cosh (freq5*t))-(freq6^2*Real.cosh (freq6*t)) := sub_nonneg.mpr (square_cosh_weight_mono (le_of_lt hp6) (le_of_lt ho5) ht)
  have hw6 : 0 ≤ (freq6^2*Real.cosh (freq6*t))-(freq7^2*Real.cosh (freq7*t)) := sub_nonneg.mpr (square_cosh_weight_mono (le_of_lt hp7) (le_of_lt ho6) ht)
  have hw7 : 0 ≤ (freq7^2*Real.cosh (freq7*t))-(freq8^2*Real.cosh (freq8*t)) := sub_nonneg.mpr (square_cosh_weight_mono (le_of_lt hp8) (le_of_lt ho7) ht)
  have hw8 : 0 ≤ (freq8^2*Real.cosh (freq8*t))-(freq9^2*Real.cosh (freq9*t)) := sub_nonneg.mpr (square_cosh_weight_mono (le_of_lt hp9) (le_of_lt ho8) ht)
  have hw9 : 0 ≤ (freq9^2*Real.cosh (freq9*t))-(freq10^2*Real.cosh (freq10*t)) := sub_nonneg.mpr (square_cosh_weight_mono (le_of_lt hp10) (le_of_lt ho9) ht)
  have hw10 : 0 ≤ (freq10^2*Real.cosh (freq10*t))-(freq11^2*Real.cosh (freq11*t)) := sub_nonneg.mpr (square_cosh_weight_mono (le_of_lt hp11) (le_of_lt ho10) ht)
  have hlast := square_cosh_weight_nonneg freq11 t
  rw [show c0_2*(freq0^2*Real.cosh (freq0*t)) + c1_2*(freq1^2*Real.cosh (freq1*t)) + c2_2*(freq2^2*Real.cosh (freq2*t)) + c3_2*(freq3^2*Real.cosh (freq3*t)) + c4_2*(freq4^2*Real.cosh (freq4*t)) + c5_2*(freq5^2*Real.cosh (freq5*t)) + c6_2*(freq6^2*Real.cosh (freq6*t)) + c7_2*(freq7^2*Real.cosh (freq7*t)) + c8_2*(freq8^2*Real.cosh (freq8*t)) + c9_2*(freq9^2*Real.cosh (freq9*t)) + c10_2*(freq10^2*Real.cosh (freq10*t)) + c11_2*(freq11^2*Real.cosh (freq11*t)) = (c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2 + c10_2 + c11_2)*(freq11^2*Real.cosh (freq11*t)) + (c0_2)*((freq0^2*Real.cosh (freq0*t))-(freq1^2*Real.cosh (freq1*t))) + (c0_2 + c1_2)*((freq1^2*Real.cosh (freq1*t))-(freq2^2*Real.cosh (freq2*t))) + (c0_2 + c1_2 + c2_2)*((freq2^2*Real.cosh (freq2*t))-(freq3^2*Real.cosh (freq3*t))) + (c0_2 + c1_2 + c2_2 + c3_2)*((freq3^2*Real.cosh (freq3*t))-(freq4^2*Real.cosh (freq4*t))) + (c0_2 + c1_2 + c2_2 + c3_2 + c4_2)*((freq4^2*Real.cosh (freq4*t))-(freq5^2*Real.cosh (freq5*t))) + (c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2)*((freq5^2*Real.cosh (freq5*t))-(freq6^2*Real.cosh (freq6*t))) + (c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2)*((freq6^2*Real.cosh (freq6*t))-(freq7^2*Real.cosh (freq7*t))) + (c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2)*((freq7^2*Real.cosh (freq7*t))-(freq8^2*Real.cosh (freq8*t))) + (c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2)*((freq8^2*Real.cosh (freq8*t))-(freq9^2*Real.cosh (freq9*t))) + (c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2)*((freq9^2*Real.cosh (freq9*t))-(freq10^2*Real.cosh (freq10*t))) + (c0_2 + c1_2 + c2_2 + c3_2 + c4_2 + c5_2 + c6_2 + c7_2 + c8_2 + c9_2 + c10_2)*((freq10^2*Real.cosh (freq10*t))-(freq11^2*Real.cosh (freq11*t))) by ring]
  positivity
theorem E_derivative24_pos {t : ℝ} (ht : 0 ≤ t) : 0 < iteratedDeriv 24 E t := by
  have h0 := weighted0 ht
  have h1 := weighted1 ht
  have h2 := weighted2 ht
  have he := E_derivative24 t
  have hpos : 0 < (c0_0*Real.cosh (freq0*t) + c1_0*Real.cosh (freq1*t) + c2_0*Real.cosh (freq2*t) + c3_0*Real.cosh (freq3*t) + c4_0*Real.cosh (freq4*t) + c5_0*Real.cosh (freq5*t) + c6_0*Real.cosh (freq6*t) + c7_0*Real.cosh (freq7*t) + c8_0*Real.cosh (freq8*t) + c9_0*Real.cosh (freq9*t) + c10_0*Real.cosh (freq10*t) + c11_0*Real.cosh (freq11*t)) + t*((c0_1+c0_2)*(freq0*Real.sinh (freq0*t)) + (c1_1+c1_2)*(freq1*Real.sinh (freq1*t)) + (c2_1+c2_2)*(freq2*Real.sinh (freq2*t)) + (c3_1+c3_2)*(freq3*Real.sinh (freq3*t)) + (c4_1+c4_2)*(freq4*Real.sinh (freq4*t)) + (c5_1+c5_2)*(freq5*Real.sinh (freq5*t)) + (c6_1+c6_2)*(freq6*Real.sinh (freq6*t)) + (c7_1+c7_2)*(freq7*Real.sinh (freq7*t)) + (c8_1+c8_2)*(freq8*Real.sinh (freq8*t)) + (c9_1+c9_2)*(freq9*Real.sinh (freq9*t)) + (c10_1+c10_2)*(freq10*Real.sinh (freq10*t)) + (c11_1+c11_2)*(freq11*Real.sinh (freq11*t))) + t^2*(c0_2*(freq0^2*Real.cosh (freq0*t)) + c1_2*(freq1^2*Real.cosh (freq1*t)) + c2_2*(freq2^2*Real.cosh (freq2*t)) + c3_2*(freq3^2*Real.cosh (freq3*t)) + c4_2*(freq4^2*Real.cosh (freq4*t)) + c5_2*(freq5^2*Real.cosh (freq5*t)) + c6_2*(freq6^2*Real.cosh (freq6*t)) + c7_2*(freq7^2*Real.cosh (freq7*t)) + c8_2*(freq8^2*Real.cosh (freq8*t)) + c9_2*(freq9^2*Real.cosh (freq9*t)) + c10_2*(freq10^2*Real.cosh (freq10*t)) + c11_2*(freq11^2*Real.cosh (freq11*t))) := add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg h0 (mul_nonneg ht h1)) (mul_nonneg (sq_nonneg t) h2)
  have hid : iteratedDeriv 24 E t / 2 = (c0_0*Real.cosh (freq0*t) + c1_0*Real.cosh (freq1*t) + c2_0*Real.cosh (freq2*t) + c3_0*Real.cosh (freq3*t) + c4_0*Real.cosh (freq4*t) + c5_0*Real.cosh (freq5*t) + c6_0*Real.cosh (freq6*t) + c7_0*Real.cosh (freq7*t) + c8_0*Real.cosh (freq8*t) + c9_0*Real.cosh (freq9*t) + c10_0*Real.cosh (freq10*t) + c11_0*Real.cosh (freq11*t)) + t*((c0_1+c0_2)*(freq0*Real.sinh (freq0*t)) + (c1_1+c1_2)*(freq1*Real.sinh (freq1*t)) + (c2_1+c2_2)*(freq2*Real.sinh (freq2*t)) + (c3_1+c3_2)*(freq3*Real.sinh (freq3*t)) + (c4_1+c4_2)*(freq4*Real.sinh (freq4*t)) + (c5_1+c5_2)*(freq5*Real.sinh (freq5*t)) + (c6_1+c6_2)*(freq6*Real.sinh (freq6*t)) + (c7_1+c7_2)*(freq7*Real.sinh (freq7*t)) + (c8_1+c8_2)*(freq8*Real.sinh (freq8*t)) + (c9_1+c9_2)*(freq9*Real.sinh (freq9*t)) + (c10_1+c10_2)*(freq10*Real.sinh (freq10*t)) + (c11_1+c11_2)*(freq11*Real.sinh (freq11*t))) + t^2*(c0_2*(freq0^2*Real.cosh (freq0*t)) + c1_2*(freq1^2*Real.cosh (freq1*t)) + c2_2*(freq2^2*Real.cosh (freq2*t)) + c3_2*(freq3^2*Real.cosh (freq3*t)) + c4_2*(freq4^2*Real.cosh (freq4*t)) + c5_2*(freq5^2*Real.cosh (freq5*t)) + c6_2*(freq6^2*Real.cosh (freq6*t)) + c7_2*(freq7^2*Real.cosh (freq7*t)) + c8_2*(freq8^2*Real.cosh (freq8*t)) + c9_2*(freq9^2*Real.cosh (freq9*t)) + c10_2*(freq10^2*Real.cosh (freq10*t)) + c11_2*(freq11^2*Real.cosh (freq11*t))) := by rw [he]; ring
  linarith
end LogArctangentMean
