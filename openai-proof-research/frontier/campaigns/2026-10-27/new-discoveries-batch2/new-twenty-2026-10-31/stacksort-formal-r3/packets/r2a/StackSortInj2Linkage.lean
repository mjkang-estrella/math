import StackSortInj2Rows5
import Mathlib.Tactic.IntervalCases
namespace StackSort
open BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem lowerTable_seed_check : ∀ n : Fin 21, tableValue n = seed20[n.val]! := by decide
theorem lowerTable_step {n : ℕ} (h : 20 < n) (hn : n ≤ 130) :
    tableValue n = rootRhs tableValue n := by
  rw [rootRhs_eq_evalRhs tableValue (by omega)]
  interval_cases n
  · exact lower_row_21
  · exact lower_row_22
  · exact lower_row_23
  · exact lower_row_24
  · exact lower_row_25
  · exact lower_row_26
  · exact lower_row_27
  · exact lower_row_28
  · exact lower_row_29
  · exact lower_row_30
  · exact lower_row_31
  · exact lower_row_32
  · exact lower_row_33
  · exact lower_row_34
  · exact lower_row_35
  · exact lower_row_36
  · exact lower_row_37
  · exact lower_row_38
  · exact lower_row_39
  · exact lower_row_40
  · exact lower_row_41
  · exact lower_row_42
  · exact lower_row_43
  · exact lower_row_44
  · exact lower_row_45
  · exact lower_row_46
  · exact lower_row_47
  · exact lower_row_48
  · exact lower_row_49
  · exact lower_row_50
  · exact lower_row_51
  · exact lower_row_52
  · exact lower_row_53
  · exact lower_row_54
  · exact lower_row_55
  · exact lower_row_56
  · exact lower_row_57
  · exact lower_row_58
  · exact lower_row_59
  · exact lower_row_60
  · exact lower_row_61
  · exact lower_row_62
  · exact lower_row_63
  · exact lower_row_64
  · exact lower_row_65
  · exact lower_row_66
  · exact lower_row_67
  · exact lower_row_68
  · exact lower_row_69
  · exact lower_row_70
  · exact lower_row_71
  · exact lower_row_72
  · exact lower_row_73
  · exact lower_row_74
  · exact lower_row_75
  · exact lower_row_76
  · exact lower_row_77
  · exact lower_row_78
  · exact lower_row_79
  · exact lower_row_80
  · exact lower_row_81
  · exact lower_row_82
  · exact lower_row_83
  · exact lower_row_84
  · exact lower_row_85
  · exact lower_row_86
  · exact lower_row_87
  · exact lower_row_88
  · exact lower_row_89
  · exact lower_row_90
  · exact lower_row_91
  · exact lower_row_92
  · exact lower_row_93
  · exact lower_row_94
  · exact lower_row_95
  · exact lower_row_96
  · exact lower_row_97
  · exact lower_row_98
  · exact lower_row_99
  · exact lower_row_100
  · exact lower_row_101
  · exact lower_row_102
  · exact lower_row_103
  · exact lower_row_104
  · exact lower_row_105
  · exact lower_row_106
  · exact lower_row_107
  · exact lower_row_108
  · exact lower_row_109
  · exact lower_row_110
  · exact lower_row_111
  · exact lower_row_112
  · exact lower_row_113
  · exact lower_row_114
  · exact lower_row_115
  · exact lower_row_116
  · exact lower_row_117
  · exact lower_row_118
  · exact lower_row_119
  · exact lower_row_120
  · exact lower_row_121
  · exact lower_row_122
  · exact lower_row_123
  · exact lower_row_124
  · exact lower_row_125
  · exact lower_row_126
  · exact lower_row_127
  · exact lower_row_128
  · exact lower_row_129
  · exact lower_row_130

theorem G_eq_table {n : ℕ} (hn : n ≤ 130) : G n = tableValue n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : n ≤ 20
    · rw [G_seed hs]
      exact (lowerTable_seed_check ⟨n, by omega⟩).symm
    · rw [G_step (by omega), lowerTable_step (by omega) hn]
      unfold rootRhs
      rw [ih (n-1) (by omega) (by omega)]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      rw [ih i (by omega) (by omega), ih (n-1-i) (by omega) (by omega)]

theorem G_130_eq_lower130 : G 130 = lower130 := by
  rw [G_eq_table (by decide)]
  rfl

/-- Linkage is closed; the remaining input is the combinatorial RootSplit bound. -/
theorem lower130_of_seeds (hr : RootSplit) : ExactSeeds20 → Lower130 := by
  intro hs
  unfold Lower130
  rw [← G_130_eq_lower130]
  exact G_le_P hr hs 130
end StackSort
