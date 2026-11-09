import EdgeRows0
import EdgeRows1
import EdgeRows2
import EdgeRows3
import EdgeRows4
import EdgeRows5
import EdgeRows6
import EdgeRows7
namespace R162
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem labels_injective : Function.Injective labels := by decide
theorem labels_positive : ∀ i : Fin 88, 0 < labels i := by decide

theorem edge_certificate : ∀ i j : Fin 88,
 (treeGraph (nanostar 4)).Adj i j ↔
 i ≠ j ∧ (next i = j ∨ next j = i) := by
 intro i
 fin_cases i
 · exact row_0
 · exact row_1
 · exact row_2
 · exact row_3
 · exact row_4
 · exact row_5
 · exact row_6
 · exact row_7
 · exact row_8
 · exact row_9
 · exact row_10
 · exact row_11
 · exact row_12
 · exact row_13
 · exact row_14
 · exact row_15
 · exact row_16
 · exact row_17
 · exact row_18
 · exact row_19
 · exact row_20
 · exact row_21
 · exact row_22
 · exact row_23
 · exact row_24
 · exact row_25
 · exact row_26
 · exact row_27
 · exact row_28
 · exact row_29
 · exact row_30
 · exact row_31
 · exact row_32
 · exact row_33
 · exact row_34
 · exact row_35
 · exact row_36
 · exact row_37
 · exact row_38
 · exact row_39
 · exact row_40
 · exact row_41
 · exact row_42
 · exact row_43
 · exact row_44
 · exact row_45
 · exact row_46
 · exact row_47
 · exact row_48
 · exact row_49
 · exact row_50
 · exact row_51
 · exact row_52
 · exact row_53
 · exact row_54
 · exact row_55
 · exact row_56
 · exact row_57
 · exact row_58
 · exact row_59
 · exact row_60
 · exact row_61
 · exact row_62
 · exact row_63
 · exact row_64
 · exact row_65
 · exact row_66
 · exact row_67
 · exact row_68
 · exact row_69
 · exact row_70
 · exact row_71
 · exact row_72
 · exact row_73
 · exact row_74
 · exact row_75
 · exact row_76
 · exact row_77
 · exact row_78
 · exact row_79
 · exact row_80
 · exact row_81
 · exact row_82
 · exact row_83
 · exact row_84
 · exact row_85
 · exact row_86
 · exact row_87

theorem realizable_four : Realizable (nanostar 4) := by
 apply realizes_of_label (t := nanostar 4) labels labels_injective labels_positive
 · change ∀ i : Fin 88, ∃ j : Fin 88, Nat.totient (labels i) = labels j
   intro i; exact ⟨next i, phi_labels i⟩
 · change ∀ i j : Fin 88, (treeGraph (nanostar 4)).Adj i j ↔
     i ≠ j ∧ (Nat.totient (labels i) = labels j ∨ Nat.totient (labels j) = labels i)
   intro i j
   rw [edge_certificate, phi_labels, phi_labels]
   simp only [labels_injective.eq_iff]

theorem not_conjecture349177 : ¬ Conjecture349177 := by
 intro h
 exact h 4 (by decide) realizable_four

#print axioms not_conjecture349177
#print Conjecture349177
end R162
