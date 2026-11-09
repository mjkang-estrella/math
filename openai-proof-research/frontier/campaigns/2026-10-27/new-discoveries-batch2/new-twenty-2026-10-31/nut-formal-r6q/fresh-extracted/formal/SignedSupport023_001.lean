import SupportData023
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport023
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0034.C1100, NewCertificates0034.C1101, NewCertificates0034.C1102, NewCertificates0034.C1103, NewCertificates0034.C1104, NewCertificates0034.C1105, NewCertificates0034.C1106, NewCertificates0034.C1107, NewCertificates0034.C1108, NewCertificates0034.C1109, NewCertificates0034.C1110, NewCertificates0034.C1111, NewCertificates0034.C1112, NewCertificates0034.C1113, NewCertificates0034.C1114, NewCertificates0034.C1115} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0034.C1116, NewCertificates0034.C1117, NewCertificates0034.C1118, NewCertificates0034.C1119, NewCertificates0035.C1120, NewCertificates0035.C1121, NewCertificates0035.C1122, NewCertificates0035.C1123} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0035.C1124, NewCertificates0035.C1125, NewCertificates0035.C1126, NewCertificates0035.C1127, NewCertificates0035.C1128, NewCertificates0035.C1129, NewCertificates0035.C1130, NewCertificates0035.C1131, NewCertificates0035.C1132, NewCertificates0035.C1133, NewCertificates0035.C1134, NewCertificates0035.C1135, NewCertificates0035.C1136, NewCertificates0035.C1137, NewCertificates0035.C1138, NewCertificates0035.C1139} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0035.C1140, NewCertificates0035.C1141, NewCertificates0035.C1142, NewCertificates0035.C1143, NewCertificates0035.C1144, NewCertificates0035.C1145, NewCertificates0035.C1146, NewCertificates0035.C1147} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0034.obstruction1100
  · exact NewCertificates0034.obstruction1101
  · exact NewCertificates0034.obstruction1102
  · exact NewCertificates0034.obstruction1103
  · exact NewCertificates0034.obstruction1104
  · exact NewCertificates0034.obstruction1105
  · exact NewCertificates0034.obstruction1106
  · exact NewCertificates0034.obstruction1107
  · exact NewCertificates0034.obstruction1108
  · exact NewCertificates0034.obstruction1109
  · exact NewCertificates0034.obstruction1110
  · exact NewCertificates0034.obstruction1111
  · exact NewCertificates0034.obstruction1112
  · exact NewCertificates0034.obstruction1113
  · exact NewCertificates0034.obstruction1114
  · exact NewCertificates0034.obstruction1115
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0034.obstruction1116
  · exact NewCertificates0034.obstruction1117
  · exact NewCertificates0034.obstruction1118
  · exact NewCertificates0034.obstruction1119
  · exact NewCertificates0035.obstruction1120
  · exact NewCertificates0035.obstruction1121
  · exact NewCertificates0035.obstruction1122
  · exact NewCertificates0035.obstruction1123
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0035.obstruction1124
  · exact NewCertificates0035.obstruction1125
  · exact NewCertificates0035.obstruction1126
  · exact NewCertificates0035.obstruction1127
  · exact NewCertificates0035.obstruction1128
  · exact NewCertificates0035.obstruction1129
  · exact NewCertificates0035.obstruction1130
  · exact NewCertificates0035.obstruction1131
  · exact NewCertificates0035.obstruction1132
  · exact NewCertificates0035.obstruction1133
  · exact NewCertificates0035.obstruction1134
  · exact NewCertificates0035.obstruction1135
  · exact NewCertificates0035.obstruction1136
  · exact NewCertificates0035.obstruction1137
  · exact NewCertificates0035.obstruction1138
  · exact NewCertificates0035.obstruction1139
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0035.obstruction1140
  · exact NewCertificates0035.obstruction1141
  · exact NewCertificates0035.obstruction1142
  · exact NewCertificates0035.obstruction1143
  · exact NewCertificates0035.obstruction1144
  · exact NewCertificates0035.obstruction1145
  · exact NewCertificates0035.obstruction1146
  · exact NewCertificates0035.obstruction1147
end Nut8.FiniteSupport023
