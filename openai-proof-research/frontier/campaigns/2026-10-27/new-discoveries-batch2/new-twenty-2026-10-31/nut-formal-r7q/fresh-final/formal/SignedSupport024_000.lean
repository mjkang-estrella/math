import SupportData024
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport024
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0036.C1156, NewCertificates0036.C1157, NewCertificates0036.C1158, NewCertificates0036.C1159, NewCertificates0036.C1160, NewCertificates0036.C1161, NewCertificates0036.C1162, NewCertificates0036.C1163, NewCertificates0036.C1164, NewCertificates0036.C1165, NewCertificates0036.C1166, NewCertificates0036.C1167, NewCertificates0036.C1168, NewCertificates0036.C1169, NewCertificates0036.C1170, NewCertificates0036.C1171, NewCertificates0036.C1172, NewCertificates0036.C1173, NewCertificates0036.C1174, NewCertificates0036.C1175, NewCertificates0036.C1176, NewCertificates0036.C1177, NewCertificates0036.C1178, NewCertificates0036.C1179, NewCertificates0036.C1180, NewCertificates0036.C1181, NewCertificates0036.C1182, NewCertificates0036.C1183, NewCertificates0037.C1184, NewCertificates0037.C1185, NewCertificates0037.C1186, NewCertificates0037.C1187} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0036.obstruction1156
  · exact NewCertificates0036.obstruction1157
  · exact NewCertificates0036.obstruction1158
  · exact NewCertificates0036.obstruction1159
  · exact NewCertificates0036.obstruction1160
  · exact NewCertificates0036.obstruction1161
  · exact NewCertificates0036.obstruction1162
  · exact NewCertificates0036.obstruction1163
  · exact NewCertificates0036.obstruction1164
  · exact NewCertificates0036.obstruction1165
  · exact NewCertificates0036.obstruction1166
  · exact NewCertificates0036.obstruction1167
  · exact NewCertificates0036.obstruction1168
  · exact NewCertificates0036.obstruction1169
  · exact NewCertificates0036.obstruction1170
  · exact NewCertificates0036.obstruction1171
  · exact NewCertificates0036.obstruction1172
  · exact NewCertificates0036.obstruction1173
  · exact NewCertificates0036.obstruction1174
  · exact NewCertificates0036.obstruction1175
  · exact NewCertificates0036.obstruction1176
  · exact NewCertificates0036.obstruction1177
  · exact NewCertificates0036.obstruction1178
  · exact NewCertificates0036.obstruction1179
  · exact NewCertificates0036.obstruction1180
  · exact NewCertificates0036.obstruction1181
  · exact NewCertificates0036.obstruction1182
  · exact NewCertificates0036.obstruction1183
  · exact NewCertificates0037.obstruction1184
  · exact NewCertificates0037.obstruction1185
  · exact NewCertificates0037.obstruction1186
  · exact NewCertificates0037.obstruction1187
end Nut8.FiniteSupport024
