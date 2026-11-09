import SupportData025
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport025
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0037.C1188, NewCertificates0037.C1189, NewCertificates0037.C1190, NewCertificates0037.C1191, NewCertificates0037.C1192, NewCertificates0037.C1193, NewCertificates0037.C1194, NewCertificates0037.C1195, NewCertificates0037.C1196, NewCertificates0037.C1197, NewCertificates0037.C1198, NewCertificates0037.C1199, NewCertificates0037.C1200, NewCertificates0037.C1201, NewCertificates0037.C1202, NewCertificates0037.C1203, NewCertificates0037.C1204, NewCertificates0037.C1205, NewCertificates0037.C1206, NewCertificates0037.C1207, NewCertificates0037.C1208, NewCertificates0037.C1209, NewCertificates0037.C1210, NewCertificates0037.C1211, NewCertificates0037.C1212, NewCertificates0037.C1213, NewCertificates0037.C1214, NewCertificates0037.C1215, NewCertificates0038.C1216, NewCertificates0038.C1217, NewCertificates0038.C1218, NewCertificates0038.C1219} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0037.obstruction1188
  · exact NewCertificates0037.obstruction1189
  · exact NewCertificates0037.obstruction1190
  · exact NewCertificates0037.obstruction1191
  · exact NewCertificates0037.obstruction1192
  · exact NewCertificates0037.obstruction1193
  · exact NewCertificates0037.obstruction1194
  · exact NewCertificates0037.obstruction1195
  · exact NewCertificates0037.obstruction1196
  · exact NewCertificates0037.obstruction1197
  · exact NewCertificates0037.obstruction1198
  · exact NewCertificates0037.obstruction1199
  · exact NewCertificates0037.obstruction1200
  · exact NewCertificates0037.obstruction1201
  · exact NewCertificates0037.obstruction1202
  · exact NewCertificates0037.obstruction1203
  · exact NewCertificates0037.obstruction1204
  · exact NewCertificates0037.obstruction1205
  · exact NewCertificates0037.obstruction1206
  · exact NewCertificates0037.obstruction1207
  · exact NewCertificates0037.obstruction1208
  · exact NewCertificates0037.obstruction1209
  · exact NewCertificates0037.obstruction1210
  · exact NewCertificates0037.obstruction1211
  · exact NewCertificates0037.obstruction1212
  · exact NewCertificates0037.obstruction1213
  · exact NewCertificates0037.obstruction1214
  · exact NewCertificates0037.obstruction1215
  · exact NewCertificates0038.obstruction1216
  · exact NewCertificates0038.obstruction1217
  · exact NewCertificates0038.obstruction1218
  · exact NewCertificates0038.obstruction1219
end Nut8.FiniteSupport025
