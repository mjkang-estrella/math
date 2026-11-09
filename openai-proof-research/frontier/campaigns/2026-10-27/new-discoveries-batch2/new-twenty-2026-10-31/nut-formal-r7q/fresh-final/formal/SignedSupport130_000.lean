import SupportData130
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport130
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0193.C6196, NewCertificates0193.C6197, NewCertificates0193.C6198, NewCertificates0193.C6199, NewCertificates0193.C6200, NewCertificates0193.C6201, NewCertificates0193.C6202, NewCertificates0193.C6203, NewCertificates0193.C6204, NewCertificates0193.C6205, NewCertificates0193.C6206, NewCertificates0193.C6207, NewCertificates0194.C6208, NewCertificates0194.C6209, NewCertificates0194.C6210, NewCertificates0194.C6211} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0194.C6212, NewCertificates0194.C6213, NewCertificates0194.C6214, NewCertificates0194.C6215, NewCertificates0194.C6216, NewCertificates0194.C6217, NewCertificates0194.C6218, NewCertificates0194.C6219, NewCertificates0194.C6220, NewCertificates0194.C6221, NewCertificates0194.C6222, NewCertificates0194.C6223, NewCertificates0194.C6224, NewCertificates0194.C6225, NewCertificates0194.C6226, NewCertificates0194.C6227} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0193.obstruction6196
  · exact NewCertificates0193.obstruction6197
  · exact NewCertificates0193.obstruction6198
  · exact NewCertificates0193.obstruction6199
  · exact NewCertificates0193.obstruction6200
  · exact NewCertificates0193.obstruction6201
  · exact NewCertificates0193.obstruction6202
  · exact NewCertificates0193.obstruction6203
  · exact NewCertificates0193.obstruction6204
  · exact NewCertificates0193.obstruction6205
  · exact NewCertificates0193.obstruction6206
  · exact NewCertificates0193.obstruction6207
  · exact NewCertificates0194.obstruction6208
  · exact NewCertificates0194.obstruction6209
  · exact NewCertificates0194.obstruction6210
  · exact NewCertificates0194.obstruction6211
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0194.obstruction6212
  · exact NewCertificates0194.obstruction6213
  · exact NewCertificates0194.obstruction6214
  · exact NewCertificates0194.obstruction6215
  · exact NewCertificates0194.obstruction6216
  · exact NewCertificates0194.obstruction6217
  · exact NewCertificates0194.obstruction6218
  · exact NewCertificates0194.obstruction6219
  · exact NewCertificates0194.obstruction6220
  · exact NewCertificates0194.obstruction6221
  · exact NewCertificates0194.obstruction6222
  · exact NewCertificates0194.obstruction6223
  · exact NewCertificates0194.obstruction6224
  · exact NewCertificates0194.obstruction6225
  · exact NewCertificates0194.obstruction6226
  · exact NewCertificates0194.obstruction6227
end Nut8.FiniteSupport130
