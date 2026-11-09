import SupportData110
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport110
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0164.C5248, NewCertificates0164.C5249, NewCertificates0164.C5250, NewCertificates0164.C5251, NewCertificates0164.C5252, NewCertificates0164.C5253, NewCertificates0164.C5254, NewCertificates0164.C5255} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0164.C5256, NewCertificates0164.C5257, NewCertificates0164.C5258, NewCertificates0164.C5259, NewCertificates0164.C5260, NewCertificates0164.C5261, NewCertificates0164.C5262, NewCertificates0164.C5263} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0164.C5264, NewCertificates0164.C5265, NewCertificates0164.C5266, NewCertificates0164.C5267, NewCertificates0164.C5268, NewCertificates0164.C5269, NewCertificates0164.C5270, NewCertificates0164.C5271} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0164.C5272, NewCertificates0164.C5273, NewCertificates0164.C5274, NewCertificates0164.C5275, NewCertificates0164.C5276, NewCertificates0164.C5277, NewCertificates0164.C5278, NewCertificates0164.C5279} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0164.obstruction5248
  · exact NewCertificates0164.obstruction5249
  · exact NewCertificates0164.obstruction5250
  · exact NewCertificates0164.obstruction5251
  · exact NewCertificates0164.obstruction5252
  · exact NewCertificates0164.obstruction5253
  · exact NewCertificates0164.obstruction5254
  · exact NewCertificates0164.obstruction5255
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0164.obstruction5256
  · exact NewCertificates0164.obstruction5257
  · exact NewCertificates0164.obstruction5258
  · exact NewCertificates0164.obstruction5259
  · exact NewCertificates0164.obstruction5260
  · exact NewCertificates0164.obstruction5261
  · exact NewCertificates0164.obstruction5262
  · exact NewCertificates0164.obstruction5263
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0164.obstruction5264
  · exact NewCertificates0164.obstruction5265
  · exact NewCertificates0164.obstruction5266
  · exact NewCertificates0164.obstruction5267
  · exact NewCertificates0164.obstruction5268
  · exact NewCertificates0164.obstruction5269
  · exact NewCertificates0164.obstruction5270
  · exact NewCertificates0164.obstruction5271
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0164.obstruction5272
  · exact NewCertificates0164.obstruction5273
  · exact NewCertificates0164.obstruction5274
  · exact NewCertificates0164.obstruction5275
  · exact NewCertificates0164.obstruction5276
  · exact NewCertificates0164.obstruction5277
  · exact NewCertificates0164.obstruction5278
  · exact NewCertificates0164.obstruction5279
end Nut8.FiniteSupport110
