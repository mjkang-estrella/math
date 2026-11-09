import SupportData153
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport153
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0226.C7232, NewCertificates0226.C7233, NewCertificates0226.C7234, NewCertificates0226.C7235, NewCertificates0226.C7236, NewCertificates0226.C7237, NewCertificates0226.C7238, NewCertificates0226.C7239} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0226.C7240, NewCertificates0226.C7241, NewCertificates0226.C7242, NewCertificates0226.C7243, NewCertificates0226.C7244, NewCertificates0226.C7245, NewCertificates0226.C7246, NewCertificates0226.C7247} := by
  decide +kernel
theorem signed_enumeration6 : signedPatterns (U6.submatrix e e) p = {NewCertificates0226.C7248, NewCertificates0226.C7249, NewCertificates0226.C7250, NewCertificates0226.C7251, NewCertificates0226.C7252, NewCertificates0226.C7253, NewCertificates0226.C7254, NewCertificates0226.C7255} := by
  decide +kernel
theorem signed_enumeration7 : signedPatterns (U7.submatrix e e) p = {NewCertificates0226.C7256, NewCertificates0226.C7257, NewCertificates0226.C7258, NewCertificates0226.C7259} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0226.obstruction7232
  · exact NewCertificates0226.obstruction7233
  · exact NewCertificates0226.obstruction7234
  · exact NewCertificates0226.obstruction7235
  · exact NewCertificates0226.obstruction7236
  · exact NewCertificates0226.obstruction7237
  · exact NewCertificates0226.obstruction7238
  · exact NewCertificates0226.obstruction7239
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0226.obstruction7240
  · exact NewCertificates0226.obstruction7241
  · exact NewCertificates0226.obstruction7242
  · exact NewCertificates0226.obstruction7243
  · exact NewCertificates0226.obstruction7244
  · exact NewCertificates0226.obstruction7245
  · exact NewCertificates0226.obstruction7246
  · exact NewCertificates0226.obstruction7247
theorem checked6 : ∀ A ∈ signedPatterns (U6.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration6]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0226.obstruction7248
  · exact NewCertificates0226.obstruction7249
  · exact NewCertificates0226.obstruction7250
  · exact NewCertificates0226.obstruction7251
  · exact NewCertificates0226.obstruction7252
  · exact NewCertificates0226.obstruction7253
  · exact NewCertificates0226.obstruction7254
  · exact NewCertificates0226.obstruction7255
theorem checked7 : ∀ A ∈ signedPatterns (U7.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration7]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0226.obstruction7256
  · exact NewCertificates0226.obstruction7257
  · exact NewCertificates0226.obstruction7258
  · exact NewCertificates0226.obstruction7259
end Nut8.FiniteSupport153
