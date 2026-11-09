import SupportData110
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport110
theorem signed_enumeration0 : signedPatterns (U0.submatrix e e) p = {NewCertificates0163.C5216, NewCertificates0163.C5217, NewCertificates0163.C5218, NewCertificates0163.C5219, NewCertificates0163.C5220, NewCertificates0163.C5221, NewCertificates0163.C5222, NewCertificates0163.C5223} := by
  decide +kernel
theorem signed_enumeration1 : signedPatterns (U1.submatrix e e) p = {NewCertificates0163.C5224, NewCertificates0163.C5225, NewCertificates0163.C5226, NewCertificates0163.C5227, NewCertificates0163.C5228, NewCertificates0163.C5229, NewCertificates0163.C5230, NewCertificates0163.C5231} := by
  decide +kernel
theorem signed_enumeration2 : signedPatterns (U2.submatrix e e) p = {NewCertificates0163.C5232, NewCertificates0163.C5233, NewCertificates0163.C5234, NewCertificates0163.C5235, NewCertificates0163.C5236, NewCertificates0163.C5237, NewCertificates0163.C5238, NewCertificates0163.C5239} := by
  decide +kernel
theorem signed_enumeration3 : signedPatterns (U3.submatrix e e) p = {NewCertificates0163.C5240, NewCertificates0163.C5241, NewCertificates0163.C5242, NewCertificates0163.C5243, NewCertificates0163.C5244, NewCertificates0163.C5245, NewCertificates0163.C5246, NewCertificates0163.C5247} := by
  decide +kernel
theorem checked0 : ∀ A ∈ signedPatterns (U0.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration0]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0163.obstruction5216
  · exact NewCertificates0163.obstruction5217
  · exact NewCertificates0163.obstruction5218
  · exact NewCertificates0163.obstruction5219
  · exact NewCertificates0163.obstruction5220
  · exact NewCertificates0163.obstruction5221
  · exact NewCertificates0163.obstruction5222
  · exact NewCertificates0163.obstruction5223
theorem checked1 : ∀ A ∈ signedPatterns (U1.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration1]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0163.obstruction5224
  · exact NewCertificates0163.obstruction5225
  · exact NewCertificates0163.obstruction5226
  · exact NewCertificates0163.obstruction5227
  · exact NewCertificates0163.obstruction5228
  · exact NewCertificates0163.obstruction5229
  · exact NewCertificates0163.obstruction5230
  · exact NewCertificates0163.obstruction5231
theorem checked2 : ∀ A ∈ signedPatterns (U2.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration2]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0163.obstruction5232
  · exact NewCertificates0163.obstruction5233
  · exact NewCertificates0163.obstruction5234
  · exact NewCertificates0163.obstruction5235
  · exact NewCertificates0163.obstruction5236
  · exact NewCertificates0163.obstruction5237
  · exact NewCertificates0163.obstruction5238
  · exact NewCertificates0163.obstruction5239
theorem checked3 : ∀ A ∈ signedPatterns (U3.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration3]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0163.obstruction5240
  · exact NewCertificates0163.obstruction5241
  · exact NewCertificates0163.obstruction5242
  · exact NewCertificates0163.obstruction5243
  · exact NewCertificates0163.obstruction5244
  · exact NewCertificates0163.obstruction5245
  · exact NewCertificates0163.obstruction5246
  · exact NewCertificates0163.obstruction5247
end Nut8.FiniteSupport110
