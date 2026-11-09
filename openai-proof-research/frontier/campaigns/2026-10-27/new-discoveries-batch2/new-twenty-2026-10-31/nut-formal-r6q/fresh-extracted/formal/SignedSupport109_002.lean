import SupportData109
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport109
theorem signed_enumeration8 : signedPatterns (U8.submatrix e e) p = {NewCertificates0162.C5198, NewCertificates0162.C5199, NewCertificates0162.C5200, NewCertificates0162.C5201, NewCertificates0162.C5202, NewCertificates0162.C5203, NewCertificates0162.C5204, NewCertificates0162.C5205} := by
  decide +kernel
theorem signed_enumeration9 : signedPatterns (U9.submatrix e e) p = {NewCertificates0162.C5206, NewCertificates0162.C5207, NewCertificates0162.C5208, NewCertificates0162.C5209} := by
  decide +kernel
theorem signed_enumeration10 : signedPatterns (U10.submatrix e e) p = {NewCertificates0162.C5210, NewCertificates0162.C5211, NewCertificates0162.C5212, NewCertificates0162.C5213} := by
  decide +kernel
theorem signed_enumeration11 : signedPatterns (U11.submatrix e e) p = {NewCertificates0162.C5214, NewCertificates0162.C5215} := by
  decide +kernel
theorem checked8 : ∀ A ∈ signedPatterns (U8.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration8]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0162.obstruction5198
  · exact NewCertificates0162.obstruction5199
  · exact NewCertificates0162.obstruction5200
  · exact NewCertificates0162.obstruction5201
  · exact NewCertificates0162.obstruction5202
  · exact NewCertificates0162.obstruction5203
  · exact NewCertificates0162.obstruction5204
  · exact NewCertificates0162.obstruction5205
theorem checked9 : ∀ A ∈ signedPatterns (U9.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration9]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0162.obstruction5206
  · exact NewCertificates0162.obstruction5207
  · exact NewCertificates0162.obstruction5208
  · exact NewCertificates0162.obstruction5209
theorem checked10 : ∀ A ∈ signedPatterns (U10.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration10]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0162.obstruction5210
  · exact NewCertificates0162.obstruction5211
  · exact NewCertificates0162.obstruction5212
  · exact NewCertificates0162.obstruction5213
theorem checked11 : ∀ A ∈ signedPatterns (U11.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration11]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · exact NewCertificates0162.obstruction5214
  · exact NewCertificates0162.obstruction5215
end Nut8.FiniteSupport109
