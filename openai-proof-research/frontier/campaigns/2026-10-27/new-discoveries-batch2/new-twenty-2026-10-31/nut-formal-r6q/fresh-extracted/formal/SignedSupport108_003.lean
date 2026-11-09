import SupportData108
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport108
theorem signed_enumeration12 : signedPatterns (U12.submatrix e e) p = {NewCertificates0159.C5114, NewCertificates0159.C5115, NewCertificates0159.C5116, NewCertificates0159.C5117} := by
  decide +kernel
theorem signed_enumeration13 : signedPatterns (U13.submatrix e e) p = {NewCertificates0159.C5118, NewCertificates0159.C5119, NewCertificates0160.C5120, NewCertificates0160.C5121} := by
  decide +kernel
theorem signed_enumeration14 : signedPatterns (U14.submatrix e e) p = {NewCertificates0160.C5122, NewCertificates0160.C5123, NewCertificates0160.C5124, NewCertificates0160.C5125} := by
  decide +kernel
theorem checked12 : ∀ A ∈ signedPatterns (U12.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration12]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0159.obstruction5114
  · exact NewCertificates0159.obstruction5115
  · exact NewCertificates0159.obstruction5116
  · exact NewCertificates0159.obstruction5117
theorem checked13 : ∀ A ∈ signedPatterns (U13.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration13]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0159.obstruction5118
  · exact NewCertificates0159.obstruction5119
  · exact NewCertificates0160.obstruction5120
  · exact NewCertificates0160.obstruction5121
theorem checked14 : ∀ A ∈ signedPatterns (U14.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration14]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0160.obstruction5122
  · exact NewCertificates0160.obstruction5123
  · exact NewCertificates0160.obstruction5124
  · exact NewCertificates0160.obstruction5125
end Nut8.FiniteSupport108
