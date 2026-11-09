import SupportData122
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport122
theorem signed_enumeration20 : signedPatterns (U20.submatrix e e) p = {NewCertificates0183.C5868, NewCertificates0183.C5869, NewCertificates0183.C5870, NewCertificates0183.C5871} := by
  decide +kernel
theorem signed_enumeration21 : signedPatterns (U21.submatrix e e) p = {NewCertificates0183.C5872, NewCertificates0183.C5873, NewCertificates0183.C5874, NewCertificates0183.C5875} := by
  decide +kernel
theorem signed_enumeration22 : signedPatterns (U22.submatrix e e) p = {NewCertificates0183.C5876, NewCertificates0183.C5877, NewCertificates0183.C5878, NewCertificates0183.C5879} := by
  decide +kernel
theorem signed_enumeration23 : signedPatterns (U23.submatrix e e) p = {NewCertificates0183.C5880, NewCertificates0183.C5881, NewCertificates0183.C5882, NewCertificates0183.C5883} := by
  decide +kernel
theorem checked20 : ∀ A ∈ signedPatterns (U20.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration20]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0183.obstruction5868
  · exact NewCertificates0183.obstruction5869
  · exact NewCertificates0183.obstruction5870
  · exact NewCertificates0183.obstruction5871
theorem checked21 : ∀ A ∈ signedPatterns (U21.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration21]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0183.obstruction5872
  · exact NewCertificates0183.obstruction5873
  · exact NewCertificates0183.obstruction5874
  · exact NewCertificates0183.obstruction5875
theorem checked22 : ∀ A ∈ signedPatterns (U22.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration22]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0183.obstruction5876
  · exact NewCertificates0183.obstruction5877
  · exact NewCertificates0183.obstruction5878
  · exact NewCertificates0183.obstruction5879
theorem checked23 : ∀ A ∈ signedPatterns (U23.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration23]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0183.obstruction5880
  · exact NewCertificates0183.obstruction5881
  · exact NewCertificates0183.obstruction5882
  · exact NewCertificates0183.obstruction5883
end Nut8.FiniteSupport122
