import SupportData147
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport147
theorem signed_enumeration4 : signedPatterns (U4.submatrix e e) p = {NewCertificates0213.C6840, NewCertificates0213.C6841, NewCertificates0213.C6842, NewCertificates0213.C6843, NewCertificates0213.C6844, NewCertificates0213.C6845, NewCertificates0213.C6846, NewCertificates0213.C6847} := by
  decide +kernel
theorem signed_enumeration5 : signedPatterns (U5.submatrix e e) p = {NewCertificates0214.C6848, NewCertificates0214.C6849, NewCertificates0214.C6850, NewCertificates0214.C6851} := by
  decide +kernel
theorem checked4 : ∀ A ∈ signedPatterns (U4.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration4]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact NewCertificates0213.obstruction6840
  · exact NewCertificates0213.obstruction6841
  · exact NewCertificates0213.obstruction6842
  · exact NewCertificates0213.obstruction6843
  · exact NewCertificates0213.obstruction6844
  · exact NewCertificates0213.obstruction6845
  · exact NewCertificates0213.obstruction6846
  · exact NewCertificates0213.obstruction6847
theorem checked5 : ∀ A ∈ signedPatterns (U5.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration5]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0214.obstruction6848
  · exact NewCertificates0214.obstruction6849
  · exact NewCertificates0214.obstruction6850
  · exact NewCertificates0214.obstruction6851
end Nut8.FiniteSupport147
