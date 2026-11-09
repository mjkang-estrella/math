import SupportData122
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport122
theorem signed_enumeration12 : signedPatterns (U12.submatrix e e) p = {NewCertificates0182.C5836, NewCertificates0182.C5837, NewCertificates0182.C5838, NewCertificates0182.C5839} := by
  decide +kernel
theorem signed_enumeration13 : signedPatterns (U13.submatrix e e) p = {NewCertificates0182.C5840, NewCertificates0182.C5841, NewCertificates0182.C5842, NewCertificates0182.C5843} := by
  decide +kernel
theorem signed_enumeration14 : signedPatterns (U14.submatrix e e) p = {NewCertificates0182.C5844, NewCertificates0182.C5845, NewCertificates0182.C5846, NewCertificates0182.C5847} := by
  decide +kernel
theorem signed_enumeration15 : signedPatterns (U15.submatrix e e) p = {NewCertificates0182.C5848, NewCertificates0182.C5849, NewCertificates0182.C5850, NewCertificates0182.C5851} := by
  decide +kernel
theorem checked12 : ∀ A ∈ signedPatterns (U12.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration12]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0182.obstruction5836
  · exact NewCertificates0182.obstruction5837
  · exact NewCertificates0182.obstruction5838
  · exact NewCertificates0182.obstruction5839
theorem checked13 : ∀ A ∈ signedPatterns (U13.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration13]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0182.obstruction5840
  · exact NewCertificates0182.obstruction5841
  · exact NewCertificates0182.obstruction5842
  · exact NewCertificates0182.obstruction5843
theorem checked14 : ∀ A ∈ signedPatterns (U14.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration14]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0182.obstruction5844
  · exact NewCertificates0182.obstruction5845
  · exact NewCertificates0182.obstruction5846
  · exact NewCertificates0182.obstruction5847
theorem checked15 : ∀ A ∈ signedPatterns (U15.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration15]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0182.obstruction5848
  · exact NewCertificates0182.obstruction5849
  · exact NewCertificates0182.obstruction5850
  · exact NewCertificates0182.obstruction5851
end Nut8.FiniteSupport122
