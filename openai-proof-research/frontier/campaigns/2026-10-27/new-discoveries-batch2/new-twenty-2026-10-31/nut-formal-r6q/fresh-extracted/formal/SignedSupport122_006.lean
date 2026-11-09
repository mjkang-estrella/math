import SupportData122
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport122
theorem signed_enumeration24 : signedPatterns (U24.submatrix e e) p = {NewCertificates0183.C5884, NewCertificates0183.C5885, NewCertificates0183.C5886, NewCertificates0183.C5887} := by
  decide +kernel
theorem signed_enumeration25 : signedPatterns (U25.submatrix e e) p = {NewCertificates0184.C5888, NewCertificates0184.C5889, NewCertificates0184.C5890, NewCertificates0184.C5891} := by
  decide +kernel
theorem signed_enumeration26 : signedPatterns (U26.submatrix e e) p = {NewCertificates0184.C5892, NewCertificates0184.C5893, NewCertificates0184.C5894, NewCertificates0184.C5895} := by
  decide +kernel
theorem signed_enumeration27 : signedPatterns (U27.submatrix e e) p = {NewCertificates0184.C5896, NewCertificates0184.C5897, NewCertificates0184.C5898, NewCertificates0184.C5899} := by
  decide +kernel
theorem checked24 : ∀ A ∈ signedPatterns (U24.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration24]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0183.obstruction5884
  · exact NewCertificates0183.obstruction5885
  · exact NewCertificates0183.obstruction5886
  · exact NewCertificates0183.obstruction5887
theorem checked25 : ∀ A ∈ signedPatterns (U25.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration25]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0184.obstruction5888
  · exact NewCertificates0184.obstruction5889
  · exact NewCertificates0184.obstruction5890
  · exact NewCertificates0184.obstruction5891
theorem checked26 : ∀ A ∈ signedPatterns (U26.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration26]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0184.obstruction5892
  · exact NewCertificates0184.obstruction5893
  · exact NewCertificates0184.obstruction5894
  · exact NewCertificates0184.obstruction5895
theorem checked27 : ∀ A ∈ signedPatterns (U27.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration27]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0184.obstruction5896
  · exact NewCertificates0184.obstruction5897
  · exact NewCertificates0184.obstruction5898
  · exact NewCertificates0184.obstruction5899
end Nut8.FiniteSupport122
