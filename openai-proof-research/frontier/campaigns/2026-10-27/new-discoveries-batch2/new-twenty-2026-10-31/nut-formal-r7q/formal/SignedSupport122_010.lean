import SupportData122
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport122
theorem signed_enumeration40 : signedPatterns (U40.submatrix e e) p = {NewCertificates0185.C5946, NewCertificates0185.C5947, NewCertificates0185.C5948, NewCertificates0185.C5949} := by
  decide +kernel
theorem signed_enumeration41 : signedPatterns (U41.submatrix e e) p = {NewCertificates0185.C5950, NewCertificates0185.C5951, NewCertificates0186.C5952, NewCertificates0186.C5953} := by
  decide +kernel
theorem signed_enumeration42 : signedPatterns (U42.submatrix e e) p = {NewCertificates0186.C5954, NewCertificates0186.C5955, NewCertificates0186.C5956, NewCertificates0186.C5957} := by
  decide +kernel
theorem signed_enumeration43 : signedPatterns (U43.submatrix e e) p = {NewCertificates0186.C5958, NewCertificates0186.C5959, NewCertificates0186.C5960, NewCertificates0186.C5961} := by
  decide +kernel
theorem checked40 : ∀ A ∈ signedPatterns (U40.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration40]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0185.obstruction5946
  · exact NewCertificates0185.obstruction5947
  · exact NewCertificates0185.obstruction5948
  · exact NewCertificates0185.obstruction5949
theorem checked41 : ∀ A ∈ signedPatterns (U41.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration41]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0185.obstruction5950
  · exact NewCertificates0185.obstruction5951
  · exact NewCertificates0186.obstruction5952
  · exact NewCertificates0186.obstruction5953
theorem checked42 : ∀ A ∈ signedPatterns (U42.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration42]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0186.obstruction5954
  · exact NewCertificates0186.obstruction5955
  · exact NewCertificates0186.obstruction5956
  · exact NewCertificates0186.obstruction5957
theorem checked43 : ∀ A ∈ signedPatterns (U43.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration43]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0186.obstruction5958
  · exact NewCertificates0186.obstruction5959
  · exact NewCertificates0186.obstruction5960
  · exact NewCertificates0186.obstruction5961
end Nut8.FiniteSupport122
