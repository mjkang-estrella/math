import SupportData122
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport122
theorem signed_enumeration16 : signedPatterns (U16.submatrix e e) p = {NewCertificates0182.C5852, NewCertificates0182.C5853, NewCertificates0182.C5854, NewCertificates0182.C5855} := by
  decide +kernel
theorem signed_enumeration17 : signedPatterns (U17.submatrix e e) p = {NewCertificates0183.C5856, NewCertificates0183.C5857, NewCertificates0183.C5858, NewCertificates0183.C5859} := by
  decide +kernel
theorem signed_enumeration18 : signedPatterns (U18.submatrix e e) p = {NewCertificates0183.C5860, NewCertificates0183.C5861, NewCertificates0183.C5862, NewCertificates0183.C5863} := by
  decide +kernel
theorem signed_enumeration19 : signedPatterns (U19.submatrix e e) p = {NewCertificates0183.C5864, NewCertificates0183.C5865, NewCertificates0183.C5866, NewCertificates0183.C5867} := by
  decide +kernel
theorem checked16 : ∀ A ∈ signedPatterns (U16.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration16]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0182.obstruction5852
  · exact NewCertificates0182.obstruction5853
  · exact NewCertificates0182.obstruction5854
  · exact NewCertificates0182.obstruction5855
theorem checked17 : ∀ A ∈ signedPatterns (U17.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration17]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0183.obstruction5856
  · exact NewCertificates0183.obstruction5857
  · exact NewCertificates0183.obstruction5858
  · exact NewCertificates0183.obstruction5859
theorem checked18 : ∀ A ∈ signedPatterns (U18.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration18]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0183.obstruction5860
  · exact NewCertificates0183.obstruction5861
  · exact NewCertificates0183.obstruction5862
  · exact NewCertificates0183.obstruction5863
theorem checked19 : ∀ A ∈ signedPatterns (U19.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration19]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0183.obstruction5864
  · exact NewCertificates0183.obstruction5865
  · exact NewCertificates0183.obstruction5866
  · exact NewCertificates0183.obstruction5867
end Nut8.FiniteSupport122
