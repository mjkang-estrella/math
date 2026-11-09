import SupportData122
set_option maxRecDepth 4096
namespace Nut8.FiniteSupport122
theorem signed_enumeration8 : signedPatterns (U8.submatrix e e) p = {NewCertificates0181.C5820, NewCertificates0181.C5821, NewCertificates0181.C5822, NewCertificates0181.C5823} := by
  decide +kernel
theorem signed_enumeration9 : signedPatterns (U9.submatrix e e) p = {NewCertificates0182.C5824, NewCertificates0182.C5825, NewCertificates0182.C5826, NewCertificates0182.C5827} := by
  decide +kernel
theorem signed_enumeration10 : signedPatterns (U10.submatrix e e) p = {NewCertificates0182.C5828, NewCertificates0182.C5829, NewCertificates0182.C5830, NewCertificates0182.C5831} := by
  decide +kernel
theorem signed_enumeration11 : signedPatterns (U11.submatrix e e) p = {NewCertificates0182.C5832, NewCertificates0182.C5833, NewCertificates0182.C5834, NewCertificates0182.C5835} := by
  decide +kernel
theorem checked8 : ∀ A ∈ signedPatterns (U8.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration8]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0181.obstruction5820
  · exact NewCertificates0181.obstruction5821
  · exact NewCertificates0181.obstruction5822
  · exact NewCertificates0181.obstruction5823
theorem checked9 : ∀ A ∈ signedPatterns (U9.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration9]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0182.obstruction5824
  · exact NewCertificates0182.obstruction5825
  · exact NewCertificates0182.obstruction5826
  · exact NewCertificates0182.obstruction5827
theorem checked10 : ∀ A ∈ signedPatterns (U10.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration10]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0182.obstruction5828
  · exact NewCertificates0182.obstruction5829
  · exact NewCertificates0182.obstruction5830
  · exact NewCertificates0182.obstruction5831
theorem checked11 : ∀ A ∈ signedPatterns (U11.submatrix e e) p, ¬ (A.det = 0 ∧ ∀ j, A.adjugate j j ≠ 0) := by
  rw [signed_enumeration11]
  intro A hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact NewCertificates0182.obstruction5832
  · exact NewCertificates0182.obstruction5833
  · exact NewCertificates0182.obstruction5834
  · exact NewCertificates0182.obstruction5835
end Nut8.FiniteSupport122
